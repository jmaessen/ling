{-# LANGUAGE TypeFamilies #-}
module Data.BakerVec(
  Vec,
  replicate,
  (!), push, pop, pushAndIndex,
  writeVec,
  persist, copy,
  withList
) where

import Prelude hiding (replicate)

import Control.Concurrent.MVar
import Control.Monad.Primitive
import Data.List.NonEmpty(NonEmpty(..))
import Data.Primitive.Array
  (MutableArray, newArray, arrayFromListN, copyMutableArray, cloneMutableArray,
   readArray, unsafeThawArray, writeArray)
import Data.Semigroup
import GHC.Stack
import GHC.Exts(IsList(..))
import System.IO.Unsafe(unsafeDupablePerformIO)

infixl 9 !

{-
Baker-style persistent arrays, implemented safely using unsafe
code.  Got the basic idea from Conchon and Filliatre,
"Semi-Persistent Data Structures",
http://www.lri.fr/~filliatr/ftp/publis/spds-rr.pd
Baker's original "Shallow Binding in Lisp 1.5" was in CACM 21:7 1978
Now there's Allain et al's "Snapshottable Stores" from ICFP 2024,
https://doi.org/10.1145/3674637

As realized here, a version is an MVar (for atomicity of update) that
points to a point in a reversible undo / redo log.  There's one copy
of the state, and as it moves into the future we leave behind undo log
entries.  Referring to an old version flips the intervening undo log
entries into redo log entries while winding the state back to the
original point.  We can then branch the state from there.  Basically
every snapshot is a node in a tree that's rooted at the most recently
used version, and if we switch versions then we reverse edges in the
tree until the newly-referenced version is the root.  The core of
this is `focusOwned`.

We add a couple of refinements:
* We provide a vector interface with push/pop and monoidal append
  (which left-updates).  Right now only pop adds undo log entries,
  since we know the other entries can safely be ignored, but it would
  be safer for space to annull those if we expect a lot of rollbacks.
* We track undo log size and copy when it equals the current backing
  store size.  This probably ought to be related to the size of the
  underlying vec instead.

We don't yet do a couple of things in other work:

* Mostly they keep the store alongside the undo/redo log rather than
  in a single algebraic type.  The present form prevents us from
  referencing the store directly until we've done the proper log
  manipulation.
* C&F have a rollback-only version of the structure that discards
  intermediate snapshots during rollback.  We can do this by adding a
  state, and probably should.

* A&al do away with singleton writes in favor of a "snapshot" operation;
  you can only rollback to the nearest snapshot, so we avoid lots of
  intermediate states.  You can ditch intermediate MVars.  There's
  probably a nice structured way of doing this, though I'm not sure what
  it would be.  Maybe an "open for write" operation.
* A&al use snapshot granularity to store a generation number, creating
  an undo log entry only when the entry's last write generation number
  differs.  They argue the checking cost small vs OCaml's GC r/w barriers.

The MVar discipline of take & put is useful for keeping the code systematic.

-}

-- Invariant: every version other than the unique live root is reachable
-- by following undo (Write) entries.  Growing the array (push/append)
-- must therefore record an undo entry as well: otherwise two versions
-- branched from a common parent at the same index alias the same slot
-- and clobber each other (the older child reads the younger child's
-- value).  See growFocus.  Pop likewise records an undo entry.

type Len = Int
type Idx = Int
type MutCount = Int
type VecVar a = MVar (VecContents a)
data Vec a = Vec !Len (VecVar a)
data Storage a = Storage !Len !MutCount !(MutableArray (PrimState IO) a)
data VecContents a
  = Here {-# UNPACK #-}!(Storage a)
  | Write (VecVar a) !Idx a
  -- | Trunc (VecVar a) !Len !Len  -- longer len, shorter len.
  -- | App (VecVar a) {-# UNPACK #-}!(Storage a)
  | Invalid

instance (Show a) => Show (Vec a) where
  showsPrec _ v@(Vec l _) = showParen True (shows l . (": "++) . showList (toList v))

instance (Eq a) => Eq (Vec a) where
  v1@(Vec l1 m1) == v2@(Vec l2 m2)
    | l1 /= l2 = False
    | l1 == 0 = True -- Don't evaluate undefined.
    | m1 == m2 = True
    | otherwise = toList v1 == toList v2

{-
newtype VecInternals a = VecInternals (Vec a) deriving (Eq)

instance Show a => Show (VecInternals a) where
  showsPrec _ (VecInternals (Vec l m)) =
    showParen True
      (shows l . ('/':) . shows w . (';':) . shows k . (": "++) .
       (writes++) . (' ':) . showList contents)
    where
      (writes, w, k, contents) = unsafeDupablePerformIO $ internals m
      internals m = do
        c <- takeMVar m
        r <- internals' c
        putMVar m c
        return r
      internals' (Here s@(Storage w k _)) = do
        contents <- mapM (readStorage s) [0..l-1]
        pure ("", w, k, contents)
      internals' (Write m i a) = do
        (ws, w, k, contents) <- internals m
        if i < l then
          pure (shows (i,a) (';':ws), w, k, contents)
        else
          pure (shows i (';':ws), w, k, contents)
      internals' Invalid = error "Invalid"
-}

-- Variable conventions:
--  i :: Idx
--  l :: Len
--  k :: MutCount
--  a :: a
--  m :: VecVar a
--  c :: VecContents a
--  s :: Storage a
--  v :: Vec a
--  w :: Len -- Water mark (size of underlying storage)

-- Unchecked read access
readStorage :: HasCallStack => Storage a -> Idx -> IO a
readStorage (Storage w _ arr) i
  | i < w = readArray arr i
  | otherwise = badIndex i w "readStorage"

-- Unchecked write access
writeStorage :: HasCallStack => Storage a -> Idx -> a -> IO ()
writeStorage (Storage w _ arr) i a | i < w = writeArray arr i a
  | otherwise = badIndex i w "writeStorage"

-- Make storage larger (unchecked)
expandStorage :: Len -> Storage a -> IO (Storage a)
expandStorage l (Storage w _ arr0) = do
  arr <- newArray l undefined
  copyMutableArray arr 0 arr0 0 w
  pure (Storage l 0 arr)

-- Clone the first l elements of storage (unchecked)
cloneStorage :: Len -> Storage a -> IO (Storage a)
cloneStorage l (Storage w _ arr)
  | l <= w = Storage l 0 <$> cloneMutableArray arr 0 l
  | otherwise = badIndex l w "cloneStorage"

-- Clone all elements of storage (unchecked)
cloneAll :: Storage a -> IO (Storage a)
cloneAll (Storage w _ arr) = do
  Storage w 0 <$> cloneMutableArray arr 0 w

incMut :: MutCount -> Storage a -> Storage a
incMut k' (Storage w k arr) = Storage w (k+k') arr

{-
overMut :: MutCount -> Storage a -> Bool
overMut k' (Storage w k _) = k + k' >= w
-}

resetMut :: Storage a -> Storage a
resetMut (Storage w _ arr) = Storage w 0 arr

-- First, the IO versions of the operations.
empty :: Vec a
empty = Vec 0 undefined

replicateIO :: Len -> a -> IO (Vec a)
replicateIO 0 _ = pure empty
replicateIO l _ | l < 0 = fail ("replicate: negative length "++show l)
replicateIO l a = do
  s <- newArray l a
  Vec l <$> newMVar (Here $ Storage l 0 s)

badIndex :: HasCallStack => Idx -> Len -> String -> IO a
badIndex i l op = error (op++": index "++shows i (" outside length "++show l))

readVecIO :: HasCallStack => Vec a -> Idx -> IO a
readVecIO v@(Vec l _) i
  | i < 0 || i >= l = badIndex i l "read"
  | otherwise = withReadFocus v (\s -> readStorage s i)

{-
swapVecIO :: Vec a -> Idx -> a -> IO (a, Vec a)
swapVecIO v@(Vec l _) i a
  | i < 0 || i >= l = badIndex i l "swap"
  | otherwise = focusSwap v i a
-}

writeVecIO :: Vec a -> Idx -> a -> IO (Vec a)
writeVecIO v@(Vec l _) i a
  | i < 0 || i >= l = badIndex i l "write"
  | otherwise = snd <$> focusSwap v i a

invalidErr :: String -> IO a
invalidErr op = fail (op ++ " of invalid reference.")

{-# INLINE withReadFocus #-}
-- Focus for a read
withReadFocus :: Vec a -> (Storage a -> IO b) -> IO b
withReadFocus (Vec l m) body = do
  c <- takeMVar m
  s <- focusContents 0 l m c
  r <- body s
  const r <$> putMVar m (Here s)

-- Grow v to length l (l > length v), filling indices [length v .. l-1] via
-- `body`.  Branch-safe: the result is a fresh version with its own MVar, and
-- the parent winds back to it through a Write undo chain (one entry per new
-- index), so two versions grown from a common parent never clobber each other.
-- The point of taking a target length is that we focus and expand ONCE no
-- matter how many elements are added, so an append is linear in the appended
-- length rather than paying a focus + capacity check per element.  The parent
-- has length l0 and never reads indices >= l0, so the (garbage) `old` values
-- recorded for the displaced slots only have to survive a wind-back, never a
-- real read.
growFocus :: HasCallStack => Vec a -> Len -> (Storage a -> IO ()) -> IO (Vec a)
growFocus (Vec l0 _) l _ | l <= l0 = badIndex l0 l "growFocus"
growFocus (Vec 0 _) l body = do          -- empty parent: no array to share
  let w = l + l
  arr <- newArray w undefined
  let s = Storage w 0 arr
  body s
  Vec l <$> newMVar (Here s)
growFocus (Vec l0 m') l body = do
  c  <- takeMVar m'
  s0@(Storage w _ _) <- focusContents 1 l m' c
  s  <- if w < l then expandStorage (l `max` (w+w)) s0 else pure s0
  -- Build the parent's undo chain standalone: interior waypoint MVars are
  -- filled here, but the head (destined for m') is only returned and the
  -- terminal child m is left unwritten.  We publish m and m' only after body
  -- completes, so no racing reader can block on a half-built chain, and body's
  -- array writes are ordered before any reader can observe the new root.
  (m, srcContents) <- buildChain s l0 l
  body s                                         -- fill [l0 .. l-1]
  putMVar m  (Here (incMut (l - l0) s))          -- child root, only after body
  putMVar m' srcContents                         -- release parent, only after body
  pure (Vec l m)

-- Build a Write undo chain  head -> ... -> tgt, one entry per (index, old
-- value), allocating and filling a fresh waypoint MVar for each interior link.
-- Returns the head VecContents to be stored into the parent's MVar; the
-- terminal tgt is deliberately NOT written here (the caller publishes it).
buildChain :: Storage a -> Idx -> Len -> IO (VecVar a, VecContents a)
buildChain s i l = do
  n <- newEmptyMVar
  old <- readStorage s i
  m <- if i+1 >= l then pure n else buildChain' n s (i+1) l
  pure (m, Write n i old)

buildChain' :: VecVar a -> Storage a -> Idx -> Len -> IO (VecVar a)
buildChain' n _ i l | i >= l = pure n
buildChain' n s i l = do
  m <- newEmptyMVar
  old <- readStorage s i
  putMVar n (Write m i old)
  buildChain' m s (i+1) l

focusContents :: HasCallStack => MutCount -> Len -> VecVar a -> VecContents a -> IO (Storage a)
focusContents _  _ _ Invalid = invalidErr "focusContents"
focusContents _  _ _ (Here s) = pure s
focusContents k' l m (Write m' i a) = do
  c <- takeMVar m'
  s@(Storage _ k _) <- focusContents 1 l m' c
  s' <- case s of
    _ | k >= l+k' -> do
          s' <- cloneAll s
          const s' <$> putMVar m' (Here s)
      | otherwise -> do
          a' <- readStorage s i
          const (incMut k' s) <$> putMVar m' (Write m i a')
  const s' <$> writeStorage s' i a

-- focusSwap take a full v, gets focus, and writes a to index i,
-- returning the previous contents at that index along with a fresh
-- VecVar to represent the state.
focusSwap :: Vec a -> Idx -> a -> IO (a, Vec a)
focusSwap (Vec l m') i a = do
  m <- newEmptyMVar
  -- From here on we're in the write case of focusContents.
  c <- takeMVar m'
  s@(Storage _ k _) <- focusContents 1 l m' c
  a' <- readStorage s i
  s' <- case s of
    _ | k >= l+1 -> do
          s' <- cloneAll s
          const s' <$> putMVar m' (Here s)
      | otherwise -> do
           const (incMut k s) <$> putMVar m' (Write m i a')
  writeStorage s' i a
  putMVar m (Here s')
  pure (a', Vec l m)

-- Persist a particular version, meaning the next time it is
-- used in an operation we discard all subsequent snapshots.
persistIO :: Vec a -> IO (Vec a)
persistIO (Vec l m) = do
  c <- takeMVar m
  s <- case c of
    Invalid -> invalidErr "persist"
    Here s -> pure s
    Write m' i a -> do
      s <- persistFocus m'
      const s <$> writeStorage s i a
  const (Vec l m) <$> putMVar m (Here (resetMut s))

-- Sieze permanent ownership of m, invalidating it.
persistFocus :: VecVar a -> IO (Storage a)
persistFocus m = do
  c <- takeMVar m
  putMVar m Invalid
  case c of
    Invalid -> invalidErr "persist focus (should not happen?!)"
    Here s -> pure s
    Write m' i a -> do
      s <- persistFocus m'
      const s <$> writeStorage s i a

-- fromListION is much more efficient than replicating and then
-- repeatedly writing, since it can write in bulk at creation time and
-- ignore intermediate states that might otherwise need to persist.
fromListION :: Int -> [a] -> IO (Vec a)
fromListION 0 _ = pure empty
fromListION l as = do
  arr <- unsafeThawArray (arrayFromListN l as)
  Vec l <$> newMVar (Here (Storage l 0 arr))

-- Eagerly turn contents into a list.
toListIO :: Vec a -> IO [a]
toListIO (Vec 0 _) = pure []
toListIO v@(Vec l _) =
  -- Convert eagerly while we have focus.
  withReadFocus v (\s -> mapM (readStorage s) [0..l-1])

-- copy and truncate the current contents of the Vec and start a new history
copyIO :: Vec a -> IO (Vec a)
copyIO (Vec 0 _) = pure empty
copyIO v@(Vec l _) = do
  s <- withReadFocus v (cloneStorage l)
  Vec l <$> newMVar (Here s)

-- pop the last element, cleaning the underlying storage.
popIO :: Vec a -> IO (Maybe (a, Vec a))
popIO (Vec 0 _) = pure Nothing
popIO v@(Vec l _) =
  (\(a, Vec _ m) -> Just (a, Vec (l-1) m) ) <$> focusSwap v (l - 1) undefined

-- push a new element.
pushIO :: Vec a -> a -> IO (Vec a)
pushIO v@(Vec l _) a = growFocus v (l+1) (\s -> writeStorage s l a)

-- Append a series of vectors to the given vector.  Branch-safe, and correct
-- even when a vector is appended to itself or to one that shares its storage
-- or history: we snapshot every source's contents (read-only, one at a time)
-- *before* mutating anything, then grow the base in a single shot.  Snapshot
-- first avoids the self-aliasing copy and the deadlock of re-taking a shared
-- MVar mid-append; the single growFocus focuses and expands just once.
sconcatIO :: Vec a -> [Vec a] -> IO (Vec a)
sconcatIO va [] = pure va
sconcatIO va@(Vec l0 _) vs = do
  addends <- concat <$> mapM toListIO vs
  case addends of
    [] -> pure va
    _  -> growFocus va (l0 + length addends) (\s -> fill s l0 addends)
  where
    fill _ _ []     = pure ()
    fill s i (x:xs) = writeStorage s i x >> fill s (i+1) xs

-- Compute function of list form.
withListIO :: ([a] -> b) -> Vec a -> IO b
withListIO f (Vec 0 _) = pure (f [])
withListIO f v@(Vec l _) = do
  withReadFocus v (\s -> f <$> mapM (readStorage s) [0..l-1])

------------------------------------------------------------
-- Pure interface

replicate :: Len -> a -> Vec a
replicate l a = unsafeDupablePerformIO (replicateIO l a)

(!) :: HasCallStack => Vec a -> Idx -> a
v ! i = unsafeDupablePerformIO (readVecIO v i)

-- Returns a new vec with the write performed.  The old vec is unchanged.
writeVec :: Vec a -> Idx -> a -> Vec a
writeVec v i a = unsafeDupablePerformIO (writeVecIO v i a)

pop :: Vec a -> Maybe (a, Vec a)
pop a = unsafeDupablePerformIO (popIO a)

push :: Vec a -> a -> Vec a
push v a = unsafeDupablePerformIO (pushIO v a)

-- Push and return index of pushed value.
pushAndIndex :: Vec a -> a -> (Idx, Vec a)
pushAndIndex v@(Vec l _) a = (l, push v a)

-- What are the semantics of Vec?  Mostly a promise we won't reuse its ancestors.
persist :: Vec a -> Vec a
persist v = unsafeDupablePerformIO (persistIO v)

-- Make a fresh copy with an empty history (and truncate to current length).
copy :: Vec a -> Vec a
copy v = unsafeDupablePerformIO (copyIO v)

-- Operate on list contents of vec.  Should be better than f (toList v)?
withList :: ([a] -> b) -> Vec a -> b
withList f v = unsafeDupablePerformIO (withListIO f v)

instance Semigroup (Vec a) where
  a <> b = sconcat (a :| [b])
  sconcat (a :| as) = unsafeDupablePerformIO (sconcatIO a as)

-- WARNING: Vectors may not share a common origin!
instance Monoid (Vec a) where
  mempty = empty
  mappend = (<>)
  mconcat [] = empty
  mconcat (a:as) = sconcat (a :| as)

instance IsList (Vec a) where
  type Item (Vec a) = a

  fromListN :: Int -> [a] -> Vec a
  fromListN l as = unsafeDupablePerformIO (fromListION l as)

  fromList :: [a] -> Vec a
  fromList as = fromListN (length as) as

  toList :: Vec a -> [a]
  toList as = unsafeDupablePerformIO (toListIO as)

instance Foldable Vec where
  foldMap f = withList (foldMap f)
  foldr f z = withList (foldr f z)
  foldl f z = withList (foldl f z)
  foldl' f z = withList (foldl' f z)
  length (Vec l _) = l
  null v = length v == 0

instance Functor Vec where
  fmap f = withList (fromList . fmap f)

instance Traversable Vec where
  traverse f = withList (fmap fromList . traverse f)
