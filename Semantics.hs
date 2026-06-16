{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase, TypeFamilies #-}
module Semantics(evalTop) where
import AST
import Parse(SpanPos, spanPrefix)
import Primitive
import Value

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.BakerVec as V
import Data.ByteString(ByteString)
import Data.ByteString.UTF8(toString)
import Data.List(sortOn)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import GHC.Exts(IsList(..))
import GHC.Stack(HasCallStack)
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint((<+>))
import Debug.Trace(trace)
import Prelude hiding (span)

trace_match :: Bool
trace_match = False

trace_app_compile :: Bool
trace_app_compile = True || trace_app

trace_app :: Bool
trace_app = False

traceM :: (PP a, PP c) => a -> String -> c -> b -> b
traceM a s c b | trace_match = trace (showPp a++s++showPp c) b
traceM _ _ _ e = e

traceCAp :: String -> String -> ByteString -> b -> b
traceCAp s m nm b | trace_app_compile = trace (s++m++toString nm) b
traceCAp _ _ _  b = b

traceAp :: String -> String -> ByteString -> b -> b
traceAp s m nm b | trace_app = trace (s++m++toString nm) b
traceAp _ _ _  b = b

{-
-- List model for Vec
type BV a = [a]
vpush :: BV a -> a -> BV a
vpush v a = v ++ [a]

empty :: BV a
empty = []

(!) :: HasCallStack => BV a -> Int -> a
(!) = (!!)
-}

-- BakerVec model for Vec
type BV a = V.Vec a

vpush :: BV a -> a -> BV a
vpush = V.push

empty :: HasCallStack => BV a
empty = V.empty

(!) :: BV a -> Int -> a
(!) = (V.!)

type Ofs = (GL, Int)

data GL = Global | Closure | Local
  deriving (Eq, Show)

type Env = (Map Var (Known, Ofs), Int)
type Stack = BV Value
type Closure = BV Value
type Globals = BV Value
type CloMap = BV Int

type Pat = Exp

-- Closures, Descriptors, and Values
type Value = Val EI

data SimEnv = SameEnv | DiffEnv deriving (Eq, Show)

data Known
  = Unknown
  | KnownValue Value
  | KnownDesc SimEnv (Desc EI)
  deriving (Eq, Show)

sameEnv :: Known -> Known
sameEnv (KnownDesc _ d) = KnownDesc SameEnv d
sameEnv kn = kn

-- The information-theoretic join on Known
instance Semigroup Known where
  a <> b
    | a == b = a
  KnownValue (VObj a _) <> KnownValue (VObj b _)
    | a == b = KnownDesc DiffEnv a
  KnownValue (VPAp a _ _) <> KnownValue (VPAp b _ _)
    | a == b = KnownDesc DiffEnv a
  _ <> _ = Unknown

instance PP Known where
  pp Unknown = PP.text "Unknown"
  pp (KnownValue v) = pp v
  pp (KnownDesc SameEnv (Desc v n _ _)) =
    PP.text "<k same env " <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (KnownDesc _ (Desc v n _ _)) =
    PP.text "<k" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")

-- Utilities not worth an import
fromMaybe :: a -> Maybe a -> a
fromMaybe d = maybe d id

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM d m = m >>= maybe d pure

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

spanError :: HasCallStack => Span -> String -> SpanPos -> a
spanError s msg sp = error (spanPrefix s sp ++ msg)

-- Evaluation (environment) monads
type Outer = (SpanPos, GL, Env)   -- Outer, environment and analysis info.
type Inner = (Globals, Closure, Stack)  -- Inner, factored value state.
type EO a = Reader Outer a  -- Outer evaluation monad: compilation.
newtype EI a = EI (Reader Inner a) -- Inner, actual evaluation.
  deriving (Functor, Applicative, Monad, MonadReader Inner)
type Ef b a = EO (Known, b -> EI a) -- Analysis parameterized by input
type EV = EO (Known, EI Value) -- Analyze and yield a value.
type Push = Value -> Inner -> Inner

runInner :: EI a -> Inner -> a
runInner (EI r) = runReader r

instance MonadEval EI where
  type ClosureState EI = Closure
  withClo clo = local (\t -> (fst3 t, clo, empty))

bindEnvWith :: ((Known, Ofs) -> (Known, Ofs) -> (Known, Ofs)) ->
               Var -> Known -> Outer -> Outer
bindEnvWith c i kn (sp, gl, (env, k)) =
  (sp, gl, (M.insertWith c i (kn, (gl, k)) env, k + 1))

lookupEnv :: HasCallStack => Span -> Var -> Outer -> (Known, Ofs)
lookupEnv s i (sp, _, (env, _)) =
  fromMaybe (spanError s ("Unbound variable "++toString i) sp) $
    M.lookup i env

mkPush :: GL -> Push
mkPush Global = \v (g, c, s) -> (v `seq` vpush g v, c, s)
mkPush Local = \v (g, c, s) -> (g, c, v `seq` vpush s v)
mkPush Closure = error "mkPush Closure isn't a thing."

expPush :: EO Push
expPush = do
  gl <- expGL
  pure (mkPush gl)

expGL :: EO GL
expGL = (\(_, gl, _) -> gl) <$> ask

withEnv :: Env -> EO a -> EO a
withEnv env = local (\(sp, gl, _) -> (sp, gl, env))

withSameClo :: EI a -> EI a
withSameClo = local (\(g, clo, _) -> (g, clo, empty))

withNoClo :: EI a -> EI a
withNoClo = local (\(g, _, _) -> (g, empty, empty))

withDiffEnv :: EO a -> EO a
withDiffEnv = local (\(sp, gl, (env, k)) -> (sp, gl, (diffEnv <$> env, k))) where
  diffEnv (KnownDesc SameEnv d, k) = (KnownDesc DiffEnv d, k)
  diffEnv t = t

locally :: EO a -> EO a
locally = local modGL where
  modGL (sp, Global, (env, _)) = (sp, Local, (env, 0))
  modGL s = s

-- Convert local env into closure env.
closed :: Set Var -> EO a -> EO (CloMap, a)
closed vs act = do
  (sp, gl, (env, _)) <- ask
  let -- At runtime we're going to append closure and locals and then
      -- pull vars from them to create a new closure environment
      -- containing only fv.  Compute a vector mapping slots in the
      -- new closure to the subset of offsets in this vector we want to keep.
      -- Find first slot after current closure, where the locals will start.
      k0 = 1 + maximum (-1 : [ k | (_, (Closure, k)) <- M.elems env ])
      -- Compute the offsets of the locals.
      close (Global, _) = []
      close (Local, k) = [(k0 + k)]
      close (Closure, k) = [k]
      tuples = sortOn thd3
        [ (i, kn, k) | (i, (kn, ofs)) <- M.toAscList env, k <- close ofs, i `S.member` vs]
      mapping = fromList (thd3 <$> tuples)
      env' = M.fromList [ (i, (kn, (Closure, k'))) | ((i, kn, _), k') <- zip tuples [0..]]
      -- Not sure okKnown is actually doing anything here yet.
      okKnown (KnownValue _) = True
      okKnown (KnownDesc SameEnv _) = True
      okKnown _ = False
      genv = M.filter (\(kn, (glv, _)) -> glv == Global || okKnown kn) env
      env'' = genv <> env'
  r <- local (const (sp, gl, (env'', 0))) act
  pure (mapping, r)

expSP :: EO SpanPos
expSP = asks fst3

expError :: HasCallStack => Span -> String -> EO a
expError s msg = spanError s msg <$> expSP

getVecs :: EI Inner
getVecs = ask

findEnv :: HasCallStack => Span -> Var -> EV
findEnv s i = do
  (kn, (gl, o)) <- asks (lookupEnv s i)
  pure (kn,
    case gl of
      Global -> asks ((! o) . fst3)
      Closure -> asks ((! o) . snd3)
      Local -> asks ((! o) . thd3))

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: (EO [(Var, (Known, EI Value))]) -> EV -> EV
fixEnv a inner = do
  (sp, gl, (env, k)) <- ask
  let vs = runReader a (sp, gl, (env', k'))
      k' = k + length vs
      env' = M.fromList (zipWith (\(i, (kn, _)) n -> (i,(sameEnv kn, (gl, n)))) vs [k..]) <> env
      env'' = M.fromList (zipWith (\(i, (kn, _)) n -> (i,(kn, (gl, n)))) vs [k..]) <> env
  (kn, inner') <- withEnv (env'', k') inner
  push <- expPush
  pure (kn, do
    vec <- getVecs
    let vec' = foldl (\ve (_, (_, f)) -> push (runInner f vec') ve) vec vs
    local (const vec') inner')

-- Handles a *constant* binding (constructor def)
conBinding :: Var -> Value -> EV -> EV
conBinding i v r = do
  (_, gl, _) <- ask
  let push = mkPush gl
  local (bindEnvWith const i (KnownValue v)) $ do
    (kn, r') <- r
    pure (kn, local (push v) r')

-- Match monad.  First, static information about a match.
data Mode = AlwaysSucceeds | MayFail | AlwaysFails deriving (Eq, Show)

-- The join semigroup (disjoint conditions)
instance Semigroup Mode where
  MayFail <> _ = MayFail
  AlwaysSucceeds <> AlwaysSucceeds = AlwaysSucceeds
  AlwaysSucceeds <> _ = MayFail
  AlwaysFails <> AlwaysFails = AlwaysFails
  AlwaysFails <> _ = MayFail

-- The meet semigroup (same condition)
meet :: Mode -> Mode -> Mode
meet AlwaysFails _ = AlwaysFails
meet AlwaysSucceeds o = o
meet MayFail AlwaysFails = AlwaysFails
meet MayFail _ = MayFail

type MO a = State Outer a -- Outer: compute match environment, flag dup bindings.
type MI a = StateT Inner Maybe a -- Inner: decide match and bind variables
type M v a = MO (Mode, v -> MI a) -- Analyze, produce matcher for v yielding a.

matched :: Span -> Var -> Known -> M Value ()
matched s i kn = do
  sp <- matchSP
  let collide _ _ = spanError s ("Duplicate pattern bindings for variable "++toString i) sp
  modify $ bindEnvWith collide i kn
  withPush AlwaysSucceeds $ \push v -> modify (push v)

alwaysSucceed :: M a ()
alwaysSucceed = pure (AlwaysSucceeds, \_ -> pure ())

alwaysFail :: M a ()
alwaysFail = pure (AlwaysFails, \_ -> matchFail)

mayFail :: (v -> MI a) -> M v a
mayFail r = pure (MayFail, r)

matchFail :: MI a
matchFail = lift Nothing

matchSP :: MO SpanPos
matchSP = gets fst3

matchError :: HasCallStack => Span -> String -> MO a
matchError s msg = spanError s msg <$> matchSP

withPush :: Mode -> (Push -> a) -> MO (Mode, a)
withPush m f = do
  (_, gl, _) <- get
  pure (m, f (mkPush gl))

-- Inject match into evaluation
withMatch :: HasCallStack => Span -> M b () -> EV -> Ef b (Maybe Value)
withMatch s m t = do
  (sp, gl, (env, k)) <- ask
  let ((mode, f), (_, _, (env', k'))) = runState m (sp, gl, (mempty, k))
  withEnv (env' <> env, k') $ do
    (kn, t') <- t
    pure (kn, \v -> do
      vec <- getVecs
      case execStateT (f v) vec of
        Just _ | mode == AlwaysFails -> spanError s ("AlwaysFails succeeded!") sp
        Just vec' -> Just <$> local (const vec') t'
        Nothing | mode == AlwaysSucceeds -> spanError s ("AlwaysSucceeds failed!") sp
        Nothing -> pure Nothing)

-- Assumes length ps == length vs
matches :: HasCallStack => [Pat] -> [Known] -> M [Value] ()
matches [p] [k] = do
  (mode, f) <- match p k
  sp <- matchSP
  pure (mode, \case
    [v] -> f v
    vs -> spanError (span p) ("Pat len mismatch "++show (pp p)++" and "++showsPp vs) sp)
matches [] _ = error "Empty pats; shouldn't happen!"
matches ps ks = do
  (mode, ms) <- matches' ps ks
  pure (mode, \vs -> do
    vec <- get
    case execStateT (ms vs) vec of
      Just vec' ->
        traceM ps " match " vs $
          put vec'
      Nothing -> matchFail)

matches' :: HasCallStack => [Pat] -> [Known] -> M [Value] ()
matches' ps ks = do
  let n = length ps
  fs <- zipWithM match' ps ks
  sp <- matchSP
  pure (foldl1 (<>) (map fst fs), \vs ->
    if length vs == n then
      zipWithM_ (($) . snd) fs vs
    else
      spanError (span ps) ("Pat len mismatch "++showsPp ps++" and "++showsPp vs) sp)

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Pat -> Known -> M Value ()
match p kn = do
  (mode, f) <- match' p kn
  pure (mode, \val -> do
    vec <- get
    case execStateT (f val) vec of
      Just vec' -> traceM p " matches " val $ put vec'
      Nothing -> matchFail)

match' :: HasCallStack => Pat -> Known -> M Value ()
match' (Paren _ p) kn = match p kn
match' (Wild _) _ = alwaysSucceed
match' (Id s _ Var var) kn = matched s var kn
match' (Id _ _ Con con) (KnownValue (VCon0 con'))
  | con == con' = alwaysSucceed
match' (Id _ _ Con   _) (KnownValue _) = alwaysFail
match' (Id _ _ Con con) _ = mayFail $ \case
  (VCon0 con') | con == con' -> pure ()
  _ -> matchFail
match' (Const _ c) (KnownValue (VConst c'))
  | c == c' = alwaysSucceed
match' (Const _ _) (KnownValue _) = alwaysFail
match' (Const _ c) _ = mayFail $ \case
  (VConst vc) | c == vc -> pure ()
  _ -> matchFail
match' (Tuple s []) kn =
  match' (Id s Op Con "()") kn
match' (Tuple s es) kn =
  match' (App s (Id s Op Con "()") es) kn
match' (Block (_, ds)) _ = do
  ms <- map snd <$> mapM matchField ds
  mayFail $ \case
    (VStruct fs) -> mapM_ ($ fs) ms
    _ -> matchFail
match' p@(App s (Id _ _ Con con) as) kn = do -- Can't avoid the match now
  let len = length as
      kns = const Unknown <$> as -- TODO: known con args
  (m, fs) <- matches' as kns
  let mode AlwaysSucceeds (KnownDesc _ (Desc con' i _ _)) | con == con' && i == len = AlwaysSucceeds
      mode _ (KnownDesc _ (Desc con' i _ _)) | con /= con' || i /= len = AlwaysFails
      mode _ _ = meet MayFail m
  sp <- matchSP
  pure (mode m kn, \case
    v@(VCon cn n rs)
      | n /= length rs ->
          spanError s ("Obj ctor arity "++show n++" mismatch "++showPp v) sp
      | len == n && con == cn -> fs rs
      | len /= n && con == cn ->
          spanError s ("Constructor pat expected arity "++show n ++ ": "++showPp p) sp
    _ -> matchFail)
match' p@(App s _ _) _ = matchError s ("No constructor at head of pattern "++showPp p)
match' p _ = matchError (span p) ("Unrecognized pattern "++showPp p)

matchField :: HasCallStack => (Span, Def) -> M (Map FieldName Value) ()
matchField (_, Def (Id _ _ Var fn) p) = do
  (mode, f) <- match' p Unknown
  pure (mode, \fs -> lift (M.lookup fn fs) >>= f)
matchField (s, p) = matchError s ("Illegal struct pattern "++showPp p)

isKnownValue :: Known -> Bool
isKnownValue (KnownValue _) = True
isKnownValue _ = False

knownArity :: Known -> Maybe Arity
knownArity (KnownDesc _ (Desc _ a _ _)) = Just a
knownArity (KnownValue (VDesc (Desc _ a _ _))) = Just a
knownArity _ = Nothing

-- Apply value to args.
apply :: HasCallStack => String -> (Known, EI Value) -> [(Known, EI Value)] -> (Known, EI Value)
apply s (kn, f) as = app (knownArity kn)
  where
    as' = map snd as
    app Nothing = traceCAp s "  apply " "unknown" $ (Unknown, applyUnknown s f as')
    app (Just a) = applyKnown s a kn f as

applyKnown :: HasCallStack => String -> Arity -> Known -> EI Value -> [(Known, EI Value)] -> (Known, EI Value)
applyKnown s a kn f as
  | a > len =
      let apfn = pApKnown s kn f
          as' = map snd as
      in apfn `seq` (Unknown, apfn =<< args as')
  | a < len = do
    let (bs, cs) = splitAt a as
    apply s (applyKnown s a kn f bs) cs
  where len = length as
applyKnown s _ (KnownValue (VDesc (Desc i _ Fold (CloFun f)))) _ as
  | all (isKnownValue . fst) as = traceCAp s " constant fold " i $ do -- Constant fold!
      let r = runInner (f [ v | (KnownValue v, _) <- as]) (empty, empty, empty)
      (KnownValue r, pure r)
applyKnown s _ kn f as =
  let apfn = applyKnown' s kn f
      as' = map snd as
  in apfn `seq` (Unknown, apfn =<< args as') -- Drop known-arg info

args :: [EI Value] -> EI [Value]
args = foldr (\arg act -> do as' <- act; a <- arg; a `seq` pure (a:as')) (pure [])

applyKnown' :: HasCallStack =>
  String -> Known -> EI Value -> [Value] -> EI Value
applyKnown' s (KnownValue (VDesc (Desc nm _ _ (CloFun f)))) _ = traceCAp s " known VDesc " nm $ \as -> do
  withNoClo $ f as
applyKnown' s (KnownDesc SameEnv (Desc nm _ _ (CloFun f))) _ = traceCAp s " known SameEnv " nm $ \as -> do
  withSameClo $ f as
applyKnown' s (KnownDesc _ (Desc i _ _ (CloFun f))) v = traceCAp s " known DiffEnv " i $ \as -> do
  v' <- v
  case v' of
    VPAp (Desc i' _ _ _) vec bs
      | i == i' -> withClo vec $ f (bs <> as)
    _ -> error (s++"applyKnown "++toString i++": bad closure "++showPp v')
applyKnown' s kn _ = error (s++"applyKnown non-descy " ++ show kn)

pApKnown :: HasCallStack =>
  String -> Known -> EI Value -> [Value] -> EI Value
pApKnown s (KnownValue (VDesc d@(Desc nm _ _ _))) _ = traceCAp s " pknown VDesc " nm $ \as -> do
  pure $ VPAp d mempty as
pApKnown s (KnownDesc SameEnv d@(Desc nm _ _ _)) _ = traceCAp s " pKnown SameEnv " nm $ \as -> do
  (_, clo, _) <- ask
  pure $ VPAp d clo as
pApKnown s (KnownDesc _ d@(Desc nm _ _ _)) v = traceCAp s " pKnown DiffEnv " nm $ \as -> do
  v' <- v
  case v' of
    VPAp _ vec [] -> pure $ VPAp d vec as
    _ -> error (s ++ "Unrecognized closure "++showPp v')
pApKnown s kn _ = error (s++"non-closure pApKnown "++showPp kn)

-- Evaluate function and args
applyUnknown :: HasCallStack =>
  String -> EI Value -> [EI Value] -> EI Value
applyUnknown s f as = do
  vs <- args as
  v <- f
  applyInner s v vs

-- Unpack closures
applyInner :: HasCallStack => String -> Value -> [Value] -> EI Value
applyInner s (VDesc d) vs = appWithDesc s d empty (length vs) vs
applyInner s (VPAp d@(Desc nm _ _ _) vec as) bs = traceAp s "   Expand pap " nm $ do
  let vs = as <> bs
  appWithDesc s d vec (length vs) vs
applyInner s v _ = error (s ++ "bad closure "++showPp v)

-- Apply function to args (arities given)
appWithDesc :: HasCallStack =>
  String -> Desc EI -> Stack -> Arity -> [Value] -> EI Value
appWithDesc s d@(Desc nm n _ (CloFun f)) vec nv vs
  | n > nv = traceAp s "   PAp " nm $ pure $ VPAp d vec vs
  | n == nv = traceAp s "   sat " nm $ withClo vec $ f vs
  | otherwise = traceAp s "   split sat " nm $ do
      let (vs', vs'') = splitAt n vs
      f' <- withClo vec (f vs')
      applyInner s f' vs''

appDisjs :: HasCallStack => Span -> Var -> [([Pat], Exp)] -> [Known] -> Ef [Value] Value
appDisjs s f ds knp = do
  pes <- mapM (\(ps, e) -> withMatch (span ps) (matches ps knp) (eval e)) ds
  let kn = foldr1 (<>) (map fst pes)
      ms = map snd pes
  sp <- expSP
  pure (kn, \vs -> do
          let oneMatch [] = spanError s ("Match failure in "++show f ++ " " ++ showsPp vs) sp
              oneMatch (m:mr) = fromMaybeM (oneMatch mr) (m vs)
          oneMatch ms)

eval :: HasCallStack => Exp -> EV
eval (Id s _ _ i) = findEnv s i
eval (App s e es) = do
  e' <- eval e
  es' <- mapM eval es -- Effects need to be l -> r
  sPre <- spanPrefix s <$> expSP
  pure $ apply sPre e' es'
eval (Const _ c) = pure (KnownValue $ VConst c, pure $ VConst c)
eval e@(Fn s (_, ds)) = do
  (a, cs) <- mkRhs s ds <$> expSP
  withDiffEnv $ vClo s "<anon>" a (fv e) cs
eval (Tuple _ es) = do
  es' <- traverse eval es
  let d = cDesc "()" (length es')
      kn | null es = KnownValue (VDesc d)
         | otherwise = KnownDesc DiffEnv d
      vs = fmap snd es'
  pure (kn, VObj d <$> args vs)
eval (Case s e (_,es)) = do
  (ekn, e') <- eval e
  sp <- expSP
  (kn, m) <- locally $ appDisjs s "<case>" (map (toDisj sp) es) [ekn]
  pure (kn, do
    v <- e'
    m [v])
eval (Block b) = locally (evDefs b)
eval e = expError (span e) ("eval: Unhandled expression\n  "++showPp e++"\n  "++show e)

evDefs :: Defs -> EV
evDefs b =
  case groupDefs b of
    Left es -> do
      sp <- expSP
      error $ unlines $ (\(s, err) -> spanPrefix s sp <> toString err) <$> es
    Right ds -> evGroups ds

evGroups :: HasCallStack => [DefGroup] -> EV
evGroups [] = do
  let v = VStruct mempty
  pure (KnownValue v, pure v)
evGroups (Fns fs:ts) = withDiffEnv $ fixEnv (traverse clo fs) (evGroups ts)
  where clo (s, v, n, cs) = (v,) <$> vClo s v n closeOver cs
        closeOver = fv (Fns fs)
evGroups [Record m] = do
  ms <- locally $ traverse eval m
  pure (Unknown, VStruct <$> sequenceA (snd <$> ms))
evGroups [D (BindExp e)] = locally $ eval e
evGroups (D (BindExp e) : ts) = do
  (_, e') <- locally $ eval e
  (kn, r) <- evGroups ts
  pure (kn, e' >>= \v -> v `seq` r) -- Make sure to demand v in case it's an effect!  Hack!
evGroups (D (Def p e) : ts) = do
  (ekn, e') <- locally $ eval e
  (kn, m) <- withMatch (span p) (match p ekn) (evGroups ts)
  pure (kn, do
    v <- e'
    fromMaybeM (error ("Match failure "++showPp p++" = "++showPp v)) (m v))
evGroups (D (Data _ (_,ds)) : ts) = foldr addCon (evGroups ts) ds
evGroups (g : _) = error ("Unexpected group "++showPp g)

vClo :: HasCallStack => Span -> Var -> Arity -> Set Var -> [([Pat], Exp)] -> EV
vClo s f n vs ds = do
  -- The icky thing here is we do the "closed vs" computation for every function
  -- in a binding group separately, even though the resulting env should be the same
  -- (since it's based on the passed-in vs).
  (cloMap, (_, cf)) <- closed vs $ locally $ appDisjs s f ds (replicate n Unknown)
  let d = Desc f n NoFold (CloFun cf)
  gl <- expGL
  pure $ case gl of
    Global ->
      let v = VDesc d
      in (KnownValue v, pure v)
    Local ->
      (KnownDesc DiffEnv d, do
        (_, clo, vec) <- getVecs
        let every = clo <> vec
            clo' = (every!) <$> cloMap
        pure (VPAp d clo' []))
    Closure -> error "gl of Closure isn't a thing."

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> EV -> EV
addCon (_, BindExp (Asc _ (Id _ _ Con c) t)) = conBinding c (cCon c (typeArity t))
addCon (s, d) = const (expError s ("addCon: not a constructor def "++showPp d))

typeArity :: HasCallStack => Exp -> Arity
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

cDesc :: ConName -> Arity -> Desc EI
cDesc v i = d where
  d = Desc v i Fold (CloFun cf)
  cf | i == 0 = error ("Applying 0-ary "++toString v)
     | otherwise = pure . VObj d

cCon :: ConName -> Arity -> Value
cCon v i = VDesc (cDesc v i)

toDisj :: HasCallStack => SpanPos -> (Span, Def) -> ([Pat], Exp)
toDisj _ (_, Def p e) = ([p], e)
toDisj sp (s, d) = spanError s ("Illegal case disjunct "++showPp d) sp

mkRhs :: HasCallStack => Span -> [(Span, Def)] -> SpanPos -> (Arity, [([Exp], Exp)])
mkRhs s0 ds sp = do
  let one (_, Def p e) = (patToPats p, e)
      one (_, d) = spanError s0 ("Unexpected disjunct "++showPp d) sp
  case fmap one ds of
    [] -> spanError s0 "Empty anonymous function." sp
    c:cs
      | all ((==a) . length . fst) cs -> (a, c:cs)
      | otherwise -> spanError s0 ("Inconsistent arities, expect "++show a) sp
      where a = length . fst $ c

evalTop :: HasCallStack => (SpanPos, Defs) -> Value
evalTop (sp, ds) =
  let (env, vec) = expand env0
  in runInner (snd $ runReader (evDefs ds) (sp, Global, env)) (vec, empty, empty)


expand :: HasCallStack => Map Var Value -> (Env, BV Value)
expand e =
  foldl (\((env, k), vec) (i, v) ->
           ((M.insert i (KnownValue v, (Global, k)) env, k+1), vpush vec v))
        ((mempty, 0), empty)
        (M.toList e)
