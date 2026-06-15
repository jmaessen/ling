{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase #-}
module Semantics(evalTop) where
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.BakerVec as V
import Data.ByteString(ByteString)
import Data.ByteString.UTF8(toString, fromString)
import AST
import Parse(SpanPos, spanPrefix)
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
trace_app_compile = trace_app

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

showPp :: PP a => a -> String
showPp = show . pp

showsPp :: PP a => [a] -> String
showsPp as = show (PP.fsep (pp <$> as))

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

type ConName = ByteString
type FieldName = ByteString

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
newtype CloFun = CloFun ([Value] -> EI Value)

instance Eq CloFun where
  _ == _ = True -- Rely on parent to disambiguate.

instance Show CloFun where
  show _ = "<clofun>"

data Desc = Desc !Var !Arity CloFun
  deriving (Eq, Show)

data Value
  = VConst !Constant
  | VDesc !Desc
  | VPAp !Desc !Stack ![Value] -- Also closures
  | VObj !Desc ![Value]
  | VStruct !(Map FieldName Value)
  deriving (Eq, Show)

{-# COMPLETE VConst, VDesc, VPAp, VCon, VStruct #-}

data SimEnv = SameEnv | DiffEnv deriving (Eq, Show)

data Known
  = Unknown
  | KnownValue Value
  | KnownDesc SimEnv Desc
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

pattern VCon0 :: ConName -> Value
pattern VCon0 c <- VDesc (Desc c 0 _) where
  VCon0 c =
    VDesc (Desc c 0 (CloFun (\_ -> error ("Applying nullary "++ toString c))))

pattern VCon :: ConName -> Arity -> [Value] -> Value
pattern VCon c n vs <- VObj (Desc c n _) vs where
  VCon c n vs =
    VObj (Desc c n (CloFun (\_ -> error ("Applying already-built "++toString c)))) vs

toListVal :: Value -> Maybe [Value]
toListVal (VCon0 "[]") = Just []
toListVal (VCon "::" 2 [a,as]) = (a:) <$> toListVal as
toListVal _ = Nothing

instance PP Value where
  pp (VConst c) = pp (Const noSpan c)
  pp (VCon0 c) = PP.text (toString c)
  pp (VDesc (Desc v n _)) =
    PP.text "<d" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp (Desc v n _) _ []) =
    PP.text "<c" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp (Desc v _ _) _ vs) = PP.parens (PP.text (toString v) <+> PP.sep (pp <$> vs))
  pp c@(VCon "::" 2 [_,_])
    | Just cs <- toListVal c =
      PP.brackets (PP.fsep $ PP.punctuate (PP.text ",") (pp <$> cs))
  pp (VCon "()" _ vs) =
    PP.parens (PP.hsep $ PP.punctuate (PP.text ",") (pp <$> vs))
  pp (VCon c _ vs) = PP.parens (PP.text (toString c) <+> PP.sep (pp <$> vs))
  pp (VStruct vs) =
    PP.vcat [PP.lbrace, PP.text "", PP.nest 2 (PP.vcat $ fmap ppField (M.toList vs)), PP.rbrace]
    where ppField (f, v) = PP.text (toString f) <+> PP.text "=" <+> pp v

instance PP Known where
  pp Unknown = PP.text "Unknown"
  pp (KnownValue v) = pp v
  pp (KnownDesc SameEnv (Desc v n _)) = PP.text "<k same env " <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (KnownDesc _ (Desc v n _)) = PP.text "<k" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")

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
type EI a = Reader Inner a -- Inner, actual evaluation.
type Ef b a = EO (Known, b -> EI a) -- Analysis parameterized by input
type EV = EO (Known, EI Value) -- Analyze and yield a value.
type Push = Value -> Inner -> Inner

bindEnvWith :: ((Known, Ofs) -> (Known, Ofs) -> (Known, Ofs)) ->
               Var -> Known -> (SpanPos, GL, Env) -> (SpanPos, GL, Env)
bindEnvWith c i kn (sp, gl, (env, k)) =
  (sp, gl, (M.insertWith c i (kn, (gl, k)) env, k + 1))

lookupEnv :: HasCallStack => Span -> Var -> (SpanPos, GL, Env) -> (Known, Ofs)
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

withClo :: Closure -> EI a -> EI a
withClo clo = local (\(g,_,_) -> (g, clo, empty))

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
expSP = asks (\(sp, _, _) -> sp)

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
    let vec' = foldl (\ve (_, (_, f)) -> push (runReader f vec') ve) vec vs
    local (const vec') inner')

-- Handles a *constant* binding (constructor def)
conBinding :: Var -> Value -> EV -> EV
conBinding i v r = do
  (_, gl, _) <- ask
  let push = mkPush gl
  local (bindEnvWith const i (KnownValue v)) $ do
    (kn, r') <- r
    pure (kn, local (push v) r')

-- Match monad
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

type MO a = State Outer a -- Outer: compute match environment, handle dups
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
matchSP = gets (\(sp, _, _) -> sp)

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
match' (Asc _ p _) kn = match' p kn
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
match' (List s []) kn = match' (Id s Op Con "[]") kn
match' (List s (e:es)) kn =
  match' (App s (Id s Op Con "::") [e, List s es]) kn
match' (Block (_, ds)) _ = do
  ms <- map snd <$> mapM matchField ds
  mayFail $ \case
    (VStruct fs) -> mapM_ ($ fs) ms
    _ -> matchFail
match' (App s (Paren _ p) as) kn = match' (App s p as) kn
match' (App s (Asc _ p _) as) kn = match' (App s p as) kn
match' (App s (App _ p ps) as) kn = match' (App s p (ps <> as)) kn
match' p@(App s (Id _ _ Con con) as) kn = do -- Can't avoid the match now
  let len = length as
      kns = const Unknown <$> as -- TODO: known con args
  (m, fs) <- matches' as kns
  let mode AlwaysSucceeds (KnownDesc _ (Desc con' i _)) | con == con' && i == len = AlwaysSucceeds
      mode _ (KnownDesc _ (Desc con' i _)) | con /= con' || i /= len = AlwaysFails
      mode _ _ = meet MayFail m
  sp <- matchSP
  pure (mode m kn, \case
    v@(VCon cn n rs)
      | len /= length rs ->
          spanError s ("Obj ctor arity "++show n++" mismatch "++showPp v) sp
      | len == n && con == cn -> fs rs
      | len /= n && con == cn ->
          spanError s ("Constructor pat expected arity "++show n ++ ": "++showPp p) sp
    _ -> matchFail)
match' p@(App s _ _) _ = matchError s ("No constructor at head of pattern "++showPp p)
match' p _ = matchError (span p) ("Unrecognized pattern "++showPp p)

matchField :: HasCallStack => (Span, Def) -> M (Map FieldName Value) ()
matchField (s, BindExp p) = matchField (s, Def p p)
matchField (_, Def (Id _ _ Var fn) p) = do
  (mode, f) <- match' p Unknown
  pure (mode, \fs -> lift (M.lookup fn fs) >>= f)
matchField (s, Def f _) = matchError s ("Illegal struct binding lhs "++showPp f)
matchField (s, p) = matchError s ("Illegal struct pattern "++showPp p)

isKnownValue :: Known -> Bool
isKnownValue (KnownValue _) = True
isKnownValue _ = False

knownArity :: Known -> Maybe Arity
knownArity (KnownDesc _ (Desc _ a _)) = Just a
knownArity (KnownValue (VDesc (Desc _ a _))) = Just a
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
applyKnown _ _ (KnownValue (VDesc (Desc i _ (CloFun f)))) _ as
  | i == "prim" && all (isKnownValue . fst) as = do -- Constant fold!
      -- Needs re-thinking: Can't run top level fns in empty global env!
      -- That *only* works with primitives.
      -- Just a hack for "prim" now.
      let r = runReader (f [ v | (KnownValue v, _) <- as]) (empty, empty, empty)
      (KnownValue r, pure r)
applyKnown s _ kn f as =
  let apfn = applyKnown' s kn f
      as' = map snd as
  in apfn `seq` (Unknown, apfn =<< args as') -- Drop known-arg info

args :: [EI Value] -> EI [Value]
args = foldr (\arg act -> do as' <- act; a <- arg; a `seq` pure (a:as')) (pure [])

applyKnown' :: HasCallStack =>
  String -> Known -> EI Value -> [Value] -> EI Value
applyKnown' s (KnownValue (VDesc (Desc nm _ (CloFun f)))) _ = traceCAp s " known VDesc " nm $ \as -> do
  withNoClo $ f as
applyKnown' s (KnownDesc SameEnv (Desc nm _ (CloFun f))) _ = traceCAp s " known SameEnv " nm $ \as -> do
  withSameClo $ f as
applyKnown' s (KnownDesc _ (Desc i _ (CloFun f))) v = traceCAp s " known DiffEnv " i $ \as -> do
  v' <- v
  case v' of
    VPAp (Desc i' _ _) vec bs
      | i == i' -> withClo vec $ f (bs <> as)
    _ -> error (s++"applyKnown "++toString i++": bad closure "++showPp v')
applyKnown' s kn _ = error (s++"applyKnown non-descy " ++ show kn)

pApKnown :: HasCallStack =>
  String -> Known -> EI Value -> [Value] -> EI Value
pApKnown s (KnownValue (VDesc d@(Desc nm _ _))) _ = traceCAp s " pknown VDesc " nm $ \as -> do
  pure $ VPAp d mempty as
pApKnown s (KnownDesc SameEnv d@(Desc nm _ _)) _ = traceCAp s " pKnown SameEnv " nm $ \as -> do
  (_, clo, _) <- ask
  pure $ VPAp d clo as
pApKnown s (KnownDesc _ d@(Desc nm _ _)) v = traceCAp s " pKnown DiffEnv " nm $ \as -> do
  v' <- v
  case v' of
    VPAp _ vec [] -> pure $ VPAp d vec as
    _ -> error (s ++ "Unrecognized closure "++showPp v')
pApKnown s kn _ = error (s++"non-closure pApKnown "++showPp kn)

applyUnknown :: HasCallStack =>
  String -> EI Value -> [EI Value] -> EI Value
applyUnknown s f as = do
  vs <- args as
  v <- f
  applyInner s v vs

applyInner :: HasCallStack => String -> Value -> [Value] -> EI Value
applyInner s (VDesc d) vs = appWithDesc s d empty (length vs) vs
applyInner s (VPAp d@(Desc nm _ _) vec as) bs = traceAp s "   Expand pap " nm $ do
  let vs = as <> bs
  appWithDesc s d vec (length vs) vs
applyInner s v _ = error (s ++ "bad closure "++showPp v)

-- Apply function to args (arities given)
appWithDesc :: HasCallStack =>
  String -> Desc -> Stack -> Arity -> [Value] -> EI Value
appWithDesc s d@(Desc nm n (CloFun f)) vec nv vs
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
eval (Paren _ e) = eval e
eval (Asc _ e _) = eval e
eval (OpExp _ e) = eval e
eval (Id s _ _ i) = findEnv s i
eval a@(App s _ []) = expError s ("Empty apply "++showPp a)
eval (App s e es) = do
  e' <- eval e
  es' <- mapM eval es -- Effects need to be l -> r
  sPre <- spanPrefix s <$> expSP
  pure $ apply sPre e' es'
eval (Const _ c) = pure (KnownValue $ VConst c, pure $ VConst c)
eval (Wild s) = expError s "_ is a pat, not a valid expr"
eval e@(Arrow s _ _) = expError s (showPp e ++ " is a type, not a valid expr")
eval e@(Ops _ _) = expError (span e) (showPp e ++ " residual infix operators.")
eval e@(Fn s (_, ds)) = do
  sp <- expSP
  let (a, cs) = mkRhs sp s ds
  withDiffEnv $ vClo s "<anon>" a (fv e) cs
eval (Tuple _ es) = do
  es' <- traverse eval es
  let d = cDesc "()" (length es')
      kn | null es = KnownValue (VDesc d)
         | otherwise = KnownDesc DiffEnv d
  pure (kn, VObj d <$> mapM snd es')
eval (List _ []) = do
  let v = VCon0 "[]"
  pure (KnownValue v, pure v)
eval (List s (e:es)) = eval (App s (Id s Op Con "::") [e, List s es])
eval (Case s e (_,es)) = do
  (ekn, e') <- eval e
  sp <- expSP
  (kn, m) <- locally $ appDisjs s "<case>" (map (toDisj sp) es) [ekn]
  pure (kn, do
    v <- e'
    m [v])
eval (If _ c t e) = do
  (ckn, c') <- eval c
  case ckn of
    KnownValue (VCon0 "True") -> eval t
    KnownValue (VCon0 "False") -> eval e
    Unknown -> do
      (tkn, t') <- eval t
      (ekn, e') <- eval e
      sp <- expSP
      pure (tkn <> ekn, do
        c' >>= \case
          VCon0 "True" -> t'
          VCon0 "False" -> e'
          v -> spanError (span c) ("If non-boolean "++showPp v) sp)
    _ -> expError (span c) ("If statically non-boolean "++showPp ckn)
eval (IfMatch _ p c t e) = do
  (ckn, c') <- eval c
  (tkn, tm) <- locally $ withMatch (span p) (match p ckn) (eval t)
  (ekn, e') <- eval e
  pure (tkn <> ekn, do
    v <- c'
    fromMaybeM e' (tm v))
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
evGroups [Record m] = do
  ms <- locally $ traverse eval m
  pure (Unknown, VStruct <$> sequenceA (snd <$> ms))
evGroups (D (BindExp (Asc _ (Id _ _ _ _) _)) : ts@(_:_)) = evGroups ts
evGroups [D (BindExp e)] = locally $ eval e
evGroups (Fns fs:ts) = withDiffEnv $ fixEnv (traverse clo fs) (evGroups ts)
  where clo (s, v, n, ves) = (v,) <$> vClo s v n closeOver ves
        closeOver = fv (Fns fs)
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
evGroups (D (Fix _ _ _) : ts) = evGroups ts
evGroups (D (Data _ (_,ds)) : ts) = foldr addCon (evGroups ts) ds
evGroups (D (Struct _ _) : ts) = evGroups ts
evGroups (Record b:_) =
  expError (foldr1 (<>) (span <$> b)) ("unexpected record, shouldn't happen "++showPp (Record b))

vClo :: HasCallStack => Span -> Var -> Arity -> Set Var -> [([Pat], Exp)] -> EV
vClo s f n vs ds = do
  -- The icky thing here is we do the "closed vs" computation for every function
  -- in a binding group separately, even though the resulting env should be the same
  -- (since it's based on the passed-in vs).
  (cloMap, (_, cf)) <- closed vs $ locally $ appDisjs s f ds (replicate n Unknown)
  let d = Desc f n (CloFun cf)
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
addCon (_, BindExp e) = addCon' e
addCon (s, d) = const (expError s ("addCon: not a constructor def "++showPp d))

addCon' :: HasCallStack => Exp -> EV -> EV
addCon' (Paren _ e) = addCon' e
addCon' (Id _ _ Con c) = conBinding c (VCon0 c)
addCon' (App s (Paren _ e) as) = addCon' (App s e as)
addCon' (App s (App _ e as) as') = addCon' (App s e (as <> as'))
addCon' (App _ (Id _ _ Con c) as) = conBinding c (cCon c (length as))
addCon' (Asc s (Paren _ e) t) = addCon' (Asc s e t)
addCon' (Asc _ (Id _ _ Con c) t) = conBinding c (cCon c (typeArity t))
addCon' (List _ []) = conBinding "[]" (VCon0 "[]")
addCon' e = const (expError (span e) ("addCon': not a constructor def "++showPp e))

typeArity :: HasCallStack => Exp -> Arity
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

cDesc :: ConName -> Arity -> Desc
cDesc v i =
  case cCon v i of
    VDesc d -> d
    r -> error ("cDesc: Unexpected value "++showPp r)

cCon :: ConName -> Arity -> Value
cCon v 0 = VCon0 v
cCon v i = VDesc d
  where d = Desc v i (CloFun (pure . VObj d))

toDisj :: HasCallStack => SpanPos -> (Span, Def) -> ([Pat], Exp)
toDisj _ (_, Def p e) = ([p], e)
toDisj sp (s, d) = spanError s ("Illegal case disjunct "++showPp d) sp

mkRhs :: HasCallStack => SpanPos -> Span -> [(Span, Def)] -> (Arity, [([Exp], Exp)])
mkRhs sp s0 ds = rhs ds Nothing where
  rhs [] Nothing = spanError s0 "Empty anonymous function." sp
  rhs [] (Just a) = (a, [])
  rhs ((s, Def (App _ p ps) e) : ds') ma
    | a' /= a =
      spanError s ("arity "++show (length ps + 1)++
                   " doesn't match prior clause "++ show a) sp
    | otherwise =
      (a, ((p:ps), e) : snd (rhs ds' (Just a)))
    where a' = 1 + length ps
          a = fromMaybe a' ma
  rhs ((s, Def (Asc _ p _) e) : ds') a = rhs ((s, Def p e) : ds') a
  rhs ((s, Def p e) : ds') a = rhs ((s, Def (App s p []) e) : ds') a
  rhs ((s, _) : _) _ = spanError s ("invalid function clause.") sp

evalTop :: HasCallStack => (SpanPos, Defs) -> Value
evalTop (sp, ds) =
  let (env, vec) = expand env0
  in runReader (snd $ runReader (evDefs ds) (sp, Global, env)) (vec, empty, empty)

-- Definitions of primitives

mkPrim :: (Var, Arity, [Value] -> Value) -> (Var, Value)
mkPrim (v, n, f) = (v, VDesc (Desc v n (CloFun $ pure . f)))

vBool :: Bool -> Value
vBool True = VCon0 "True"
vBool False = VCon0 "False"

i2 :: HasCallStack => (a -> Value) -> (Integer -> Integer -> a) -> [Value] -> Value
i2 v op [VConst (EInt a), VConst (EInt b)] = v (a `op` b)
i2 _ _ vs = error ("Bad args "++showsPp vs)

valToList :: HasCallStack => Value -> [Value]
valToList v =
  case toListVal v of
    Just vs -> vs
    _ -> error ("valToList: not a list "++showPp v)

valToString :: HasCallStack => Value -> ByteString
valToString (VConst (EString s)) = s
valToString v = error ("valToString: not a string "++showPp v)

strConcat :: HasCallStack => [Value] -> Value
strConcat [v] = VConst (EString (mconcat (valToString <$> valToList v)))
strConcat vs = error ("strConcat: wrong number of args "++showPp vs)

valToInt :: HasCallStack => Value -> Integer
valToInt (VConst (EInt i)) = i
valToInt v = error ("valToInt: not an int "++showPp v)

getPrim :: HasCallStack => [Value] -> Value
getPrim [n, v] =
  case M.lookup (valToString v) env0 of
    Just r@(VDesc (Desc _ n' _))
      | fromInteger (valToInt n) == n' -> r
      | otherwise ->
        error ("Arity mismatch on prim "++showPp v++" registered as "++show n'++" asked for "++showPp n)
    _ -> error ("Bad prim "++showPp v)
getPrim as = error ("Bad args to prim "++showPp as)

expand :: HasCallStack => Map Var Value -> (Env, BV Value)
expand e =
  foldl (\((env, k), vec) (i, v) ->
           ((M.insert i (KnownValue v, (Global, k)) env, k+1), vpush vec v))
        ((mempty, 0), empty)
        (M.toList e)

env0 :: Map Var Value
env0 = foldl (\env p -> uncurry M.insert (mkPrim p) env) mempty [
  ("prim", 2, getPrim),
  ("intAdd", 2, i2 (VConst . EInt) (+)),
  ("intSub", 2, i2 (VConst . EInt) (-)),
  ("intEq", 2, i2 vBool (==)),
  ("intLE", 2, i2 vBool (<=)),
  ("strAppend", 2, \case
      [VConst (EString a), VConst (EString b)] -> VConst (EString (a <> b))
      vs -> error ("strAppend "++showsPp vs)
  ),
  ("putStr", 1, \case
      [v] -> trace (toString (valToString v)) (VCon0 "()") -- total hack, but "safe"
      vs -> error ("putStr "++showsPp vs)
  ),
  ("strConcat", 1, strConcat),
  ("intToStr", 1, \case
      [v] -> VConst $ EString $ fromString $ show $ valToInt v
      vs -> error ("intToStr "++showsPp vs)
  )
  ]
