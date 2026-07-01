{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase, TypeFamilies #-}
module Compile(compileTop) where
import AST
import CUtil
import Names
import Parse(SpanPos, spanError, spanPrefix)
import Primitive
import SemUtil
import Value

-- import Control.Applicative hiding (Const(..))
import Control.Monad
import Control.Monad.State
import Data.ByteString.UTF8(toString)
import Data.Foldable(traverse_)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Debug.Trace(trace)
import GHC.Stack(HasCallStack)
import Text.PrettyPrint hiding ((<>), Mode)
import Prelude hiding (span)

trace_match :: Bool
trace_match = False

trace_app_compile :: Bool
trace_app_compile = False || trace_app

trace_app :: Bool
trace_app = False

traceM :: (PP a, PP c) => a -> String -> c -> b -> b
traceM a s c b | trace_match = trace (showPp a++s++showPp c) b
traceM _ _ _ e = e

traceCAp :: PP v => String -> String -> v -> b -> b
traceCAp s m nm b | trace_app_compile = do
  trace (s++m++showPp nm) b
traceCAp _ _ _  b = b

-- Naming and Environments

data Entry = En {
  cv_ :: ConOrVar,
  kn_ :: Known,
  vgl_ :: GL,
  n_ :: Name}
    deriving (Eq, Show)
type Env = Map Var Entry

lazyEn :: Entry -> Entry
lazyEn e = En { cv_ = cv_ e, kn_ = kn_ e, vgl_ = vgl_ e, n_ = n_ e }

-- Closures, Descriptors, and Values
type Value = Val E
type Known = Knw E

-- Utilities not worth an import
fromMaybe :: a -> Maybe a -> a
fromMaybe d = maybe d id

zipWithA :: Applicative m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithA f as bs = sequenceA (zipWith f as bs)

-- Evaluation (environment) monads
data Cont = Bind Name | Return | Exp deriving (Eq, Show)
data St = St {
  -- Never changes
  sp_ :: SpanPos,
  -- Actually persistent state (after locally)
  tn_ :: TakenNames,
  nlbl_ :: !Label,
  -- Transient top-down state reset after `local`
  gl_ :: GL,
  env_ :: Env}
data Inner = Inner {
  -- Actually persistent state (after locally)
  fns_ :: Code,
  -- Function-persistent state
  decls_ :: Code,
  stmts_ :: Code}
type E = (State St)
--  deriving (Functor, Applicative, Monad, MonadState St)
type CG a = (State Inner a)
--  deriving (Functor, Applicative, Monad, MonadState Inner)
type V = (Known, CG Code) -- Result is for point of use
type EV = Cont -> E V

-- Merge old and new state, reverting transient to old state.
oldNew :: St -> St -> St
st `oldNew` st' =
  st'{ gl_ = gl_ st, env_ = env_ st }

-- Hack.  Rather than using a reader monad just for takennames,
-- we use state for everything and define `local` to do
-- the right thing.
local :: (St -> St) -> E a -> E a
local trans act = do
  st <- get
  put (trans st)
  r <- act
  st' <- get
  put (st `oldNew` st')
  pure r

runExp :: E a -> St -> (a, St)
runExp (r) = runState r

instance MonadEval E where
  type ClosureState E = Name -- Of local containing env object
  withClo = error "We don't withClo, callee unpacks"

withName :: (HasCallStack, MonadState St m) => Var -> m Name
withName i = do
  st <- get
  let gl = gl_ st
      tn = tn_ st
      n = mangle i gl tn
      tn' = takeName n tn
  put $ st{ tn_ = tn' }
  pure $ n

bindEnvWith ::
  (Entry -> Entry -> Entry) -> Var -> (ConOrVar, Known, Name) -> St -> St
bindEnvWith c i (cv, kn, nm) st =
  st{ env_ = M.insertWith c i (En cv kn (gl_ st) nm) (env_ st) }

lookupEnv :: HasCallStack => Span -> Var -> St -> Entry
lookupEnv s i (St {env_ = env, sp_ = sp}) =
  fromMaybe (spanError s ("Unbound variable "++toString i) sp) $
    M.lookup i env

-- Make a local replica of a name, mostly for the builtin names.
withClone :: Name -> E Name
withClone n = do
  st <- get
  let r = cloneName n (gl_ st) (tn_ st)
  put (st{ tn_ = takeName r (tn_ st) })
  pure r

withEnv :: Env -> E a -> E a
withEnv env = local (\st -> st{ env_ = env })

withDiffEnv :: E a -> E a
withDiffEnv = local (\st -> st{ env_ = (diffEnv <$> env_ st)}) where
  diffEnv en@(En{ kn_ = KnownDesc SameEnv d }) =
    en{ kn_ = KnownDesc DiffEnv d }
  diffEnv en = en

locally :: E a -> E a
locally = local (\st -> st { gl_ = Local}) where

expSP :: E SpanPos
expSP = gets sp_

expError :: HasCallStack => Span -> String -> E a
expError s msg = spanError s msg <$> expSP

findEnv :: HasCallStack => Span -> Var -> E Entry
findEnv s i = gets (lookupEnv s i)

-- Add a declaration to the current function
decl :: MonadState Inner m => Code -> m ()
decl c = modify (\st -> st { decls_ = decls_ st $$ c })

-- Add a statement to the current block
stmt :: MonadState Inner m => Code -> m ()
stmt c = modify (\st -> st { stmts_ = stmts_ st $$ c })

newLabel :: MonadState St m => m Label
newLabel = state $ \st -> do
  let lbl = nlbl_ st
  (lbl, st { nlbl_ = lbl + 1 })

toplevel :: Code -> CG ()
toplevel c = modify (\st -> st { fns_ = fns_ st $*$ c })

mkFnDecl :: Name -> Int -> CG ()
mkFnDecl n a =
  modify (\st -> st { fns_ = fns_ st $*$ (cFuncDecl n a <> semi) })

mkFn :: Name -> [Name] -> CG a -> CG a
mkFn n as body = do
  st <- get
  put (st { decls_ = mempty, stmts_ = mempty })
  r <- body
  st' <- get
  let func = vcat [
        cFuncHeader n as <+> lbrace,
        nest 2 (decls_ st' $*$ stmts_ st'),
        rbrace]
  put (st { fns_ = fns_ st' $*$ func })
  pure r

mkDesc :: Name -> Int -> CG ()
mkDesc n@(N v _ _) a =
  toplevel $ cDesc (pp n) v a

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: E ([(Var, (Known, Name))], CG ()) -> E V -> E V
fixEnv a inner = do
  st <- get
  let ((vs, act), st') = runExp (withEnv env' a) st
      gl = gl_ st
      env = env_ st
      env_i = M.fromList [ (i, En { cv_ = Var, kn_ = kn, vgl_ = gl, n_ = n }) | (i, (kn, n)) <- vs ]
      env' = fmap (\en -> lazyEn $ en { kn_ = sameEnv (kn_ en) }) env_i <> env
      env'' =  env_i <> env
  put (st `oldNew` st')
  (k, act') <- withEnv env'' inner
  pure (k, act >> act')

-- Handles a *constant* binding (constructor def)
conBinding :: Var -> Name -> Desc E -> E V -> E V
conBinding i nm d@(Desc _ a _ _) act = do
  st <- bindEnvWith const i (Con, KnownValue (VDesc d), nm) <$> get
  local (const st) $ do
    (kn, gen) <- act
    let
      gen'
        | a == 0 =
          toplevel
            (hsep ["const", "ling_desc", (pp nm <> "[]"), equals] <+>
             (cArray [cCall "LING_MK_DESC" [ int a, "NULL", text (show i)]] <> semi))
        | otherwise = do
          let as = fmap (N "arg" "arg") [0..toInteger a - 1]
          mkFnDecl nm a
          mkDesc nm a
          mkFn nm as $
            stmt (cReturn $
                  cCall "ling_new_obj" [pp contextArg, pp nm, cArgArray (pp <$> as)])
    pure (kn, gen' >> gen)

-- Match monad.
type MM a = State St a
type Match = (Mode, CG ())
type M v = v -> Code -> MM Match -- Matcher for v running Code on failure.

-- Matched is where we handle mangling and adding to the env.
matched :: Span -> Var -> (Known, Name) -> MM Match
matched s i (kn, nm) = do
  sp <- matchSP
  let collide _ _ = spanError s ("Duplicate pattern bindings for variable "++toString i) sp
  modify $ bindEnvWith collide i (Var, kn, nm)
  pure (AlwaysSucceeds, pure ())

alwaysSucceed :: MM Match
alwaysSucceed = pure (AlwaysSucceeds, stmt "// Always succeeds")

alwaysFail :: Code -> MM Match
alwaysFail sfail = pure (AlwaysFails, stmt sfail)

mayFail :: CG () -> MM Match
mayFail f = pure (MayFail, f)

matchSP :: MM SpanPos
matchSP = gets sp_

matchError :: HasCallStack => Span -> String -> MM a
matchError s msg = spanError s msg <$> matchSP

funName :: (HasCallStack, MonadState St m) => Span -> Var -> m Name
funName s c = gets (n_ . lookupEnv s c)

unreachable :: CG Code
unreachable = pure "line_unreachable()"

-- Inject match into evaluation
-- Matches are formatted (for now) as:
--   attempt match or goto fail1
--   match body;
--   goto success0;
-- fail1: // next match
--   ...
-- success0:
withMatch :: HasCallStack => M b -> E V -> Label -> b -> E (Mode, Known, CG Code)
withMatch m suc lsuc b = do
  lfail <- newLabel
  st <- get
  let env = env_ st
      cenv = M.filter (\en -> cv_ en == Con) env
      sfail = cGoto "fail" lfail
      ((mode, matcher), st') = runState (m b sfail) (st{ env_ = cenv })
      env' = env_ st'
      st_match = (st `oldNew` st'){ env_ = env' <> env }
  put st_match
  case mode of
    AlwaysFails ->
      pure (mode, Bottom, stmt (cLabel "fail" lfail) >> unreachable)
    _ -> do
      (kn, rhs) <- suc
      pure (mode, kn, do
        matcher
        c <- rhs
        stmt (cGoto "succ" lsuc)
        when (mode /= AlwaysSucceeds) $
          stmt (cLabel "fail" lfail)
        pure c)

-- Assumes length ps == length vs
matches :: HasCallStack => [Pat] -> M [(Known, Name)]
matches [p] [k] = match p k
matches ps ks =
  traceM ps " match " (map fst ks) $ matches' ps ks

matches' :: HasCallStack => [Pat] -> M [(Known, Name)]
matches' [] _ _ = error "Empty pats; shouldn't happen!"
matches' ps kns _ | length ps /= length kns =
  matchError (span ps) ("Pat len mismatch "++showsPp ps++" and "++show (length kns))
matches' ps kns sfail = do
  fs <- zipWithA (\p kn -> match' p kn sfail) ps kns
  pure (foldr (meet . fst) AlwaysSucceeds fs, traverse_ snd fs)

-- Match Pat with name in Env and yield fresh Env.
-- Falls through on match, "break" on match fail.
match :: HasCallStack => Pat -> M (Known, Name)
match p (kn, nm) = traceM p " matches " kn $ match' p (kn, nm)

match' :: HasCallStack => Pat -> M (Known, Name)
match' (Paren _ p) kn sfail = match' p kn sfail
match' (Wild _) _ _ = alwaysSucceed
match' (Id s _ Var var) kn _ = matched s var kn
match' (Id _ _ Con con) (KnownValue (VCon0 con'), _) _
  | con == con' = alwaysSucceed
match' (Id _ _ Con   _) (KnownValue _, _) sfail = alwaysFail sfail
match' (Id s _ Con con) (_, nm) sfail = do
  cname <- funName s con
  mayFail $ stmt $ cIf (hsep [pp cname, "!=", gDesc(pp nm)]) sfail
match' (Const _ c) (KnownValue (VConst c'), _) _
  | c == c' = alwaysSucceed
match' (Const _ _) (KnownValue _, _) sfail = alwaysFail sfail
match' c@(Const _ (EString _)) (_, nm) sfail = mayFail $
  stmt $ cIf (hsep [cCall "strcmp" [pp c, gString $ pp nm], "!=", "0"]) sfail
match' c@(Const _ (EInt _)) (_, nm) sfail = mayFail $ do
  stmt $ cIf (hsep [pp c, "!=", gInt $ pp nm]) sfail
match' c@(Const _ (EFloat _)) (_, nm) sfail = mayFail $ do
  stmt $ cIf (hsep [pp c, "!=", gFloat $ pp nm]) sfail
match' c@(Const _ (EChar _)) (_, nm) sfail = mayFail $ do
  stmt $ cIf (hsep [pp c, "!=", gChar $ pp nm]) sfail
match' (Block (_, ds)) (_, name) sfail = do
  ms <- traverse (\d -> matchField name d sfail) ds
  pure (foldr (meet . fst) AlwaysSucceeds ms, traverse_ snd ms)
match' (App _ (Id s _ Con con) as) (kn, nm) cfail = matchCon s con as (kn, nm) cfail
match' p _ _ = matchError (span p) ("Unrecognized pattern "++showPp p)

matchCon :: HasCallStack => Span -> Var -> [Pat] -> M (Known, Name)
matchCon s con ps (_, nm) sfail = do
  ns <- traverse (withName . snd . patVar) ps
  let kns = (Unknown,) <$> ns
      ns' = zip [0..] ns
  ms <- zipWithA (\p kn -> match' p kn sfail) ps kns
  let kn = foldr (meet . fst) MayFail ms
  test <- if con == "()" then
      pure $ cCall "ling_is_tuple" [int (length ps), pp nm]
    else
      (\cname -> cCall "ling_desc_is" [pp cname, pp nm]) <$> funName s con
  pure (kn, do
    traverse_ (decl . cObjDecl) ns
    stmt $ cIf ("!" <> test) sfail
    traverse_ (\(n, pnm) -> stmt (cObjAssign pnm (cCall "ling_field" [pp nm, int n]))) ns'
    traverse_ snd ms)

matchField :: HasCallStack => Name -> M (Span, Def)
matchField _ (_, Def (Id _ _ Var _) (Wild _)) _ = alwaysSucceed
matchField nm (_, Def (Id _ _ Var fn) p) sfail = do
  fnm <- withName $ snd $ patVar p
  (m, act) <- match' p (Unknown, fnm) sfail
  pure (m, do
    decl (cObjDecl fnm)
    stmt $ hsep [ pp fnm, "=", pp nm <> "." <> pp fn <> semi ]
    act)
matchField _ (s, p) _ = matchError s ("Illegal struct pattern "++showPp p)

data BestVarKind = Wildcard | New | Orig deriving (Eq, Ord, Show)

-- Return best var to drive name for pattern.
patVar :: Pat -> (BestVarKind, Var)
patVar (Paren _ p) = patVar p
patVar (Wild _) = (Wildcard, "wpat")
patVar (Id _ _ Var var) = (Orig, var)
patVar _ = (New, "pat")

bestPatVar :: (BestVarKind, Var) -> (BestVarKind, Var) -> (BestVarKind, Var)
bestPatVar r1@(k1, _) r2@(k2, _)
  | k1 >= k2 = r1
  | otherwise = r2

clauseVars :: [Clause] -> [Var]
clauseVars [] = error "Empty clause"
clauseVars cs = snd <$> foldr1 (zipWith bestPatVar) (fmap (fmap patVar . fst) cs)

-- cont helpers.
-- This one assumes that e yields an Exp directly and handles other conts.
cont :: Cont -> CG Code -> CG Code
cont Exp e = e
cont (Bind nm) e = do
  c <- e
  stmt (cObjAssign nm c)
  pure (pp nm)
cont Return e = do
  c <- e
  stmt (cReturn c)
  unreachable

-- Force cont passed to inner to be bound
contBind :: Var -> EV -> EV
contBind v a Exp = do
  t <- withName v
  (kn, act) <- a (Bind t)
  pure (kn, decl (cObjDecl t) >> act)
contBind _ a k = a k

-- Helpers for apply
isKnownValue :: Known -> Bool
isKnownValue (KnownValue _) = True
isKnownValue _ = False

-- Note that we've stashed a serialization of the name in the Desc v.
knownVarArity :: Known -> Maybe (Var, Arity)
knownVarArity (KnownDesc _ (Desc v a _ _)) = Just (v, a)
knownVarArity (KnownValue (VDesc (Desc v a _ _))) = Just (v, a)
knownVarArity _ = Nothing

-- Apply value to args.
apply :: HasCallStack => Span -> EV -> [EV] -> EV
apply s a as k = do
  (kn, f) <- a Exp
  kas <- traverse ($ Exp) as
  apply' s kn f kas k

apply' :: HasCallStack => Span -> Known -> CG Code -> [V] -> EV
apply' s kn f kas k =
  case knownVarArity kn of
    Nothing -> pure (Unknown, cont k $ applyUnknown f kas)
    Just (nm, a) -> do
      applyKnown s nm a kn f kas k

args :: [V] -> CG [Code]
args = traverse snd

applyKnown :: HasCallStack => Span -> Var -> Arity -> Known -> CG Code -> [V] -> EV
applyKnown s nm a kn f as k
  | a > len = do
    sp <- spanPrefix s <$> expSP
    pure (Unknown, cont k $ do
      cs <- args as
      pApKnown sp nm kn f cs)
  | a < len = do
    let (bs, cs) = splitAt a as
    (kn', f') <- applyKnown s nm a kn f bs Exp
    apply' s kn' f' cs k
  where len = length as
applyKnown s _ _ (KnownValue (VDesc (Desc i _ Fold (CloFun f)))) _ as k
  | all (isKnownValue . fst) as = do
    sp <- spanPrefix s <$> expSP
    traceCAp sp " constant fold " i $ do -- Constant fold!
      va <- f [ v | (KnownValue v, _) <- as]
      act <- valueToCode s va k
      pure (KnownValue va, act)
applyKnown s nm _ kn f as k = do
  sp <- spanPrefix s <$> expSP
  pure (Unknown, cont k $ do
    cs <- args as
    applyKnown' sp nm kn f cs)

applyKnown' :: HasCallStack =>
  String -> Var -> Known -> CG Code -> [Code] -> CG Code
applyKnown' s nm (KnownValue (VDesc _)) _ as = traceCAp s " known VDesc " nm $ do
  pure $ cCall (funcOf nm) (pp contextArg : as)
applyKnown' s nm (KnownDesc SameEnv _) _ as = traceCAp s " known SameEnv " nm $ do
  pure $ cCall (funcOf nm) (pp contextArg : pp envArg : as)
applyKnown' s nm (KnownDesc _ _) f as = traceCAp s " known DiffEnv " nm $ do
  c <- f
  pure $ cCall (funcOf nm) (pp contextArg : cCall "ling_field" [c, int 1] : as)
applyKnown' s _ kn _ _ = error (s++" applyKnown non-descy " ++ showPp kn)

pApKnown :: HasCallStack =>
  String -> Var -> Known -> CG Code -> [Code] -> CG Code
pApKnown s nm (KnownValue (VDesc _)) _ cs = traceCAp s " pknown VDesc " nm $ do
  pure $ cCall "ling_pap" [
    pp contextArg, pp nm, int (length cs), cArgArray cs]
pApKnown s nm (KnownDesc SameEnv _) _ cs = traceCAp s " pKnown SameEnv " nm $ do
  pure $ cCall "ling_pap" [
    pp contextArg, pp nm, int (length cs + 1), pp envArg, cArgArray cs]
pApKnown s nm (KnownDesc _ _) f cs = traceCAp s " pKnown DiffEnv " nm $ do
  c <- f
  pure $ cCall "ling_pap" [
    pp contextArg, pp nm, int (length cs + 1),
    cCall "ling_field" [c, int 0], cArgArray cs]
pApKnown s _ kn _ _ = error (s ++ "non-closure pApKnown "++showPp kn)

constToCode :: Constant -> Code
constToCode (EInt i) = cCall "LING_INT" [integer i]
constToCode (EFloat f) = cCall "LING_FLOAT" [double f]
constToCode c = cCall "LING_STR" [pp c]

valueToCode :: HasCallStack => Span -> Value -> Cont -> E (CG Code)
valueToCode _ (VConst c) k = pure $ cont k $ pure $ constToCode c
valueToCode _ (VDesc (Desc c _ _ _)) k = do
  pure $ cont k (pure $ cCall "LING_DESC" [pp c])
valueToCode s (VObj (Desc c _ _ _) vs) k = do
  acts <- traverse (\v -> valueToCode s v Exp) vs
  nm <- withName c
  pure $ cont k $ do
    cs <- sequenceA acts
    toplevel $ hang
      (hsep ["static", "const", "ling_obj", pp nm <> "[]", equals]) 2
      (cArray (cCall "LING_DESC" [pp c] : cs) <> semi)
    pure $ cCall "LING_REF" [pp nm]
valueToCode s v _ = expError s ("Can't convert value to code "++showPp v)

-- Evaluate function and args
applyUnknown :: HasCallStack => CG Code -> [V] -> CG Code
applyUnknown f as = do
  vs <- args as
  v <- f
  pure $ cCall "ling_apply" [pp contextArg, v, int (length as), cArgArray vs]

-- Initiates a wrapping switch expression that either returns or binds the
-- disjunct value.  If we're not returning or binding, we'll need to declare
-- a variable to contain the bound value.
appDisjs :: HasCallStack => Span -> [Clause] -> [(Known, Name)] -> EV
appDisjs s ds kns Exp = contBind "case_val" (appDisjs s ds kns) Exp
appDisjs s ds kns k = do
  lsucc <- newLabel
  let clause ((ps, e):cs) (m, kn, act) = do
        (modec, knc, actc) <- withMatch (matches ps) (eval e k) lsucc kns
        case modec of
          AlwaysSucceeds -> pure (AlwaysSucceeds, kn <> knc, act >> actc)
          AlwaysFails -> clause cs (m, kn, act)
          _ -> clause cs (modec <> m, kn <> knc, act >> actc)
      clause [] (m, kn, act) = do
        sloc <- spanPrefix s <$> expSP
        pure $
          (m, kn, do
            r <- act
            stmt $ cMatchError sloc
            pure r)
  (_, kn, act) <- clause ds (mempty, mempty, unreachable)
  pure (kn, do
    r <- act
    stmt (cLabel "succ" lsucc)
    pure r)

eval :: HasCallStack => Exp -> EV
eval (Id s _ _ i) k = do
  en <- findEnv s i
  let gen (En{ kn_ = KnownValue (VDesc _)}) =
        pure . aDesc . pp . n_ $ en
      gen _ = pure . pp . n_ $ en
  pure (kn_ en, cont k $ gen en)
eval (App s e es) k = apply s (eval e) (eval <$> es) k
eval (Const s c) k = do
  act <- valueToCode s (VConst c) k
  pure (KnownValue $ VConst c, act)
eval e@(Fn s (_, ds)) k = withDiffEnv $ do
  name <- withName "anon_fn"
  (a, cs) <- mkRhs s ds <$> expSP
  info@(pack, _, _) <- closed (fv e)
  (kn, act) <- vClo s name a info cs k
  pure (kn, vCloDecl name a info >> pack >> act)
eval (Tuple s es) k = do
  es' <- traverse (\e -> eval e Exp) es
  let
    a = length es'
    d = conDesc "()" a
    kn | all (isKnownValue . fst) es' =
         KnownValue (VObj d [ v | (KnownValue v, _) <- es' ])
       | null es = KnownValue (VDesc d)
       | otherwise = KnownDesc DiffEnv d
  case kn of
    KnownValue v ->
      (kn,) <$> valueToCode s v k
    _ -> pure (kn, do
      vs <- args es'
      cont k $ pure $
        cCall "ling_tuple" [pp contextArg, int a, cArgArray vs])
eval (Case s e (_,es)) k = do
  bv <- withName "case_disc"
  (ekn, e') <- eval e (Bind bv)
  sp <- expSP
  (kn, m) <- locally $ appDisjs s (map (toDisj sp) es) [(ekn, bv)] k
  pure (kn, stmt (cObjDecl bv) >> e' >> m)
eval (Block b) k = locally (evDefs b k)
eval e _ = expError (span e) ("eval: Unhandled expression\n  "++showPp e++"\n  "++show e)

evDefs :: Defs -> EV
evDefs b k =
  case groupDefs b of
    Left es -> do
      sp <- expSP
      error $ unlines $ (\(s, err) -> spanPrefix s sp <> toString err) <$> es
    Right ds -> evGroups ds k

evGroups :: HasCallStack => [DefGroup] -> EV
evGroups [] k = do
  let v = VStruct mempty
  pure (KnownValue v, cont k $ error "TODO evGroups empty record")
evGroups [Record m] k = do
  ms <- locally $ traverse (\e -> eval e Exp) m
  pure (Unknown, cont k $
    ms `seq` error "TODO evGroups record")
evGroups [D (BindExp e)] k =
  locally $ eval e k
evGroups (D (Data _ (_,ds)) : ts) k =
  foldr addCon (evGroups ts k) ds
evGroups ts Exp =
  contBind "block_val" (evGroups ts) Exp
evGroups (Fns fs:ts) k =
  withDiffEnv $ fixEnv (evFns fs) (evGroups ts k)
evGroups (D (BindExp e) : ts) k = do
  (_, e') <- locally $ eval e Exp
  (kn, r) <- evGroups ts k
  pure (kn, e' >> r)
evGroups (D (Def p e) : ts) k = do
  sloc <- spanPrefix (span p) <$> expSP
  let v = snd $ patVar p
      matchErr = cMatchError sloc
  n <- withName v
  (ekn, e') <- locally $ eval e (Bind n)
  lsucc <- newLabel
  (m, kn, act) <- withMatch (match p) (evGroups ts k) lsucc (ekn, n)
  pure (kn, do
    decl (cObjDecl n)
    e'
    r <- act
    case m of
      AlwaysSucceeds -> stmt (cLabel "succ" lsucc)
      _ -> stmt matchErr >> stmt (cLabel "succ" lsucc)
    pure r)
evGroups (g : _) _ = error ("Unexpected group "++showPp g)

-- Bind closures for fs, assumes we're already in a fixed-point env.
evFns :: HasCallStack => [GroupFun] -> E ([(Var, (Known, Name))], CG ())
evFns fs = do
  named <- traverse (\(s, v, a, cs) -> (, s, v, a, cs) <$> withName v) fs
  ci@(mkEnv, _, _) <- closed (fv (Fns fs))
  let clo (n, s, v, a, cs) = do
        n' <- if hasEnv ci then withName (v<>"_IMP") else pure n
        (\(kn,act) -> (n',a,kn,act)) <$> vClo s n' a ci cs (Bind n)
  ns <- traverse clo named
  let r = zipWith (\(n, _, v, _, _) (_, _, kn, _) -> (v, (kn, n))) named ns
  pure (r, do
    traverse_ (\(n', a, _, _) -> vCloDecl n' a ci) ns
    traverse_ (\(_, _, _, act) -> act) ns
    traverse_ (\(n, _, _, _, _) -> when (hasEnv ci) $ decl $ cObjDecl n) named
    mkEnv)

-- Convert local env into closure env.  Returns:
-- Statement to pack the closure into closure argument
-- Name of the resulting closure argument
-- Action to bracket and unpack the env in the callee
-- TODO: handle degenerate envs.  Maybe that's actually
-- a program transformation to hoist them.
-- TODO: We handle free peer functions badly and require
-- full closures to live in the env.
type CloInfo = (CG (), Maybe Name, E V -> E V)

closed :: Set Var -> E CloInfo
closed vs = do
  env <- gets env_
  earg <- withClone envArg
  let
    -- Figure out what vars we're closing over.  Include all constructors
    -- so that matching can resolve them (they're flagged as global since
    -- they have no fvs)
    env' = M.filterWithKey (\k en -> cv_ en == Con || k `S.member` vs) env
    inClo = M.filter (\en -> vgl_ en /= Global) env'
    cloNames = n_ <$> M.elems inClo
    declEnv = do
      decl $ hang (hsep ["ling_obj", ("*"<>pp earg), equals]) 2 $
        cCall "ling_mk_env" [pp contextArg, int (length inClo)] <> semi
      stmt $
        cCall "ling_fill_env" [
          int (length inClo), pp earg,
          "(ling_obj[])" <> (cArray $ pp <$> cloNames)] <> semi
    unpackEnv =
      [ cObjDeclAssign n (cCall "ling_field" [pp envArg, int i]) |
        (n, i) <- zip cloNames [0..]]
    wrapper :: E V -> E V
    wrapper act = withEnv env' $ do
      (kn, body) <- act
      pure $
        (kn, do
          traverse_ decl unpackEnv
          traverse_ (\name -> stmt ("(void)" <> pp name <> semi)) cloNames
          body)
  (\(~(a,b,c)) -> (a,b,c)) <$>  -- NOTE: required for <<loop>> prevention!
    if null cloNames then
      pure (pure (), Nothing, withEnv env')
    else
      pure (declEnv, Just earg, wrapper)

hasEnv :: CloInfo -> Bool
hasEnv (_, Nothing, _) = False
hasEnv _ = True

-- Add the global declarations required to build a closure.
-- We need to do this for all functions in a group before defining
-- any function in the group.  For this reason we generate code eagerly.
vCloDecl :: HasCallStack => Name -> Arity -> CloInfo -> CG ()
vCloDecl f n ci = do
  let n' | hasEnv ci = n + 1
         | otherwise = n
  mkFnDecl f n'
  mkDesc f n'

noFold :: CloFun E
noFold = CloFun $ \_ -> error "Can't fold fns"

vClo :: HasCallStack => Span -> Name -> Arity -> CloInfo -> [Clause] -> EV
vClo s f n ci@(_, envName, unpackAndBind) cs k = locally $ do
  let
    d = Desc (toVar f) n NoFold noFold
    kn | hasEnv ci = KnownDesc DiffEnv $ d
       | otherwise = KnownValue $ VDesc $ d
  (kn,) <$> do
    as <- traverse withName (clauseVars cs)
    (_, body) <- unpackAndBind $ appDisjs s cs ((Unknown,) <$> as) Return
    let as' | hasEnv ci = envArg : as
            | otherwise = as
        func = mkFn f as' body
        closure en k' = cont k' $ do
          pure $ cCall "ling_pap" [pp contextArg, pp f, int 1, cArgArray [cCall "LING_REF" [pp en]]]
    case (envName, k) of
      (Nothing, Bind f')
        | f == f' -> pure (func >> pure (pp f))
        | otherwise -> pure $ do
            func
            decl (cObjDecl f')
            stmt (cObjAssign f' (pp f))
            pure (pp f')
      (Nothing, _) -> pure (func >> (cont k $ pure $ pp f))
      (Just en, _) -> snd <$> contBind "closure" (\k' -> pure $ (kn, func >> closure en k')) k

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> E V -> E V
addCon (_, BindExp (Asc _ (Id _ _ Con c) t)) k = do
  nm <- withName c
  conBinding c nm (conDesc (toVar nm) (typeArity t)) k
addCon (s, d) _ = expError s ("addCon: not a constructor def "++showPp d)

compileTop :: HasCallStack => (SpanPos, Defs) -> Code
compileTop (sp, ds) = do
  let st0 = St { sp_ = sp, tn_ = mempty, nlbl_ = 0,
                 gl_ = Global, env_ = mempty }
      in0 = Inner { fns_ = mempty, decls_ = mempty, stmts_ = mempty }
      ((_, act), _) = (`runExp` st0) $ do
        expand env0
        _ <- withName "initialize"
        evDefs ds Return
      (_, inn) = runState act in0
  vcat [
      "#include \"lingrts.h\"" $*$
      decls_ inn $*$
      fns_ inn,
      "",
      hsep ["ling_obj", cCall "initialize" ["ling_context *" <> pp contextArg], lbrace],
      nest 2 $ stmts_ inn,
      rbrace
    ]

expand :: HasCallStack => Map Var Value -> E ()
expand e = do
  let es = M.toList e
      collide (En { n_ = N v _ _ }) _ =
        error ("Name collision in initial environment on "++show v)
      oneBinding (i, v) = do
        n <- withName i
        modify $ bindEnvWith collide i (Var, KnownValue v, n)
  traverse_ oneBinding es
