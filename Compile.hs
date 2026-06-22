{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase, TypeFamilies #-}
module Compile(compileTop) where
import AST
import Names
import Parse(SpanPos, spanError, spanPrefix)
import Primitive
import SemUtil
import Value

import Control.Monad
import Control.Monad.State
import Data.ByteString(ByteString)
import Data.ByteString.UTF8(toString)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Debug.Trace(trace)
import GHC.Stack(HasCallStack)
import Text.PrettyPrint hiding ((<>), Mode)
import Prelude hiding (span)

{-
## Variable conventions

We preserve top-level variable names where possible.  We use a single underscore for C keywords.
Internal variable names are numerically mangled.  Primes are _P.

Operator mangling:
_0p_[mangled characters]
What's the mangled character mapping?  Alphabetic, then fall back to _decimal?

-}

trace_match :: Bool
trace_match = False

trace_app_compile :: Bool
trace_app_compile = False || trace_app

trace_app :: Bool
trace_app = False

traceM :: (PP a, PP c) => a -> String -> c -> b -> b
traceM a s c b | trace_match = trace (showPp a++s++showPp c) b
traceM _ _ _ e = e

traceCAp :: Span -> String -> ByteString -> E b -> E b
traceCAp s m nm b | trace_app_compile = do
  sp <- gets sp_
  trace (spanPrefix s sp++m++toString nm) b
traceCAp _ _ _  b = b

-- C stuff
cCall :: Code -> [Code] -> Code
cCall f xs = f <> parens (fsep $ punctuate comma xs)

cObjDeclAssign :: Name -> Code -> Code
cObjDeclAssign v code = hang ("ling_obj" <+> pp v <+> equals) 2 (code <> semi)

cObjDecl :: Name -> Code
cObjDecl v = "ling_obj" <+> (pp v <> semi)

cObjAssign :: Name -> Code -> Code
cObjAssign v code = hang (pp v <+> equals) 2 (code <> semi)

cFuncDecl :: Name -> Int -> Code
cFuncDecl n a =
  cCall ("ling_obj" <+> funcOf n) ("ling_context" : replicate a "ling_obj")

cFuncHeader :: Name -> [Name] -> Code
cFuncHeader n as = do
  let arg a = "ling_obj" <+> pp a
      ps = ("ling_context" <+> ("*" <> pp contextArg)) : fmap arg as
  cCall ("ling_obj" <+> funcOf n) ps

cReturn :: Code -> Code
cReturn c = sep ["return", (c <> ";")]

cLabel :: Doc -> Label -> Code
cLabel s l = s <> integer l <> ":"

cGoto :: Doc -> Label -> Code
cGoto s l = "goto" <+> (s <> integer l <> ";")

-- One-sided if statement
cIf :: Code -> Code -> Code
cIf p t = sep [ hsep [ "if", parens p, lbrace ], nest 2 t, rbrace ]

-- Naming and Environments

data Entry = En {
  kn_ :: Known,
  vgl_ :: GL,
  n_ :: Name}
    deriving (Eq, Show)
type Env = Map Var Entry

-- Closures, Descriptors, and Values
type Value = Val E
type Known = Knw E
type Code = Doc

-- Utilities not worth an import
fromMaybe :: a -> Maybe a -> a
fromMaybe d = maybe d id

-- Evaluation (environment) monads
data Cont = Bind Name | Return | Exp deriving (Eq, Show)
type Label = Integer
data St = St {
  -- Never changes
  sp_ :: SpanPos,
  -- Actually persistent state (after locally)
  tn_ :: TakenNames,
  fns_ :: Code,
  nlbl_ :: !Label,
  -- Function-persistent state
  decls_ :: Code,
  stmts_ :: Code,
  -- Transient top-down state reset after `local`
  gl_ :: GL,
  env_ :: Env}
newtype E a = E (State St a)
  deriving (Functor, Applicative, Monad, MonadState St)
type V = (Known, E Code) -- Result is for point of use
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
runExp (E r) = runState r

instance MonadEval E where
  type ClosureState E = Name -- Of local containing env object
  withClo = error "We don't withClo, callee unpacks"

withName :: MonadState St m => Var -> m Name
withName i = do
  st <- get
  let gl = gl_ st
      tn = tn_ st
      n = mangle i gl tn
      tn' = takeName n tn
  put (st{ tn_ = tn' })
  pure n

bindEnvWith ::
  (Entry -> Entry -> Entry) -> Var -> (Known, Name) -> St -> St
bindEnvWith c i (kn, nm) st =
  st{ env_ = M.insertWith c i (En kn (gl_ st) nm) (env_ st) }

lookupEnv :: HasCallStack => Span -> Var -> St -> Entry
lookupEnv s i (St {env_ = env, sp_ = sp}) =
  fromMaybe (spanError s ("Unbound variable "++toString i) sp) $
    M.lookup i env

-- Make a local replica of a name, mostly for the builtin names.
withClone :: Name -> E Name
withClone (N o m _) = do
  st <- get
  let r = untaken o m (gl_ st) (tn_ st)
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
decl :: MonadState St m => Code -> m ()
decl c = modify (\st -> st { decls_ = decls_ st $$ c })

-- Add a name declaration to the current function.
nameDecl :: MonadState St m => Var -> m Name
nameDecl i = do
  name <- withName i
  decl $ cObjDecl name
  pure name

-- Add a statement to the current block
stmt :: MonadState St m => Code -> m ()
stmt c = modify (\st -> st { stmts_ = stmts_ st $$ c })

newLabel :: MonadState St m => m Label
newLabel = state $ \st -> do
  let lbl = nlbl_ st
  (lbl, st { nlbl_ = lbl + 1 })

toplevel :: Code -> E ()
toplevel c = modify (\st -> st { fns_ = fns_ st $$ "" $$ c })

mkFnDecl :: Name -> Int -> E ()
mkFnDecl n a =
  modify (\st -> st { fns_ = fns_ st $$ "" $$ (cFuncDecl n a <> ";") })

mkFn :: Name -> [Name] -> E a -> E a
mkFn n as body = do
  st <- get
  put (st { decls_ = mempty, stmts_ = mempty })
  r <- body
  st' <- get
  let func = vcat [
        cFuncHeader n as <+> lbrace,
        nest 2 (decls_ st' $$ "" $$ stmts_ st'),
        rbrace]
  put (st { tn_ = tn_ st', fns_ = fns_ st' $$ "" $$ func })
  pure r

mkDesc :: Name -> Int -> E ()
mkDesc n@(N v _ _) a =
  toplevel $ sep [
    hsep ["const", "ling_desc", pp n, "=", lbrace],
    nest 2 $ fsep ["&"<>pp n, int a, "&"<>funcOf n, text (show v)],
    rbrace]

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: E ([(Var, (Known, Name))], E ()) -> E V -> E V
fixEnv a inner = do
  st <- get
  let ((vs, act), st'') = runExp a st'
      gl = gl_ st
      env = env_ st
      env_i = M.fromList [ (i, En { kn_ = kn, vgl_ = gl, n_ = n }) | (i, (kn, n)) <- vs ]
      env' = fmap (\en -> en { kn_ = sameEnv (kn_ en) }) env_i <> env
      env'' =  env_i <> env
      st' = st{ env_ = env' }
  put (st `oldNew` st'')
  (k, act') <- withEnv env'' inner
  pure (k, act >> act')

-- Handles a *constant* binding (constructor def)
conBinding :: Var -> Desc E -> E a -> E a
conBinding i d@(Desc _ a _ _) act = do
  nm <- withName i
  st <- bindEnvWith const i (KnownValue (VDesc d), nm) <$> get
  local (const st) $ do
    let as = fmap (N "arg" "arg") [0..toInteger a - 1]
    mkFnDecl nm a
    mkDesc nm a
    mkFn nm as $ do
      stmt (sep ["return", cCall "ling_new_obj" (pp <$> contextArg : nm : as) <> ";"])
    act

-- Match monad.
type MM a = State St a
type Match = (Mode, MM ())
type M v = v -> Code -> MM Match -- Matcher for v running Code on failure.

-- Matched is where we handle mangling and adding to the env.
matched :: Span -> Var -> (Known, Name) -> MM Match
matched s i (kn, nm) = do
  sp <- matchSP
  let collide _ _ = spanError s ("Duplicate pattern bindings for variable "++toString i) sp
  modify $ bindEnvWith collide i (kn, nm)
  pure (AlwaysSucceeds, pure ())

alwaysSucceed :: MM Match
alwaysSucceed = pure (AlwaysSucceeds, stmt "// Always succeeds")

alwaysFail :: Code -> MM Match
alwaysFail sfail = pure (AlwaysFails, stmt sfail)

mayFail :: MM () -> MM Match
mayFail f = pure (MayFail, f)

matchSP :: MM SpanPos
matchSP = gets sp_

matchError :: HasCallStack => Span -> String -> MM a
matchError s msg = spanError s msg <$> matchSP

funName :: MonadState St m => Span -> Var -> m Name
funName s c = gets (n_ . lookupEnv s c)

unreachable :: E Code
unreachable = pure "line_unreachable()"

-- Inject match into evaluation
-- Matches are formatted (for now) as:
--   attempt match or goto fail1
--   match body;
--   goto success0;
-- fail1: // next match
--   ...
-- success0:
withMatch :: HasCallStack => M b -> E V -> Label -> b -> E (Mode, Known, E Code)
withMatch m suc lsuc b = do
  lfail <- newLabel
  st <- get
  let env = env_ st
      sfail = cGoto "fail" lfail
      ((mode, matcher), st') = runState (m b sfail) (st{ env_ = mempty })
      env' = env_ st'
      st_match = (st `oldNew` st'){ env_ = env' <> env }
  put st_match
  case mode of
    AlwaysFails ->
      pure (mode, Bottom, stmt (cLabel "fail" lfail) >> unreachable)
    _ -> do
      (kn, rhs) <- suc
      pure (mode, kn, do
        state $ runState matcher
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
  fs :: [(Mode, MM())] <- zipWithM (\p kn -> match' p kn sfail) ps kns
  pure (foldr (meet . fst) AlwaysSucceeds fs, mapM_ snd fs)

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
match' (Id s _ Con con) (_, nm) sfail = mayFail $ do
  cname <- funName s con
  stmt $ cIf (hsep [pp cname, "!=", pp nm]) sfail
match' (Const _ c) (KnownValue (VConst c'), _) _
  | c == c' = alwaysSucceed
match' (Const _ _) (KnownValue _, _) sfail = alwaysFail sfail
match' c@(Const _ (EString _)) (_, nm) sfail = mayFail $
  stmt $ cIf (hsep [cCall "strcmp" [pp c, pp nm], "!=", "0"]) sfail
match' c@(Const _ _) (_, nm) sfail = mayFail $ do
  stmt $ cIf (hsep [pp c, "!=", pp nm]) sfail
match' (Block (_, ds)) (_, name) sfail = do
  ms <- mapM (\d -> matchField name d sfail) ds
  pure (foldr (meet . fst) AlwaysSucceeds ms, mapM_ snd ms)
match' (App _ (Id s _ Con con) as) (kn, nm) cfail = matchCon s con as (kn, nm) cfail
match' p _ _ = matchError (span p) ("Unrecognized pattern "++showPp p)

matchCon :: Span -> Var -> [Pat] -> M (Known, Name)
matchCon s con ps (_, nm) sfail = do
  cname <- funName s con
  ns <- mapM (nameDecl . snd . patVar) ps
  let kns = (Unknown,) <$> ns
      ns' = filter ((/= wildPlaceHolder) . snd) $ zip [0..] ns
  ms <- zipWithM (\p kn -> match' p kn sfail) ps kns
  pure (foldr (meet . fst) MayFail ms, do
    stmt $ cIf ("!" <> cCall "ling_desc_is" [pp cname, pp nm]) sfail
    mapM_ (\(n, pnm) -> stmt (cObjAssign pnm (cCall "ling_field" [pp nm, int n]))) ns'
    mapM_ snd ms)

matchField :: HasCallStack => Name -> M (Span, Def)
matchField _ (_, Def (Id _ _ Var _) (Wild _)) _ = alwaysSucceed
matchField nm (_, Def (Id _ _ Var fn) p) sfail = do
  fnm <- nameDecl $ snd $ patVar p
  stmt $ hsep [ pp fnm, "=", pp nm <> "." <> pp fn <> ";" ]
  match' p (Unknown, fnm) sfail
matchField _ (s, p) _ = matchError s ("Illegal struct pattern "++showPp p)

wildPlaceHolder :: Name
wildPlaceHolder = N "_" "_" (-1)

data BestVarKind = Wildcard | New | Orig deriving (Eq, Ord, Show)

-- Return best var to drive name for pattern.
patVar :: Pat -> (BestVarKind, Var)
patVar (Paren _ p) = patVar p
patVar (Wild _) = (Wildcard, "wild")
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
cont :: Cont -> E Code -> E Code
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
  a (Bind t)
contBind _ a k = a k

-- Helpers for apply
isKnownValue :: Known -> Bool
isKnownValue (KnownValue _) = True
isKnownValue _ = False

knownArity :: Known -> Maybe Arity
knownArity (KnownDesc _ (Desc _ a _ _)) = Just a
knownArity (KnownValue (VDesc (Desc _ a _ _))) = Just a
knownArity _ = Nothing

-- Apply value to args.
apply :: HasCallStack => Span -> EV -> [EV] -> EV
apply s a as k = do
  (kn, f) <- a Exp
  kas <- mapM ($ Exp) as
  apply' s kn f kas k

apply' :: HasCallStack => Span -> Known -> E Code -> [V] -> EV
apply' s kn f kas k =
  case knownArity kn of
    Nothing -> pure (Unknown, cont k $ applyUnknown f kas)
    Just a -> applyKnown s a kn f kas k

args :: [V] -> E [Code]
args = mapM snd

applyKnown :: HasCallStack => Span -> Arity -> Known -> E Code -> [V] -> EV
applyKnown s a kn f as k
  | a > len = do
      cs <- args as
      pure (Unknown, cont k $ pApKnown s kn f cs)
  | a < len = do
    let (bs, cs) = splitAt a as
    (kn', f') <- applyKnown s a kn f bs Exp
    apply' s kn' f' cs k
  where len = length as
applyKnown s _ (KnownValue (VDesc (Desc i _ Fold (CloFun f)))) _ as k
  | all (isKnownValue . fst) as = traceCAp s " constant fold " i $ do -- Constant fold!
    va <- f [ v | (KnownValue v, _) <- as]
    pure (KnownValue va, valueToCode s va k)
applyKnown s _ kn f as k = do
  cs <- args as
  pure (Unknown, cont k $ applyKnown' s kn f cs)

applyKnown' :: HasCallStack =>
  Span -> Known -> E Code -> [Code] -> E Code
applyKnown' s (KnownValue (VDesc (Desc v _ _ _))) _ as = traceCAp s " known VDesc " v $ do
  nm <- funName s v
  pure $ cCall (funcOf nm) (pp contextArg : as)
applyKnown' s (KnownDesc SameEnv (Desc v _ _ _)) _ as = traceCAp s " known SameEnv " v $ do
  nm <- funName s v
  pure $ cCall (funcOf nm) (pp contextArg : pp envArg : as)
applyKnown' s (KnownDesc _ (Desc v _ _ _)) f as = traceCAp s " known DiffEnv " v $ do
  nm <- funName s v
  c <- f
  pure $ cCall (funcOf nm) (pp contextArg : cCall "ling_field" [c, int 0] : as)
applyKnown' s kn _ _ = expError s ("applyKnown non-descy " ++ show kn)

pApKnown :: HasCallStack =>
  Span -> Known -> E Code -> [Code] -> E Code
pApKnown s (KnownValue (VDesc (Desc v _ _ _))) _ cs = traceCAp s " pknown VDesc " v $ do
  nm <- funName s v
  pure $ cCall "ling_pap" ([pp contextArg, pp nm, int (length cs)] <> cs)
pApKnown s (KnownDesc SameEnv (Desc v _ _ _)) _ cs = traceCAp s " pKnown SameEnv " v $ do
  nm <- funName s v
  pure $ cCall "ling_pap" ([pp contextArg, pp nm, int (length cs + 1), pp envArg] <> cs)
pApKnown s (KnownDesc _ (Desc v _ _ _)) f cs = traceCAp s " pKnown DiffEnv " v $ do
  nm <- funName s v
  c <- f
  pure $ cCall "ling_pap" ([
    pp contextArg, pp nm, int (length cs + 1),
    cCall "ling_field" [c, int 0]] <> cs)
pApKnown s kn _ _ = expError s ("non-closure pApKnown "++showPp kn)

valueToCode :: HasCallStack => Span -> Value -> Cont -> E Code
valueToCode _ c@(VConst _) k = cont k $ pure $ pp c
valueToCode s (VDesc (Desc c _ _ _)) k = do
  d <- funName s c
  cont k (pure $ pp d)
valueToCode s (VObj (Desc c _ _ _) vs) k = do
  cs <- mapM (\v -> valueToCode s v Exp) vs
  d <- funName s c
  nm <- withName c
  toplevel $ hang
    (hsep ["static", "const", "ling_obj", pp nm <> "[]", equals]) 2
    (cCall "LING_OBJ" (pp d : cs))
  cont k (pure $ pp nm)
valueToCode s v _ = expError s ("Can't convert value to code "++showPp v)

-- Evaluate function and args
applyUnknown :: HasCallStack => E Code -> [V] -> E Code
applyUnknown f as = do
  vs <- args as
  v <- f
  pure $ cCall "ling_apply" ([pp contextArg, v, int (length as)] <> vs)

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
            stmt (cReturn (cCall "ling_match_error" [text (show sloc)]))
            pure r)
  (_, kn, act) <- clause ds (mempty, mempty, unreachable)
  pure (kn, do
    r <- act
    stmt (cLabel "succ" lsucc)
    pure r)

eval :: HasCallStack => Exp -> EV
eval (Id s _ _ i) k = do
  en <- findEnv s i
  pure (kn_ en, cont k $ pure $ pp $ n_ en)
eval (App s e es) k = apply s (eval e) (eval <$> es) k
eval (Const s c) k =
  pure (KnownValue $ VConst c, valueToCode s (VConst c) k)
eval e@(Fn s (_, ds)) k = withDiffEnv $ do
  name <- withName "anon_fn"
  (a, cs) <- mkRhs s ds <$> expSP
  vCloDecl name a
  info <- closed (fv e)
  vClo s name a info cs k
eval (Tuple s es) k = do
  es' <- mapM (\e -> eval e Exp) es
  let
    a = length es'
    d = cDesc "()" a
    kn | all (isKnownValue . fst) es' =
         KnownValue (VObj d [ v | (KnownValue v, _) <- es' ])
       | null es = KnownValue (VDesc d)
       | otherwise = KnownDesc DiffEnv d
  pure $
    (kn, do
       case kn of
         KnownValue v -> valueToCode s v k
         _ -> do
           vs <- args es'
           cont k $ pure $
             cCall "ling_tuple" (pp contextArg:int a:vs))
eval (Case s e (_,es)) k = do
  bv <- withName "case_disc"
  (ekn, e') <- eval e (Bind bv)
  sp <- expSP
  (kn, m) <- locally $ appDisjs s (map (toDisj sp) es) [(ekn, bv)] k
  pure (kn, e' >> m)
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
evGroups [D (BindExp e)] k = locally $ eval e k
evGroups (D (Data _ (_,ds)) : ts) k = foldr addCon (evGroups ts k) ds
evGroups ts Exp = contBind "block_val" (evGroups ts) Exp
evGroups (Fns fs:ts) k = withDiffEnv $ fixEnv (evFns fs) (evGroups ts k)
evGroups (D (BindExp e) : ts) k = do
  (_, e') <- locally $ eval e Exp
  (kn, r) <- evGroups ts k
  pure (kn, e' >> r)
evGroups (D (Def p e) : ts) k = do
  sloc <- spanPrefix (span p) <$> expSP
  let (_, v) = patVar p
      matchErr = cReturn (cCall "ling_match_error" [text (show sloc)])
  n <- withName v
  (ekn, e') <- locally $ eval e (Bind n)
  lsucc <- newLabel
  (m, kn, act) <- withMatch (match p) (evGroups ts k) lsucc (ekn, n)
  pure (kn, do
    e'
    r <- act
    case (m, k) of
      (AlwaysSucceeds, Return) -> pure ()
      (AlwaysSucceeds, _) -> stmt (cLabel "succ" lsucc)
      (_, Return) -> stmt matchErr
      _ -> stmt matchErr >> stmt (cLabel "succ" lsucc)
    pure r)
evGroups (g : _) _ = error ("Unexpected group "++showPp g)

-- Bind closures for fs, assumes we're already in a fixed-point env.
evFns :: HasCallStack => [GroupFun] -> E ([(Var, (Known, Name))], E ())
evFns fs = do
  ci <- closed (fv (Fns fs))
  let clo (s, v, a, cs) = do
        n <- withName v
        (n, a,) <$> vClo s n a ci cs (Bind n)
  ns <- mapM clo fs
  let r = [ (v, (k, n)) | (n@(N v _ _), _, (k, _)) <- ns ]
  pure (r, do
    mapM_ (\(n, a, _) -> vCloDecl n a) ns
    mapM_ (\(_, _, (_, act)) -> act) ns)

-- Convert local env into closure env.  Returns:
-- Statement to pack the closure into closure argument
-- Name of the resulting closure argument
-- Action to bracket and unpack the env in the callee
-- TODO: handle degenerate envs.  Maybe that's actually
-- a program transformation to hoist them.
-- TODO: We handle free peer functions badly and require
-- full closures to live in the env.
type CloInfo = (Code, Maybe Name, E V -> E V)
closed :: Set Var -> E CloInfo
closed vs = do
  env <- gets env_
  earg <- withClone envArg
  let -- Figure out what vars we're closing over.
    env' = M.filterWithKey (\k _ -> k `S.member` vs) env
    inClo = M.filter (\en -> vgl_ en /= Global) env'
    cloNames = n_ <$> M.elems inClo
    mkEnv = cCall "ling_tuple" (pp contextArg : int (length inClo) : (pp <$> cloNames))
    declEnv = cObjDeclAssign earg mkEnv
    unpackEnv =
      [ cObjDeclAssign n (cCall "ling_field" [pp envArg, int i]) |
        (n, i) <- zip cloNames [0..]]
    wrapper :: E V -> E V
    wrapper act = withEnv env' $ do
      (kn, body) <- act
      pure $
        (kn, do
          mapM_ decl unpackEnv
          body)
  if null cloNames then
    pure (mempty, Nothing, withEnv env')
  else
    pure (declEnv, Just earg, wrapper)

-- Add the global declarations required to build a closure.
-- We need to do this for all functions in a group before defining
-- any function in the group.  For this reason we generate code eagerly.
vCloDecl :: HasCallStack => Name -> Arity -> E ()
vCloDecl f n = do
  mkFnDecl f n
  mkDesc f n


vClo :: HasCallStack => Span -> Name -> Arity -> CloInfo -> [Clause] -> EV
vClo s f@(N i _ _) n (pack, envName, unpackAndBind) cs k = do
  as <- mapM withName (clauseVars cs)
  (_, body) <- unpackAndBind $ locally $ appDisjs s cs ((Unknown,) <$> as) Return
  let d = Desc i n NoFold (CloFun $ \_ -> error "Can't fold fns")
      func = mkFn f as body
      closure :: Name -> Cont -> E Code
      closure en k' = cont k' $ do
        stmt pack
        pure $ cCall "ling_pap" [pp contextArg, pp f, int 1, pp en]
  case envName of
    Nothing -> pure (KnownValue $ VDesc d, func >> (cont k $ pure $ pp f))
    Just en -> contBind "closure" (\k' -> pure (KnownDesc DiffEnv d, closure en k')) k

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> E V -> E V
addCon (_, BindExp (Asc _ (Id _ _ Con c) t)) = conBinding c (cDesc c (typeArity t))
addCon (s, d) = const (expError s ("addCon: not a constructor def "++showPp d))

compileTop :: HasCallStack => (SpanPos, Defs) -> Code
compileTop (sp, ds) = do
  let st0 = St { sp_ = sp, tn_ = mempty, fns_ = mempty, nlbl_ = 0,
                 decls_ = mempty, stmts_ = mempty, gl_ = Global, env_ = mempty }
      (_, st) = runExp (expand env0 >> evDefs ds Return) st0
  vcat [
      fns_ st,
      "",
      hsep ["int", cCall "main" ["int argc", "char *argv[]"], lbrace],
      nest 2 (vcat [decls_ st, "", stmts_ st]),
      rbrace
    ]

expand :: HasCallStack => Map Var Value -> E ()
expand e = do
  let es = M.toList e
      collide (En { n_ = N v _ _ }) _ =
        error ("Name collision in initial environment on "++show v)
      oneBinding (i, v) = do
        n <- withName i
        modify $ bindEnvWith collide i (KnownValue v, n)
  mapM_ oneBinding es
