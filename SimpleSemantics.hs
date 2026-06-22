{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase, TypeFamilies #-}
module SimpleSemantics(evalTop) where
import AST
import Parse(SpanPos, spanError, spanPrefix)
import Primitive
import SemUtil
import Value

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.ByteString(ByteString)
import Data.ByteString.UTF8(toString)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Debug.Trace(trace)
import GHC.Stack(HasCallStack)
import qualified Text.PrettyPrint as PP
import Prelude hiding (span)

trace_match :: Bool
trace_match = False

trace_app :: Bool
trace_app = False

traceM :: (IsAST a, PP c) => a -> String -> c -> MM b -> MM b
traceM a s c b | trace_match = do
  p <- spanPrefix (span a) <$> matchSP
  trace (p++showPp a++s++showPp c) b
traceM _ _ _ e = e

traceAp :: Span -> String -> ByteString -> E b -> E b
traceAp s m nm b | trace_app = do
  p <- spanPrefix s <$> expSP
  trace (p++m++toString nm) b
traceAp _ _ _  b = b

-- Values
type Env = Map Var Value
type Value = Val E

-- Utilities not worth an import
fromMaybe :: a -> Maybe a -> a
fromMaybe d = maybe d id

-- Evaluation (environment) monads
type St = (SpanPos, Env)
newtype E a = E (Reader St a)  -- Outer evaluation monad: compilation.
  deriving (Functor, Applicative, Monad, MonadReader St)

runEnv :: E a -> (SpanPos, Env) -> a
runEnv (E r) = runReader r

instance MonadEval E where
  type ClosureState E = Env
  withClo env = local (\(sp, _) -> (sp, env))

bindEnvWith :: (Value -> Value -> Value) -> Var -> Value -> St -> St
bindEnvWith c i v = fmap (M.insertWith c i v)

lookupEnv :: HasCallStack => Span -> Var -> St -> Value
lookupEnv s i (sp, env) =
  fromMaybe (spanError s ("Unbound variable "++toString i++" in "++show (fmap (\(k, v) -> PP.parens (PP.sep [pp k, "->", pp v])) $ M.toList env)) sp) $
    M.lookup i env

-- Convert local env into closure env within act
closed :: Set Var -> E a -> E a
closed vs =
  local (\(sp, env) -> (sp, M.filterWithKey (\k _ -> k `S.member` vs) env))

expSP :: E SpanPos
expSP = asks fst

expError :: HasCallStack => Span -> String -> E a
expError s msg = spanError s msg <$> expSP

findEnv :: HasCallStack => Span -> Var -> E Value
findEnv s i = asks (lookupEnv s i)

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: E [(Var, Value)] -> E Value -> E Value
fixEnv a inner = do
  (sp, env) <- ask
  let vs = runEnv a (sp, env')
      env' = M.fromList vs <> env
  withClo env' inner

-- Handles a *constant* binding (constructor def)
conBinding :: Var -> Value -> E Value -> E Value
conBinding i v r =
  local (bindEnvWith const i v) r

-- Match monad.
type MM a = StateT St Maybe a
type M v a = v -> MM a

matched :: Span -> Var -> M Value ()
matched s i v = do
  sp <- matchSP
  let collide _ _ = spanError s ("Duplicate pattern bindings for variable "++toString i) sp
  modify $ bindEnvWith collide i v

matchFail :: MM a
matchFail = lift Nothing

matchSP :: MM SpanPos
matchSP = gets fst

matchError :: HasCallStack => Span -> String -> MM a
matchError s msg = spanError s msg <$> matchSP

-- Inject match into evaluation
withMatch :: HasCallStack => MM () -> E Value -> E (Maybe Value)
withMatch m t = do
  (sp :: SpanPos, env :: Env) <- ask
  case execStateT m (sp, mempty) of
    Nothing -> pure Nothing
    Just (_, env') -> Just <$> withClo (env' <> env) t

-- Assumes length ps == length vs
matches :: HasCallStack => [Pat] -> M [Value] ()
matches [] _ = error "Empty pats; shouldn't happen!"
matches ps vs = do -- This nonsense is just for tracing.
  s <- get
  case execStateT (matches' ps vs) s of
    Just s' -> traceM ps " match " vs $ put s'
    Nothing -> matchFail

matches' :: HasCallStack => [Pat] -> M [Value] ()
matches' ps vs
  | length ps == length vs = zipWithM_ match' ps vs
  | otherwise =
    matchError (span ps) ("Pat len mismatch "++showsPp ps++" and "++showsPp vs)

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Pat -> M Value ()
match p v = do
  s <- get
  case execStateT (match' p v) s of
    Just s' -> traceM p " matches " v $ put s'
    Nothing -> matchFail

match' :: HasCallStack => Pat -> M Value ()
match' (Paren _ p) v = match p v
match' (Wild _) _ = pure ()
match' (Id s _ Var var) v = matched s var v
match' (Id _ _ Con con) (VCon0 con')
  | con == con' = pure ()
match' (Id _ _ _ _) _ = matchFail
match' (Const _ c) (VConst vc)
  | c == vc = pure ()
match' (Const _ _) _ = matchFail
match' (Block (_, ds)) (VStruct fs) = mapM_ (`matchField` fs) ds
match' (Block _) _ = matchFail
match' p@(App s (Id _ _ Con con) as) v@(VCon cn n rs)
  | n /= length rs =
      matchError s ("Obj ctor arity "++show n++" mismatch "++showPp v)
  | len == n && con == cn = matches' as rs
  | len /= n && con == cn =
      matchError s ("Constructor pat expected arity "++show n ++ ": "++showPp p)
  where len = length as
match' (App _ (Id _ _ _ _) _) _ = matchFail
match' p _ = matchError (span p) ("Unrecognized pattern "++showPp p)

matchField :: HasCallStack => (Span, Def) -> M (Map FieldName Value) ()
matchField (_, Def (Id _ _ Var fn) p) fs = do
  v <- lift (M.lookup fn fs)
  match' p v
matchField (s, p) _ = matchError s ("Illegal struct pattern "++showPp p)

-- Apply value to args.
apply :: HasCallStack => Span -> E Value -> [E Value] -> E Value
apply s f as = do
  vs <- args as
  v <- f
  applyInner s v vs

args :: [E Value] -> E [Value]
args = foldr (\arg act -> do as' <- act; a <- arg; a `seq` pure (a:as')) (pure [])

-- Unpack closures.
applyInner :: HasCallStack => Span -> Value -> [Value] -> E Value
applyInner s (VDesc d) vs = appWithDesc s d mempty (length vs) vs
applyInner s (VPAp d@(Desc nm _ _ _) env as) bs = traceAp s "   Expand pap " nm $ do
  let vs = as <> bs
  appWithDesc s d env (length vs) vs
applyInner s v _ = expError s ("bad closure "++showPp v)

-- Apply function to args (arities given)
appWithDesc :: HasCallStack => Span -> Desc E -> Env -> Arity -> [Value] -> E Value
appWithDesc s d@(Desc nm n _ (CloFun f)) env nv vs
  | n > nv = traceAp s "   PAp " nm $ pure $ VPAp d env vs
  | n == nv = traceAp s "   sat " nm $ withClo env $ f vs
  | otherwise = traceAp s "   split sat " nm $ do
      let (vs', vs'') = splitAt n vs
      f' <- withClo env (f vs')
      applyInner s f' vs''

appDisjs :: HasCallStack => Span -> Var -> [Clause] -> [Value] -> E Value
appDisjs s f [] vs = expError s ("Match failure in "++show f ++ " " ++ showsPp vs)
appDisjs s f ((ps, e): cs) vs = do
  mv <- withMatch (matches ps vs) (eval e)
  case mv of
    Nothing -> appDisjs s f cs vs
    Just v -> pure v

eval :: HasCallStack => Exp -> E Value
eval (Id s _ _ i) = findEnv s i
eval (App s e es) = do
  apply s (eval e) (eval <$> es)
eval (Const _ c) = pure $ VConst c
eval e@(Fn s (_, ds)) = do
  (a, cs) <- mkRhs s ds <$> expSP
  vClo s "<anon>" a (fv e) cs
eval (Tuple _ es) = do
  let d = cDesc "()" (length es)
  VObj d <$> args (fmap eval es)
eval (Case s e (_,es)) = do
  v <- eval e
  sp <- expSP
  appDisjs s "<case>" (map (toDisj sp) es) [v]
eval (Block b) = evDefs b
eval e = expError (span e) ("eval: Unhandled expression\n  "++showPp e++"\n  "++show e)

evDefs :: Defs -> E Value
evDefs b =
  case groupDefs b of
    Left es -> do
      sp <- expSP
      error $ unlines $ (\(s, err) -> spanPrefix s sp <> toString err) <$> es
    Right ds -> evGroups ds

evGroups :: HasCallStack => [DefGroup] -> E Value
evGroups [] = pure $ VStruct mempty
evGroups (Fns fs:ts) = fixEnv (traverse clo fs) (evGroups ts)
  where clo (s, v, n, cs) = (v,) <$> vClo s v n closeOver cs
        closeOver = fv (Fns fs)
evGroups [Record m] = VStruct <$> mapM eval m
evGroups [D (BindExp e)] = eval e
evGroups (D (BindExp e) : ts) = do
  v <- eval e
  v `seq` evGroups ts -- Make sure to demand v in case it's an effect!  Hack!
evGroups (D (Def p e) : ts) = do
  v <- eval e
  m <- withMatch (match p v) (evGroups ts)
  case m of
    Nothing -> expError (span p) ("Match failure "++showPp p++" = "++showPp v)
    Just r -> pure r
evGroups (D (Data _ (_,ds)) : ts) = foldr addCon (evGroups ts) ds
evGroups (g : _) = expError (span g) ("Unexpected group "++showPp g)

vClo :: HasCallStack => Span -> Var -> Arity -> Set Var -> [([Pat], Exp)] -> E Value
vClo s f n vs ds = do
  -- The icky thing here is we do the "closed vs" computation for every function
  -- in a binding group separately, even though the resulting env should be the same
  -- (since it's based on the passed-in vs).
  closed vs $ do
    (_, env) <- ask
    let cf = appDisjs s f ds
        d = Desc f n NoFold (CloFun cf)
    pure $
      if M.null env then
        VDesc d
      else
        VPAp d env []

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> E Value -> E Value
addCon (_, BindExp (Asc _ (Id _ _ Con c) t)) = conBinding c (cCon c (typeArity t))
addCon (s, d) = const (expError s ("addCon: not a constructor def "++showPp d))

evalTop :: HasCallStack => (SpanPos, Defs) -> Value
evalTop (sp, ds) =
  runEnv (evDefs ds) (sp, env0)
