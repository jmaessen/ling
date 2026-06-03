{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase #-}
module Semantics where
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.BakerVec
import Data.ByteString(ByteString)
import Data.ByteString.UTF8(toString, fromString)
import AST
import Data.Map(Map)
import qualified Data.Map as M
import GHC.Stack(HasCallStack)
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint((<+>))
import Debug.Trace(trace)

trace_enabled :: Bool
trace_enabled = False

traceSt :: String -> b -> b
traceSt s b | trace_enabled = trace s b
traceSt _ e = e

showPp :: (IsAST a) => a -> String
showPp = show . pp

showsPp :: (IsAST a) => [a] -> String
showsPp as = show (PP.fsep (pp <$> as))

{-
-- List model for Vec
type Vec a = [a]
push :: Vec a -> a -> Vec a
push v a = v ++ [a]

pushAndIndex :: Vec a -> a -> (Ofs, Vec a)
pushAndIndex v a = (length v, push v a)

(!) :: Vec a -> Ofs -> a
(!) = (!!)
-}

type ConName = ByteString
type FieldName = ByteString
type Var = ByteString

type Ofs = Int

type Env = (Map Var Ofs, Int)
type Stack = Vec Value

type Pat = Exp

-- Closures, Descriptors, and Values
newtype CloFun = CloFun ([Value] -> EI Value)

instance Eq CloFun where
  _ == _ = True -- Rely on parent to disambiguate.

instance Show CloFun where
  show _ = "<clofun>"

data Desc = Desc Var Int CloFun
  deriving (Eq, Show)

data Value
  = VConst Constant
  | VDesc Desc
  | VPAp Desc Stack [Value] -- Also closures
  | VObj Desc [Value]
  | VStruct (Map FieldName Value)
  deriving (Eq, Show)

vClo :: HasCallStack => Var -> Int -> [([Pat], Exp)] -> E Value
vClo f n ds = do
  cf <- appDisjs f ds
  pure $ do
    vec <- ask
    pure (VPAp (Desc f n (CloFun cf)) vec [])

pattern VCon0 :: ConName -> Value
pattern VCon0 c <- VDesc (Desc c 0 _) where
  VCon0 c =
    VDesc (Desc c 0 (CloFun (\_ -> error ("Applying nullary "++ toString c))))

pattern VCon :: ConName -> Int -> [Value] -> Value
pattern VCon c n vs <- VObj (Desc c n _) vs where
  VCon c n vs =
    VObj (Desc c n (CloFun (\_ -> error ("Applying already-built "++toString c)))) vs

{-# COMPLETE VConst, VDesc, VPAp, VCon, VStruct #-}

toList :: Value -> Maybe [Value]
toList (VCon0 "[]") = Just []
toList (VCon "::" 2 [a,as]) = (a:) <$> toList as
toList _ = Nothing

instance IsAST Value where
  isValid _ = []
  span _ = noSpan
  fullParen t = t
  noParen t = t
  pp (VConst c) = pp (Const noSpan c)
  pp (VCon0 c) = PP.text (toString c)
  pp (VDesc (Desc v n _)) =
    PP.text "<d" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp (Desc v n _) _ []) =
    PP.text "<c" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp (Desc v _ _) _ vs) = PP.parens (PP.text (toString v) <+> PP.sep (pp <$> vs))
  pp c@(VCon "::" 2 [_,_])
    | Just cs <- toList c =
      PP.brackets (PP.fsep $ PP.punctuate (PP.text ",") (pp <$> cs))
  pp (VCon "()" _ vs) =
    PP.parens (PP.hsep $ PP.punctuate (PP.text ",") (pp <$> vs))
  pp (VCon c _ vs) = PP.parens (PP.text (toString c) <+> PP.sep (pp <$> vs))
  pp (VStruct vs) =
    PP.vcat [PP.lbrace, PP.text "", PP.nest 2 (PP.vcat $ fmap ppField (M.toList vs)), PP.rbrace]
    where ppField (f, v) = PP.text (toString f) <+> PP.text "=" <+> pp v

-- Evaluation (environment) monad
type EI a = Reader Stack a
type EO a = Reader Env a
type E a = EO (EI a)
type Ef b a = EO (b -> EI a)

bindEnvWith :: (Ofs -> Ofs -> Ofs) -> Var -> Env -> Env
bindEnvWith c i (env, k) =
  (M.insertWith c i k env, k + 1)

lookupEnv :: HasCallStack => Var -> Env -> Ofs
lookupEnv i (env, _) =
  case M.lookup i env of
    Nothing -> error ("Unbound variable "++toString i)
    Just o -> o

getEnv :: EO Env
getEnv = ask

withEnv :: Env -> EO a -> EO a
withEnv env = local (const env)

findEnv :: HasCallStack => Var -> E Value
findEnv i = asks (lookupEnv i) >>= \ofs -> pure (asks (! ofs))

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: (EO [(Var, EI Value)]) -> E r -> E r
fixEnv a inner = do
  (env, k) <- ask
  let vs = runReader a (env', k')
      k' = k + length vs
      env' = M.fromList (zipWith (\(i, _) n -> (i,n)) vs [k..]) <> env
  inner' <- local (const (env', k')) inner
  pure $ do
    vec <- ask
    let vec' = foldl (\ve (_, f) -> push ve (runReader f vec')) vec vs
    local (const vec') inner'

-- Handles a *constant* binding (constructor def)
withBinding :: Var -> Value -> E r -> E r
withBinding i v r = local (bindEnvWith const i) $ do
  r' <- r
  pure $ local (`push` v) r'

-- Match monad
type MO a = State Env a
type MI a = StateT Stack Maybe a
type M v a = MO (v -> MI a)

matched :: Var -> M Value ()
matched i = do
  let collide _ _ = error ("Duplicate pattern bindings for key "++toString i)
  modify $ bindEnvWith collide i
  pure $ \v -> modify (`push` v)

matchFail :: MI a
matchFail = lift Nothing

-- Inject match into evaluation
withMatchesOr :: M b ()  -> E a -> Ef b a -> Ef b a
withMatchesOr m t e = do
  (env, k) <- ask
  e' <- e
  let (f, (env', k')) = runState m (mempty, k)
  local (const (env' <> env, k')) $ do
    t' <- t
    pure $ \v -> do
      vec <- ask
      case execStateT (f v) vec of
        Just vec' -> local (const vec') t'
        Nothing -> e' v

-- Assumes length ps == length vs
matches :: HasCallStack => [Pat] -> M [Value] ()
matches [p] = do
  f <- match p
  pure $ \case
    [v] -> f v
    vs -> error ("Pat len mismatch "++show (pp p)++" and "++showsPp vs)
matches [] = error "Empty pats"
matches ps = do
  ms <- matches' ps
  pure $ \vs -> do
    vec <- get
    case execStateT (ms vs) vec of
      Just vec' ->
        traceSt
          (showsPp ps++
           " match "++showsPp vs)
          (put vec')
      Nothing -> matchFail

matches' :: HasCallStack => [Pat] -> M [Value] ()
matches' ps = do
  let n = length ps
  fs <- mapM match' ps
  pure $ \vs ->
    if length vs == n then
      zipWithM_ ($) fs vs
    else
      error ("Pat len mismatch "++showsPp ps++" and "++showsPp vs)

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Pat -> M Value ()
match p = do
  f <- match' p
  pure $ \val -> do
    vec <- get
    case execStateT (f val) vec of
      Just vec' -> traceSt (showPp p++" matches "++showPp val) (put vec')
      Nothing -> matchFail

match' :: HasCallStack => Pat -> M Value ()
match' (Paren _ p) = match p
match' (Asc _ p _) = match' p
match' (Wild _) = pure $ \_ -> pure ()
match' (Id _ _ Var var) = matched var
match' (Id _ _ Con con) = pure $ \case
  (VCon0 con') | con == con' -> pure ()
  _ -> matchFail
match' (Const _ c) = pure $ \case
  (VConst vc) | c == vc -> pure ()
  _ -> matchFail
match' (Tuple _ es) = do
  f <- matches es
  pure $ \case
    v@(VCon "()" n vs)
      | n /= length vs -> error ("Bad tuple arity "++show n++": "++showPp v)
      | length es == length vs -> f vs
    _ -> matchFail
match' (List _ []) = pure $ \case
  (VCon0 "[]") -> pure ()
  _ -> matchFail
match' (List s (e:es)) = do
  f <- match' e
  fs <- match (List s es)
  pure $ \case
     (VCon "::" 2 [v, vs]) -> f v *> fs vs
     _ -> matchFail
match' (Block (_, ds)) = do
  ms <- mapM matchField ds
  pure $ \case
    (VStruct fs) -> mapM_ ($ fs) ms
    _ -> matchFail
match' (App s (Paren _ p) as) = match' (App s p as)
match' (App s (Asc _ p _) as) = match' (App s p as)
match' (App s (App _ p ps) as) = match' (App s p (ps <> as))
match' p@(App _ (Id _ _ Con con) as) = do
  let len = length as
  fs <- matches' as
  pure $ \case
    v@(VCon cn n rs)
      | len /= length rs -> error ("Obj ctor arity "++show n++" mismatch "++showPp v)
      | len == n && con == cn -> fs rs
      | len /= n && con == cn -> error ("Constructor pat expected arity "++show n ++ ": "++showPp p)
    _ -> matchFail
match' p@(App _ _ _) = error ("No constructor at head of pattern "++showPp p)
match' p = error ("Unrecognized pattern "++showPp p)

matchField :: HasCallStack => (Span, Def) -> M (Map FieldName Value) ()
matchField (s, BindExp p) = matchField (s, Def p p)
matchField (_, Def (Id _ _ Var fn) p) = do
  f <- match' p
  pure $ \fs -> lift (M.lookup fn fs) >>= f
matchField (_, Def f _) = error ("Illegal struct binding lhs "++showPp f)
matchField (_, p) = error ("Illegal struct pattern "++showPp p)

-- Apply value to args.
apply :: HasCallStack => Value -> [Value] -> EI Value
apply (VDesc d) vs = appWithArity d mempty (length vs) vs
apply (VPAp d vec as) bs = do
  let vs = as <> bs
  appWithArity d vec (length vs) vs
apply v _ = error ("apply: bad closure "++showPp v)

-- Apply function to args (arities given)
appWithArity :: HasCallStack => Desc -> Stack -> Int -> [Value] -> EI Value
appWithArity (Desc v 0 _) _ _ _ = error ("Applying 0-ary "++toString v)
appWithArity d@(Desc _ n (CloFun f)) vec nv vs
  | n > nv = pure $ VPAp d vec vs
  | n == nv = local (const vec) $ f vs
  | otherwise = do
      let (vs', vs'') = splitAt n vs
      f' <- local (const vec) (f vs')
      apply f' vs''

appDisjs :: HasCallStack => Var -> [([Pat], Exp)] -> Ef [Value] Value
appDisjs f [] = pure $ \vs -> error ("Match failure in appDisjs "++show f ++ " = " ++ showPp vs)
appDisjs f ((p, e):ds) =
  withMatchesOr (matches p) (eval e) (appDisjs f ds)

eval :: HasCallStack => Exp -> E Value
eval (Paren _ e) = eval e
eval (Asc _ e _) = eval e
eval (OpExp _ e) = eval e
eval (Id _ _ _ i) = findEnv i
eval a@(App _ _ []) = error ("Empty apply "++showPp a)
eval (App _ e es) = do
  e' <- eval e
  es' <- mapM eval es -- Effects need to be l -> r
  pure $ do
    ev <- e'
    evs <- sequence es' -- Effects l -> r
    apply ev evs
eval (Const _ c) = pure $ pure $ VConst c
eval (Wild _) = error "_ is a pat, not a valid expr"
eval e@(Arrow _ _ _) = error (showPp e ++ " is a type, not a valid expr")
eval e@(Ops _ _) = error (showPp e ++ " residual infix operators.")
eval (Fn s (Asc _ p _) e) = eval (Fn s p e)
eval (Fn s (App s' (Asc _ p _) ps) e) = eval (Fn s (App s' p ps) e)
eval (Fn s (App s' (App _ p ps) ps') e) =
  eval (Fn s (App s' p (ps ++ ps')) e)
eval (Fn _ (App _ p ps) e) = vClo "<anon>" (1 + length ps) [(p:ps, e)]
eval (Fn _ p e) = vClo "<anon1>" 1 [([p], e)]
eval (Tuple _ es) = do
  es' <- traverse eval es
  pure (VCon "()" (length es) <$> sequenceA es')
eval (List _ []) = pure $ pure $ VCon0 "[]"
eval (List s (e:es)) = do
  as <- traverse eval [e, List s es]
  pure (VCon "::" 2 <$> sequenceA as)
eval (Case _ e (_,es)) = do
  e' <- eval e
  ms <- appDisjs "<case>" (map toDisj es)
  pure $ do
    v <- e'
    ms [v]
eval (If _ c t e) = do
  c' <- eval c
  t' <- eval t
  e' <- eval e
  pure $ do
    c' >>= \case
      VCon0 "True" -> t'
      VCon0 "False" -> e'
      v -> error ("If non-boolean "++showPp v)
eval (IfMatch _ p c t e) = do
  c' <- eval c
  e' <- eval e
  m <- withMatchesOr (match p) (eval t) (pure $ \_ -> e')
  pure $ do
    v <- c'
    m v
eval (Block b) = evThings (groupDefs b)
eval e = error ("eval: Unhandled expression\n  "++showPp e++"\n  "++show e)

evThings :: HasCallStack => [BlockThing] -> E Value
evThings [] = pure $ pure $ VStruct mempty
evThings [BTS m] = do
  ms <- traverse eval m
  pure $ (VStruct <$> sequenceA ms)
evThings (D (BindExp (Asc _ (Id _ _ _ _) _)) : ts@(_:_)) = evThings ts
evThings [D (BindExp e)] = eval e
evThings (Fns fs:ts) = fixEnv (traverse clo fs) (evThings ts)
  where clo (v, n, ves) = (v,) <$> vClo v n ves
evThings (D (BindExp e) : ts) =
  eval e >>= \e' -> e' `seq` evThings ts
evThings (D (Def p e) : ts) = do
  e' <- eval e
  m <- withMatchesOr (match p)
    (evThings ts)
    (pure $ \v -> error ("Match failure "++showPp p++" = "++showPp v))
  pure $ do
    v <- e'
    m v
evThings (D (Fix _ _ _) : ts) = evThings ts
evThings (D (Data _ (_,ds)) : ts) = foldr addCon (evThings ts) ds
evThings (D (Struct _ _) : ts) = evThings ts
evThings (t:_) = error ("evThings: unexpected thing "++showPp t)

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> E a -> E a
addCon (_, BindExp e) = addCon' e
addCon (_, d) = error ("addCon: not a constructor def "++showPp d)

addCon' :: HasCallStack => Exp -> E a -> E a
addCon' (Paren _ e) = addCon' e
addCon' (Id _ _ Con c) = withBinding c (VCon0 c)
addCon' (App s (Paren _ e) as) = addCon' (App s e as)
addCon' (App s (App _ e as) as') = addCon' (App s e (as <> as'))
addCon' (App _ (Id _ _ Con c) as) = withBinding c (cCon c (length as))
addCon' (Asc s (Paren _ e) t) = addCon' (Asc s e t)
addCon' (Asc _ (Id _ _ Con c) t) = withBinding c (cCon c (typeArity t))
addCon' (List _ []) = withBinding "[]" (VCon0 "[]")
addCon' e = error ("addCon': not a constructor def "++showPp e)

typeArity :: HasCallStack => Exp -> Int
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

cCon :: Var -> Int -> Value
cCon v 0 = VCon0 v
cCon v i = VDesc d
  where d = Desc v i (CloFun (pure . VObj d))

toDisj :: HasCallStack => (Span, Def) -> ([Pat], Exp)
toDisj (_, Def p e) = ([p], e)
toDisj (_, d) = error ("Illegal case disjunct "++showPp d)

data BlockThing
  = D Def
  | Fns [(Var, Int, [([Pat], Exp)])]
  | BTS (Map FieldName Exp)
  deriving (Eq, Show)

instance IsAST BlockThing where
  isValid _ = []
  span _ = noSpan
  fullParen d = d
  noParen d = d
  pp (D d) = pp d
  pp (BTS m) = pp [(Def (Id noSpan Ident Var f) e) | (f, e) <- M.toList m]
  pp (Fns m) = PP.vcat $ concat [
    [PP.text "-- Group:"],
    [pp $ Def (App noSpan i ps) e |
      (nm, _, pes) <- m,
      let i = Id noSpan Ident Var nm,
      (ps, e) <- pes ],
    [PP.text "-- End group"]]

groupDefs :: HasCallStack => Defs -> [BlockThing]
groupDefs (_, ds) =
  case foldr groupDef [] ds of
    [] -> [BTS mempty]
    ds' -> ds'

groupDef :: HasCallStack => (Span, Def) -> [BlockThing] -> [BlockThing]
groupDef (s, BindExp (Asc s' (Paren _ e) t)) ts =
  groupDef (s, BindExp (Asc s' e t)) ts
groupDef (_, a@(BindExp (Asc _ (Id _ _ Var _) _))) (Fns m : bs) =
  Fns m : D a : bs
groupDef (_, Def (Id _ _ Var var) e) [] = [BTS (M.singleton var e)]
groupDef (_, Def (Id _ _ Var var) e) (BTS m:_) = [BTS (M.insert var e m)]
groupDef d (BTS _ : _) = error (showPp d ++ " is not a struct binding")
groupDef (_, d@(BindExp _)) ts = (D d):ts
groupDef (s, Def (Asc _ p _) e) ts = groupDef (s, Def p e) ts
groupDef (s, Def (App s' (Asc _ p _) ps) e) ts =
  groupDef (s, Def (App s' p ps) e) ts
groupDef (s, Def (App s' (App _ p ps) ps') e) ts =
  groupDef (s, Def (App s' p (ps ++ ps')) e) ts
groupDef (_, Def (App _ (Id _ _ Var f) ps) e) (Fns ((ff, n, pes): fns) : ts)
  | f == ff =
    if n /= length ps then
      error ("Arity mismatch in definition of "++toString f)
    else
      Fns ((ff, n, (ps, e):pes) : fns) : ts
  | otherwise = Fns ((f, length ps, [(ps, e)]) : (ff, n, pes) : fns) : ts
groupDef (_, Def (App _ (Id _ _ Var f) ps) e) ts =
  Fns [(f, length ps, [(ps, e)])] : ts
groupDef (_, d) ts = D d : ts

mkPrim :: (Var, Int, [Value] -> Value) -> (Var, Value)
mkPrim (v, n, f) = (v, VDesc (Desc v n (CloFun $ pure . f)))

vBool :: Bool -> Value
vBool True = VCon0 "True"
vBool False = VCon0 "False"

i2 :: HasCallStack => (a -> Value) -> (Integer -> Integer -> a) -> [Value] -> Value
i2 v op [VConst (EInt a), VConst (EInt b)] = v (a `op` b)
i2 _ _ vs = error ("Bad args "++showsPp vs)

evalTop :: HasCallStack => Defs -> Value
evalTop ds =
  let (env, vec) = expand env0
  in runReader (runReader (eval (Block ds)) env) vec

valToList :: HasCallStack => Value -> [Value]
valToList v =
  case toList v of
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

expand :: Map Var Value -> (Env, Vec Value)
expand e =
  foldl (\((env, k), vec) (i, v) -> ((M.insert i k env, k+1), push vec v))
        ((mempty, 0), mempty)
        (M.toList e)

env0 :: Map Var Value
env0 = foldl (\env p -> uncurry M.insert (mkPrim p) env) mempty [
  ("prim", 2, getPrim),
  ("intAdd", 2, i2 (VConst . EInt) (+)),
  ("intSub", 2, i2 (VConst . EInt) (-)),
  ("intEq", 2, i2 vBool (==)),
  ("intLE", 2, i2 vBool (<=)),
  ("strAppend", 2, \[VConst (EString a), VConst (EString b)] -> VConst (EString (a <> b))),
  ("putStr", 1, \[v] -> trace (toString (valToString v)) (VCon0 "()")), -- total hack, but "safe"
  ("strConcat", 1, strConcat),
  ("intToStr", 1, \[v] -> VConst $ EString $ fromString $ show $ valToInt v)
  ]
