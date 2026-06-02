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
import Debug.Trace(trace, traceShow)

trace_enabled :: Bool
trace_enabled = False

traceS :: Show a => a -> b -> b
traceS a b | trace_enabled = traceShow a b
traceS _ e = e

traceSt :: String -> b -> b
traceSt s b | trace_enabled = trace s b
traceSt _ e = e

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

type Env = (Map Var Ofs, Vec Value)

type Pat = Exp

-- Closures, Descriptors, and Values
newtype CloFun = CloFun ([Value] -> E Value)

instance Eq CloFun where
  _ == _ = True -- Rely on parent to disambiguate.

instance Show CloFun where
  show _ = "<clofun>"

data Desc = Desc Var Int CloFun
  deriving (Eq, Show)

data Value
  = VConst Constant
  | VDesc Desc
  | VPAp Desc Env [Value] -- Also closures
  | VObj Desc [Value]
  | VStruct (Map FieldName Value)
  deriving (Eq, Show)

vClo :: HasCallStack => Var -> Int -> [([Pat], Exp)] -> E Value
vClo f n ds =
  (\env -> VPAp (Desc f n (CloFun $ (withEnv env . appDisjs f ds))) env []) <$> getEnv

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
    PP.text "<desc" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp (Desc v n _) _ []) =
    PP.text "<closure" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp (Desc v _ _) _ vs) = PP.parens (PP.text (toString v) <+> PP.sep (pp <$> vs))
  pp c@(VCon "::" 2 [_,_])
    | Just cs <- toList c =
      PP.brackets (PP.sep $ PP.punctuate (PP.text ",") (pp <$> cs))
  pp (VCon "()" _ vs) =
    PP.parens (PP.hsep $ PP.punctuate (PP.text ",") (pp <$> vs))
  pp (VCon c _ vs) = PP.parens (PP.text (toString c) <+> PP.sep (pp <$> vs))
  pp (VStruct vs) =
    PP.vcat [PP.lbrace, PP.text "", PP.nest 2 (PP.vcat $ fmap ppField (M.toList vs)), PP.rbrace]
    where ppField (f, v) = PP.text (toString f) <+> PP.text "=" <+> pp v

-- Evaluation (environment) monad
type E a = Reader Env a

bindEnvWith :: (Ofs -> Ofs -> Ofs) -> Var -> Value -> Env -> Env
bindEnvWith c i v (env, vec) =
  let (o, vec') = pushAndIndex vec v
  in (M.insertWith c i o env, vec')

lookupEnv :: HasCallStack => Var -> Env -> Value
lookupEnv i (env, vec) =
  case M.lookup i env of
    Nothing -> error ("Unbound variable "++toString i)
    Just o -> vec ! o

getEnv :: E Env
getEnv = ask

withEnv :: Env -> E a -> E a
withEnv env = local (const env)

findEnv :: HasCallStack => Var -> E Value
findEnv i = asks (lookupEnv i)

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: (E [(Var, Value)]) -> E r -> E r
fixEnv a = local $ \(env, vec) ->
  let vs = runReader a (env', vec')
      env' :: Map Var Ofs
      env' = M.fromList (zipWith (\(i, _) n -> (i,n)) vs [length vec ..]) <> env
      vec' :: Vec Value
      vec' = foldl (\ve (_, v) -> push ve v) vec vs
  in (env', vec')

withBinding :: Var -> Value -> E r -> E r
withBinding i v = local $ bindEnvWith const i v

-- Match monad
type M a = StateT Env Maybe a

matched :: Var -> Value -> M ()
matched i v = modify $ bindEnvWith collide i v
  where collide _ _ = error ("Duplicate pattern bindings for key "++toString i)

matchFail :: M a
matchFail = lift Nothing

-- Inject match into evaluation
withMatchesOr :: M () -> E a -> E a -> E a
withMatchesOr m t e = do
  (env, vec) <- ask
  case execStateT m (mempty, vec) of
    Just (env', vec') -> local (const (env'<>env, vec')) t
    Nothing -> e

-- Assumes length ps == length vs
matches :: HasCallStack => [Pat] -> [Value] -> M ()
matches [p] [v] = match p v
matches [] _ = error "Empty pats"
matches _ [] = error "Empty vars"
matches ps vs = do
  env <- get
  case execStateT (matches' ps vs) env of
    Just env' -> traceSt (show (PP.hsep (pp <$> ps))++" match "++show (PP.hsep (pp <$> vs))) (put env')
    Nothing -> matchFail

matches' :: HasCallStack => [Pat] -> [Value] -> M ()
matches' ps vs = zipWithM_ match' ps vs

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Pat -> Value -> M ()
match p val = do
  env <- get
  case execStateT (match' p val) env of
    Just env' -> traceSt (show (pp p)++" matches "++show (pp val)) (put env')
    Nothing -> matchFail

match' :: HasCallStack => Pat -> Value -> M ()
match' (Paren _ p) val = match p val
match' (Asc _ p _) val = match' p val
match' (Wild _) _ = pure ()
match' (Id _ _ Var var) val = matched var val
match' (Id _ _ Con con) (VCon0 con')
  | con == con' = pure ()
match' (Id _ _ Con _) _ = matchFail
match' (Const _ c) (VConst vc) | c == vc = pure ()
match' (Const _ _) _ = matchFail
match' (Tuple _ es) v@(VCon "()" n vs)
  | n /= length vs = error ("Bad tuple arity "++show n++": "++show (pp v))
  | length es /= length vs = matchFail
  | otherwise = matches' es vs
match' (Tuple _ _) _ = matchFail
match' (List _ []) (VCon0 "[]") = pure ()
match' (List s (e:es)) (VCon "::" 2 [v, vs]) = do
  match' e v
  match' (List s es) vs
match' (List _ _) _ = matchFail
match' (Block (_, ds)) (VStruct fs) =
  mapM_ (matchField fs) ds
match' (Block _) _ = matchFail
match' (App s (Paren _ p) as) v = match' (App s p as) v
match' (App s (Asc _ p _) as) v = match' (App s p as) v
match' (App s (App _ p ps) as) v = match' (App s p (ps <> as)) v
match' p@(App _ (Id _ _ Con con) as) v@(VCon cn n rs)
  | len /= length rs = error ("Obj ctor arity "++show n++" mismatch "++show (pp v))
  | len == n && con == cn = matches' as rs
  | len /= n && con == cn = error ("Constructor pat expected arity "++show n ++ ": "++show (pp p))
  where len = length as
match' (App _ _ _) _ = matchFail
match' p v =
  error ("Unrecognized pattern or missed match:\n"++show (pp p)++"\n"++show (pp v))

matchField :: HasCallStack => Map FieldName Value -> (Span, Def) -> M ()
matchField fs (_, BindExp p@(Id _ _ Var fn)) =
  match' p =<< lift(M.lookup fn fs)
matchField _ (_, BindExp e) = error ("Illegal struct binding exp "++show (pp e))
matchField fs (_, Def (Id _ _ Var fn) p) =
  match' p =<< lift (M.lookup fn fs)
matchField _ (_, Def f _) = error ("Illegal struct binding lhs "++show (pp f))
matchField _ (_, p) = error ("Illegal struct pattern "++show (pp p))

-- Apply value to args.
apply :: HasCallStack => Value -> [Value] -> E Value
apply (VDesc d) vs = appWithArity d mempty (length vs) vs
apply (VPAp d env as) bs = appWithArity d env (length vs) vs
  where vs = as <> bs
apply v _ = error ("apply: bad closure "++show (pp v))

-- Apply function to args (arities given)
appWithArity :: HasCallStack => Desc -> Env -> Int -> [Value] -> E Value
appWithArity (Desc v 0 _) _ _ _ = error ("Applying 0-ary "++toString v)
appWithArity d@(Desc _ n (CloFun f)) env nv vs
  | n > nv = pure $ VPAp d env vs
  | n == nv = withEnv env $ f vs
  | otherwise = do
      let (vs', vs'') = splitAt n vs
      f' <- withEnv env (f vs')
      apply f' vs''

appDisjs :: HasCallStack => Var -> [([Pat], Exp)] -> [Value] -> E Value
appDisjs f [] vs = error ("Match failure in appDisjs "++show f ++ " = " ++ show (pp vs))
appDisjs f ((p, e):ds) vs = withMatchesOr (matches p vs) (eval e) (appDisjs f ds vs)

eval :: HasCallStack => Exp -> E Value
eval (Paren _ e) = eval e
eval (Asc _ e _) = eval e
eval (OpExp _ e) = eval e
eval (Id _ _ _ i) = findEnv i
eval a@(App _ _ []) = error ("Empty apply "++show (pp a))
eval (App _ e es) = do
  e' <- eval e
  es' <- traverse eval es
  apply e' es'
eval (Const _ c) = pure $ VConst c
eval (Wild _) = error "_ is a pat, not a valid expr"
eval e@(Arrow _ _ _) = error (show (pp e) ++ " is a type, not a valid expr")
eval e@(Ops _ _) = error (show (pp e) ++ " residual infix operators.")
eval (Fn s (Asc _ p _) e) = eval (Fn s p e)
eval (Fn s (App s' (Asc _ p _) ps) e) = eval (Fn s (App s' p ps) e)
eval (Fn s (App s' (App _ p ps) ps') e) =
  eval (Fn s (App s' p (ps ++ ps')) e)
eval (Fn _ (App _ p ps) e) = vClo "<anon>" (1 + length ps) [(p:ps, e)]
eval (Fn _ p e) = vClo "<anon1>" 1 [([p], e)]
eval (Tuple _ es) = VCon "()" (length es) <$> traverse eval es
eval (List _ []) = pure $ VCon0 "[]"
eval (List s (e:es)) = VCon "::" 2 <$> traverse eval [e, List s es]
eval (Case _ e (_,es)) = do
  v <- eval e
  appDisjs "<case>" (map toDisj es) [v]
eval (If _ c t e) =
  eval c >>= \case
    VCon0 "True" -> eval t
    VCon0 "False" -> eval e
    v -> error ("If non-boolean "++show (pp v))
eval (IfMatch _ p c t e) = do
  v <- eval c
  withMatchesOr (match p v) (eval t) (eval e)
eval (Block b) = evThings (groupDefs b)
eval e = error ("eval: Unhandled expression\n  "++show (pp e)++"\n  "++show e)

evThings :: HasCallStack => [BlockThing] -> E Value
evThings [] = pure $ VStruct mempty
evThings [BTS m] = VStruct <$> (traverse eval m)
evThings (D (BindExp (Asc _ (Id _ _ _ _) _)) : ts@(_:_)) = evThings ts
evThings [D (BindExp e)] = eval e
evThings (Fns fs:ts) = fixEnv (traverse clo fs) (evThings ts)
  where clo (v, n, ves) = (v,) <$> vClo v n ves
evThings (D (BindExp e) : ts) =
  eval e >>= \e' -> e' `seq` evThings ts
evThings (D (Def p e) : ts) = do
  v <- eval e
  withMatchesOr (match p v)
    (evThings ts)
    (error ("Match failure "++show (pp p)++" = "++show (pp v)))
evThings (D (Fix _ _ _) : ts) = evThings ts
evThings (D (Data _ (_,ds)) : ts) = foldr addCon (evThings ts) ds
evThings (D (Struct _ _) : ts) = evThings ts
evThings (t:_) = error ("evThings: unexpected thing "++show (pp t))

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> E a -> E a
addCon (_, BindExp e) = addCon' e
addCon (_, d) = error ("addCon: not a constructor def "++show (pp d))

addCon' :: HasCallStack => Exp -> E a -> E a
addCon' (Paren _ e) r = addCon' e r
addCon' (Id _ _ Con c) r = withBinding c (VCon0 c) r
addCon' (App s (Paren _ e) as) r = addCon' (App s e as) r
addCon' (App s (App _ e as) as') r = addCon' (App s e (as <> as')) r
addCon' (App _ (Id _ _ Con c) as) r = withBinding c (cCon c (length as)) r
addCon' (Asc s (Paren _ e) t) r = addCon' (Asc s e t) r
addCon' (Asc _ (Id _ _ Con c) t) r = withBinding c (cCon c (typeArity t)) r
addCon' (List _ []) r = withBinding "[]" (VCon0 "[]") r
addCon' e _ = error ("addCon': not a constructor def "++show (pp e))

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
toDisj (_, d) = error ("Illegal case disjunct "++show (pp d))

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
groupDef d (BTS _ : _) = error (show (pp d) ++ " is not a struct binding")
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
i2 _ _ vs = error ("Bad args "++show (PP.hsep (pp <$> vs)))

evalTop :: HasCallStack => Defs -> Value
evalTop ds = runReader (eval (Block ds)) env0

valToList :: HasCallStack => Value -> [Value]
valToList v =
  case toList v of
    Just vs -> vs
    _ -> error ("valToList: not a list "++show (pp v))

valToString :: HasCallStack => Value -> ByteString
valToString (VConst (EString s)) = s
valToString v = error ("valToString: not a string "++show (pp v))

strConcat :: HasCallStack => [Value] -> Value
strConcat [v] = VConst (EString (mconcat (valToString <$> valToList v)))
strConcat vs = error ("strConcat: wrong number of args "++show (pp vs))

valToInt :: HasCallStack => Value -> Integer
valToInt (VConst (EInt i)) = i
valToInt v = error ("valToInt: not an int "++show (pp v))

getPrim :: HasCallStack => [Value] -> Value
getPrim [n, v] =
  case lookupEnv (valToString v) env0 of
    r@(VDesc (Desc _ n' _))
      | fromInteger (valToInt n) == n' -> r
      | otherwise ->
        error ("Arity mismatch on prim "++show (pp v)++" registered as "++show n'++" asked for "++show (pp n))
    _ -> error ("Bad prim "++show (pp v))
getPrim as = error ("Bad args to prim "++show (pp as))

env0 :: Env
env0 = foldl (\env p -> uncurry (bindEnvWith const) (mkPrim p) env) mempty [
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
