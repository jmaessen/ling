{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}
module Semantics where
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

type ConName = ByteString
type FieldName = ByteString
type Var = ByteString

type Env = Map Var Value

type Pat = Exp

newtype CloFun = CloFun (Env -> [Value] -> Value)

instance Eq CloFun where
  _ == _ = True -- Rely on parent to disambiguate.

instance Show CloFun where
  show _ = "<clofun>"

data Value
  = VConst Constant
  | VClo Var Int CloFun Env
  | VCon ConName Int [Value]
  | VPAp Value [Value]
  | VTuple [Value]
  | VStruct (Map FieldName Value)
  deriving (Eq, Show)

toList :: Value -> Maybe [Value]
toList (VCon "[]" 0 []) = Just []
toList (VCon "::" 2 [a,as]) = (a:) <$> toList as
toList _ = Nothing

instance IsAST Value where
  isValid _ = []
  span _ = noSpan
  fullParen t = t
  noParen t = t
  pp (VConst c) = pp (Const noSpan c)
  pp (VClo v n _ _) = PP.text "<closure" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp v vs) = PP.parens (pp v <+> PP.sep (pp <$> vs))
  pp (VCon c _ []) = PP.text (toString c)
  pp c@(VCon "::" 2 [_, _])
    | Just cs <- toList c = PP.brackets (PP.sep $ PP.punctuate (PP.text ",") (pp <$> cs))
  pp (VCon c _ vs) = PP.parens (PP.text (toString c) <+> PP.sep (pp <$> vs))
  pp (VTuple vs) = PP.parens (PP.hsep $ PP.punctuate (PP.text ",") (pp <$> vs))
  pp (VStruct vs) =
    PP.vcat [PP.lbrace, PP.text "", PP.nest 2 (PP.vcat $ fmap ppField (M.toList vs)), PP.rbrace]
    where ppField (f, v) = PP.text (toString f) <+> PP.text "=" <+> pp v


-- Assumes length ps == length vs
matches :: HasCallStack => Env -> [Pat] -> [Value] -> Maybe Env
matches env ps vs =
  (<>env) <$> foldr (\(p, v) -> (>>= (\env' -> match env' p v))) (Just mempty) (zip ps vs)

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Env -> Pat -> Value -> Maybe Env
match env (Paren _ p) val = match env p val
match env (Asc _ p _) val = match env p val
match env (Wild _) _ = Just env
match env (Id _ _ Var var) val =
  case M.lookup var env of
    Nothing -> Just $ M.insert var val env
    Just _ -> error ("Duplicate binding of "++toString var++" in pat")
match env (Id _ _ Con con) (VCon con' _ []) | con == con' = Just env
match _ (Id _ _ Con _) _ = Nothing
match env (Const _ c) (VConst vc) | c == vc = Just env
match _ (Const _ _) _ = Nothing
match env (Tuple _ es) (VTuple vs)
  | length es /= length vs = Nothing
  | otherwise = matches env es vs
match _ (Tuple _ _) _ = Nothing
match env (List _ []) (VCon "[]" 0 []) = Just env
match env (List s (e:es)) (VCon "::" 2 [v, vs]) = do
  env' <- match env e v
  match env' (List s es) vs
match _ (List _ _) _ = Nothing
match env (Block (_, ds)) (VStruct fs) =
  foldr (matchField fs) (Just env) ds
match _ (Block _) _ = Nothing
match env (App s (Paren _ p) as) v = match env (App s p as) v
match env (App s (Asc _ p _) as) v = match env (App s p as) v
match env (App s (App _ p ps) as) v = match env (App s p (ps <> as)) v
match env p@(App _ (Id _ _ Con con) as) (VCon cn n rs)
  | len == n && len == length rs && con == cn = matches env as rs
  | len /= n && con == cn = error ("Constructor pat expected arity "++show n ++ ": "++show (pp p))
  where len = length as
match _ (App _ _ _) _ = Nothing
match _ p v =
  error ("Unrecognized pattern or missed match:\n"++show (pp p)++"\n"++show (pp v))

matchField :: HasCallStack => Map FieldName Value -> (Span, Def) -> Maybe Env -> Maybe Env
matchField _ _ Nothing = Nothing
matchField fs (_, BindExp p@(Id _ _ Var fn)) (Just env) =
  match env p =<< M.lookup fn fs
matchField _ (_, BindExp e) _ = error ("Illegal struct binding exp "++show (pp e))
matchField fs (_, Def (Id _ _ Var fn) p) (Just env) =
  match env p =<< M.lookup fn fs
matchField _ (_, Def f _) _ = error ("Illegal struct binding lhs "++show (pp f))
matchField _ (_, p) _ = error ("Illegal struct pattern "++show (pp p))

-- What's the arity of the function?
arity :: HasCallStack => Value -> Int
arity (VClo _ n _ _) = n
arity (VPAp v as) = arity v - length as
arity v = error ("No arity for "++show v)

-- Apply value to args.
apply :: HasCallStack => Value -> [Value] -> Value
apply c vs = appWithArity (arity c) (length vs) c vs

-- Apply function to args (arities given)
appWithArity :: HasCallStack => Int -> Int -> Value -> [Value] -> Value
appWithArity n nv c vs
  | n > nv = VPAp c vs
  | n == nv = appSat c vs
  | otherwise = do
      let (vs', vs'') = splitAt n vs
      apply (appSat c vs') vs''

-- Apply function to exactly its arity of args.
appSat :: HasCallStack => Value -> [Value] -> Value
appSat (VClo _ _ (CloFun f) env) vs = f env vs
appSat (VPAp v ds) vs = appSat v (ds <> vs)
appSat v _ = error ("appSat: bad closure "++show (pp v))

vClo :: Var -> Int -> [([Pat], Exp)] -> Env -> Value
vClo f n ds env = VClo f n (CloFun $ appDisjs f ds) env

appDisjs :: HasCallStack => Var -> [([Pat], Exp)] -> Env -> [Value] -> Value
appDisjs f [] _ vs = error ("Match failure in appDisjs "++show f ++ " = " ++ show (pp vs))
appDisjs f ((p, e):ds) env vs =
  case matches mempty p vs of
    Just envm -> eval (envm <> env) e
    Nothing -> appDisjs f ds env vs

patLen :: Pat -> Int
patLen (Asc _ e _) = patLen e
patLen (App _ e es) = patLen e + length es
patLen _ = 1

eval :: HasCallStack => Env -> Exp -> Value
eval env (Paren _ e) = eval env e
eval env (Asc _ e _) = eval env e
eval env (OpExp _ e) = eval env e
eval env (Id _ _ _ i) =
  case M.lookup i env of
    Just val -> traceS i $ val
    Nothing -> error ("Unbound variable "++toString i)
eval _ a@(App _ _ []) = error ("Empty apply "++show (pp a))
eval env (App _ e es) = apply (eval env e) (map (eval env) es)
eval _ (Const _ c) = VConst c
eval _ (Wild _) = error "_ is a pat, not a valid expr"
eval _ e@(Arrow _ _ _) = error (show (pp e) ++ " is a type, not a valid expr")
eval _ e@(Ops _ _) = error (show (pp e) ++ " residual infix operators.")
eval env (Fn s (Asc _ p _) e) = eval env (Fn s p e)
eval env (Fn s (App s' (Asc _ p _) ps) e) = eval env (Fn s (App s' p ps) e)
eval env (Fn s (App s' (App _ p ps) ps') e) =
  eval env (Fn s (App s' p (ps ++ ps')) e)
eval env (Fn _ (App _ p ps) e) = vClo "<anon>" (1 + length ps) [(p:ps, e)] env
eval env (Fn _ p e) = vClo "<anon1>" 1 [([p], e)] env
eval env (Tuple _ es) = VTuple $ fmap (eval env) es
eval _ (List _ []) = VCon "[]" 0 []
eval env (List s (e:es)) = VCon "::" 2 [eval env e, eval env (List s es)]
eval env (Case _ e (_,es)) =
  appDisjs "<case>" (map toDisj es) env [eval env e]
eval env (If _ c t e) =
  case eval env c of
    VCon "True" 0 [] -> eval env t
    _ -> eval env e
eval env (IfMatch _ p c t e) =
  case match mempty p (eval env c) of
    Just env' -> eval (env' <> env) t
    Nothing -> eval env e
eval env (Block b) = evThings env (groupDefs b)
eval _ e = error ("eval: Unhandled expression\n  "++show (pp e)++"\n  "++show e)

evThings :: HasCallStack => Env -> [BlockThing] -> Value
evThings _ [] = VTuple []
evThings env [BTS m] = VStruct (eval env <$> m)
evThings env (D (BindExp (Asc _ (Id _ _ _ _) _)) : ts@(_:_)) = evThings env ts
evThings env [D (BindExp e)] = eval env e
evThings env (Fns fs:ts) = evThings env' ts
  where
    clos = fmap clo fs
    env' = M.fromList clos <> env
    clo (v, n, ves) = (v, vClo v n ves env')
evThings env (D (BindExp e) : ts) =
  eval env e `seq` evThings env ts
evThings env (D (Def p e) : ts) =
  let v = eval env e
  in  case match mempty p v of
        Nothing -> error ("Match failure "++show (pp p)++" = "++show (pp v))
        Just env' -> evThings (env' <> env) ts
evThings env (D (Fix _ _ _) : ts) = evThings env ts
evThings env (D (Data _ (_,ds)) : ts) = evThings (foldr addCon env ds) ts
evThings env (D (Struct _ _) : ts) = evThings env ts
evThings _ (t:_) = error ("evThings: unexpected thing "++show (pp t))

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> Env -> Env
addCon (_, BindExp e) = addCon' e
addCon (_, d) = error ("addCon: not a constructor def "++show (pp d))

addCon' :: HasCallStack => Exp -> Env -> Env
addCon' (Paren _ e) env = addCon' e env
addCon' (Id _ _ Con c) env = M.insert c (VCon c 0 []) env
addCon' (App s (Paren _ e) as) env = addCon' (App s e as) env
addCon' (App s (App _ e as) as') env = addCon' (App s e (as <> as')) env
addCon' (App _ (Id _ _ Con c) as) env = M.insert c (cCon c (length as)) env
addCon' (Asc s (Paren _ e) t) env = addCon' (Asc s e t) env
addCon' (Asc _ (Id _ _ Con c) t) env = M.insert c (cCon c (typeArity t)) env
addCon' (List _ []) env = M.insert "[]" (VCon "[]" 0 []) env
addCon' e _ = error ("addCon': not a constructor def "++show (pp e))

typeArity :: HasCallStack => Exp -> Int
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

cCon :: Var -> Int -> Value
cCon v 0 = VCon v 0 []
cCon v i = VClo v i (CloFun $ const (VCon v i)) mempty

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
mkPrim (v, n, f) = (v, VClo v n (CloFun $ const f) mempty)

vBool :: Bool -> Value
vBool True = VCon "True" 0 []
vBool False = VCon "False" 0 []

i2 :: HasCallStack => (a -> Value) -> (Integer -> Integer -> a) -> [Value] -> Value
i2 v op [VConst (EInt a), VConst (EInt b)] = v (a `op` b)
i2 _ _ vs = error ("Bad args "++show (pp vs))

evalTop :: HasCallStack => Defs -> Value
evalTop ds = eval env0 (Block ds)

valToList :: HasCallStack => Value -> [Value]
valToList (VCon "[]" 0 []) = []
valToList (VCon "::" 2 [h, t]) = h : valToList t
valToList v = error ("valToList: not a list "++show (pp v))

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
  case M.lookup (valToString v) env0 of
    Just r@(VClo _ n' _ _)
      | fromInteger (valToInt n) == n' -> r
      | otherwise ->
        error ("Arity mismatch on prim "++show (pp v)++" registered as "++show n'++" asked for "++show (pp n))
    _ -> error ("Nonexistent prim "++show (pp v))
getPrim as = error ("Bad args to prim "++show (pp as))

env0 :: Env
env0 = M.fromList $ fmap mkPrim [
  ("prim", 2, getPrim),
  ("intAdd", 2, i2 (VConst . EInt) (+)),
  ("intSub", 2, i2 (VConst . EInt) (-)),
  ("intEq", 2, i2 vBool (==)),
  ("intLE", 2, i2 vBool (<=)),
  ("strAppend", 2, \[VConst (EString a), VConst (EString b)] -> VConst (EString (a <> b))),
  ("putStr", 1, \[v] -> trace (toString (valToString v)) (VTuple [])), -- total hack, but "safe"
  ("strConcat", 1, strConcat),
  ("intToStr", 1, \[v] -> VConst $ EString $ fromString $ show $ valToInt v)
  ]
