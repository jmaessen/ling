{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}
module Semantics where
import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.UTF8(toString, fromString)
import AST
import Data.Map(Map)
import qualified Data.Map as M
import GHC.Stack(HasCallStack)
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint((<+>))
import Debug.Trace(trace)

traceS :: Show a => a -> b -> b
traceS _ e = e

type ConName = ByteString
type FieldName = ByteString
type Var = ByteString

type Env = Map Var Value

type Pat = Exp

newtype Prim = Prim ([Value] -> Value)

instance Eq Prim where
  _ == _ = False

instance Show Prim where
  show _ = "<prim>"

data Value
  = VConst Constant
  | VClo Var Int [([Pat],Exp)] Env
  | VPAp Value [Value]
  | VPrim Var Int Prim
  | VCon ConName [Value]
  | VTuple [Value]
  | VStruct (Map FieldName Value)
  deriving (Eq, Show)

toList :: Value -> Maybe [Value]
toList (VCon "[]" []) = Just []
toList (VCon "::" [a,as]) = (a:) <$> toList as
toList _ = Nothing

instance IsAST Value where
  isValid _ = []
  span _ = noSpan
  fullParen t = t
  noParen t = t
  pp (VConst c) = pp (Const noSpan c)
  pp (VClo v n _ _) = PP.text "<closure" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")
  pp (VPAp v vs) = PP.parens (pp v <+> PP.sep (pp <$> vs))
  pp (VPrim p n _) = PP.text "<prim" <+> PP.text (toString p) <+> PP.int n <+> PP.text ">"
  pp (VCon c []) = PP.text (toString c)
  pp c@(VCon "::" [_, _])
    | Just cs <- toList c = PP.brackets (PP.sep $ PP.punctuate (PP.text ",") (pp <$> cs))
  pp (VCon c vs) = PP.parens (PP.text (toString c) <+> PP.sep (pp <$> vs))
  pp (VTuple vs) = PP.parens (PP.hsep $ PP.punctuate (PP.text ",") (pp <$> vs))
  pp (VStruct vs) =
    PP.vcat [PP.lbrace, PP.text "", PP.nest 2 (PP.vcat $ fmap ppField (M.toList vs)), PP.rbrace]
    where ppField (f, v) = PP.text (toString f) <+> PP.text "=" <+> pp v


-- Assumes length ps == length vs
matches :: HasCallStack => Env -> [Pat] -> [Value] -> Maybe Env
matches ps vs env = (<>env) <$> foldr (=<<) (Just mempty) (zipWith match ps vs)

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Env -> Pat -> Value -> Maybe Env
match (Paren _ p) val env = match p val env
match (Asc _ p _) val env = match p val env
match (Wild _) _ env = Just env
match (Id _ _ Var var) val env =
  case M.lookup var env of
    Nothing -> Just $ M.insert var val env
    Just _ -> error ("Duplicate binding of "++toString var++" in pat")
match (Id _ _ Con con) (VCon con' []) env | con == con' = Just env
match (Id _ _ Con _) _ env = Nothing
match (Const _ c) (VConst vc) env | c == vc = Just env
match (Const _ c) _ _ = Nothing
match (Tuple _ es) (VTuple vs) env
  | length es /= length vs = Nothing
  | otherwise = matches es vs env
match (Tuple _ _) _ env = Nothing
match (List _ []) (VCon "[]" []) env = Just env
match (List s (e:es)) (VCon "::" [v, vs]) env = do
  env' <- match e v env
  match (List s es) vs env'
match (List _ _) _ env = Nothing
match (Block (_, ds)) (VStruct fs) env =
  foldr (matchField fs) (Just env) ds
match (Block _) _ _ = Nothing
match (App _ f as) (VCon cn rs) env
  | length as <= length rs = do
    let (rsf, rs') = splitAt (length rs - length as) rs
    env' <- match f (VCon cn rsf) env
    matches as rs' env'
match (App _ _ _) _ _ = Nothing

matchField :: HasCallStack => Map FieldName Value -> (Span, Def) -> Maybe Env -> Maybe Env
matchField _ _ Nothing = Nothing
matchField fs (_, BindExp p@(Id _ _ Var fn)) (Just env) =
  (\v -> match p v env) =<< M.lookup fn fs
matchField _ (_, BindExp e) _ = error ("Illegal struct binding exp "++show (pp e))
matchField fs (_, Def (Id _ _ Var fn) p) (Just env) =
  (\v -> match p v env) =<< M.lookup fn fs
matchField _ (_, Def f _) _ = error ("Illegal struct binding lhs "++show (pp f))
matchField _ (_, p) _ = error ("Illegal struct pattern "++show (pp p))

-- What's the arity of the function?
arity :: HasCallStack => Value -> Int
arity (VClo _ n _ _) = n
arity (VPrim _ n _) = n
arity v = error ("No arity for "++show v)

-- Apply value to args.
apply :: HasCallStack => Value -> [Value] -> Value
apply (VCon cn vs0) vs = VCon cn (vs0 ++ vs)
apply (VPAp c vs0) vs = apply c (vs0 ++ vs)
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
appSat (VPrim _ _ (Prim f)) vs = f vs
appSat (VClo v _ ds env) vs = appDisjs v ds env vs

appDisjs :: HasCallStack => Var -> [([Pat], Exp)] -> Env -> [Value] -> Value
appDisjs f [] _ vs = error ("Match failure in appDisjs "++show f ++ " = " ++ show (pp vs))
appDisjs f ((p, e):ds) env vs =
  case matches p vs mempty of
    Just envm -> eval e (envm <> env)
    Nothing -> appDisjs f ds env vs

patLen :: Pat -> Int
patLen (Asc _ e _) = patLen e
patLen (App _ e es) = patLen e + length es
patLen _ = 1

eval :: HasCallStack => Env -> Exp -> Value
eval (Paren _ e) env = eval e env
eval (Asc _ e _) env = eval e env
eval (OpExp _ e) env = eval e env
eval (Id _ _ Var var) env =
  case M.lookup var env of
    Just val -> traceS var $ val
    Nothing -> error ("Unbound variable "++toString var)
eval (Id _ _ Con con) _ = VCon con []
eval a@(App _ _ []) _ = error ("Empty apply "++show (pp a))
eval (App _ e es) env = apply (eval e env) (map (`eval` env) es)
eval (Const _ const) _ = VConst const
eval (Wild _) _ = error "_ is a pat, not a valid expr"
eval e@(Arrow _ _ _) _ = error (show (pp e) ++ " is a type, not a valid expr")
eval e@(Ops _ _) _ = error (show (pp e) ++ " residual infix operators.")
eval (Fn s (Asc _ p _) e) env = eval (Fn s p e) env
eval (Fn s (App s' (Asc _ p _) ps) e) env = eval (Fn s (App s' p ps) e) env
eval (Fn s (App s' (App _ p ps) ps') e) env =
  eval (Fn s (App s' p (ps ++ ps')) e) env
eval (Fn _ (App _ p ps) e) env = VClo "<anon>" (1 + length ps) [(p:ps, e)] env
eval (Fn _ p e) env = VClo "<anon1>" 1 [([p], e)] env
eval (Tuple _ es) env = VTuple $ fmap (`eval` env) es
eval (List _ []) env = VCon "[]" []
eval (List s (e:es)) env = VCon "::" [eval e env, eval (List s es) env]
eval (Case _ e (_,es)) env =
  appDisjs "<case>" (map toDisj es) env [eval e env]
eval (If _ c t e) env =
  case eval c env of
    VCon "True" [] -> eval t env
    _ -> eval e env
eval (IfMatch _ p c t e) env =
  case match p (eval c env) mempty of
    Just env' -> eval t (env' <> env)
    Nothing -> eval e env
eval (Block b) env = evThings (groupDefs b) env
eval e _ = error ("eval: Unhandled expression\n  "++show (pp e)++"\n  "++show e)

evThings :: HasCallStack => Env -> [BlockThing] -> Value
evThings [] env = VTuple []
evThings [BTS m] env = VStruct ((`eval` env) <$> m)
evThings [D (BindExp e)] env = eval e env
evThings (Fns fs:ts) env = evThings ts env'
  where
    clos = fmap clo fs
    env' = M.fromList clos <> env
    clo (v, n, ves) = (v, VClo v n ves env')
evThings (D (BindExp e) : ts) env =
  eval e env `seq` evThings ts env
evThings (D (Def p e) : ts) env =
  let v = eval e env
  in  case match p v mempty of
        Nothing -> error ("Match failure "++show (pp p)++" = "++show (pp v))
        Just env' -> evThings ts (env' <> env)
evThings (t:ts) _ = error ("evThings: unexpected thing "++show (pp t))

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
    ds -> ds

groupDef :: HasCallStack => (Span, Def) -> [BlockThing] -> [BlockThing]
groupDef (s, BindExp (Asc s' (Paren _ e) t)) ts =
  groupDef (s, BindExp (Asc s' e t)) ts
groupDef (_, BindExp (Asc _ (Id _ _ _ var) t)) ts = ts
groupDef (_, Def (Id _ _ Var var) e) [] = [BTS (M.singleton var e)]
groupDef (_, Def (Id _ _ Var var) e) (BTS m:_) = [BTS (M.insert var e m)]
groupDef d (BTS m : _) = error (show (pp d) ++ " is not a struct binding")
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
groupDef (_, Data _ _) ts = ts
groupDef (_, Struct _ _) ts = ts
groupDef (_, Fix _ _ _) ts = ts
groupDef (_, d) ts = D d : ts

mkPrim :: (Var, Int, [Value] -> Value) -> (Var, Value)
mkPrim (v, n, f) = (v, VPrim v n (Prim f))

vBool :: Bool -> Value
vBool True = VCon "True" []
vBool False = VCon "False" []

i2 :: HasCallStack => (a -> Value) -> (Integer -> Integer -> a) -> [Value] -> Value
i2 v op [VConst (EInt a), VConst (EInt b)] = v (a `op` b)
i2 _ _ vs = error ("Bad args "++show (pp vs))

evalTop :: HasCallStack => Defs -> Value
evalTop ds = eval (Block ds) env0

valToList :: HasCallStack => Value -> [Value]
valToList (VCon "[]" []) = []
valToList (VCon "::" [h, t]) = h : valToList t
valToList v = error ("valToList: not a list "++show (pp v))

valToString :: HasCallStack => Value -> ByteString
valToString (VConst (EString s)) = s
valToString v = error ("valToString: not a string "++show (pp v))

strConcat :: HasCallStack => [Value] -> Value
strConcat [v] = VConst (EString (mconcat (valToString <$> valToList v)))

valToInt :: HasCallStack => Value -> Integer
valToInt (VConst (EInt i)) = i
valToInt v = error ("valToInt: not an int "++show (pp v))

env0 :: Env
env0 = M.fromList $ fmap mkPrim [
  ("prim", 1, \[p] -> env0 M.! (valToString p)),
  ("+", 2, i2 (VConst . EInt) (+)),
  ("-", 2, i2 (VConst . EInt) (-)),
  ("==", 2, i2 vBool (==)),
  ("<=", 2, i2 vBool (<=)),
  ("++", 2, \[VConst (EString a), VConst (EString b)] -> VConst (EString (a <> b))),
  ("putStr", 1, \[v] -> trace (toString (valToString v)) (VTuple [])), -- total hack, but "safe"
  ("strConcat", 1, strConcat),
  ("intToStr", 1, \[v] -> VConst $ EString $ fromString $ show $ valToInt v)
  ]
