{-# LANGUAGE OverloadedStrings, ApplicativeDo, PatternSynonyms, LambdaCase #-}
module Semantics where
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.BakerVec hiding (replicate)
import Data.ByteString(ByteString)
import Data.ByteString.UTF8(toString, fromString)
import AST
import Parse(SpanPos)
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

type Env = (Map Var (Known, Ofs), Int)
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

data Known
  = Unknown
  | KnownValue Value
  | KnownDesc Desc
  deriving (Eq, Show)

-- The information-theoretic join on Known
instance Semigroup Known where
  a <> b
    | a == b = a
  KnownValue (VObj a _) <> KnownValue (VObj b _)
    | a == b = KnownDesc a
  KnownValue (VPAp a _ _) <> KnownValue (VPAp b _ _)
    | a == b = KnownDesc a
  _ <> _ = Unknown

vClo :: HasCallStack => Var -> Int -> [([Pat], Exp)] -> EV
vClo f n ds = do
  (_, cf) <- appDisjs f ds (replicate n Unknown)
  let d = Desc f n (CloFun cf)
  pure $ (KnownDesc d, do
    vec <- getVec
    pure (VPAp d vec []))

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
  allSpans _ = []
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

instance IsAST Known where
  isValid _ = []
  span _ = noSpan
  allSpans _ = []
  fullParen t = t
  noParen t = t
  pp Unknown = PP.text "Unknown"
  pp (KnownValue v) = pp v
  pp (KnownDesc (Desc v n _)) = PP.text "<k" <+> PP.text (toString v) <+> (PP.int n <> PP.text ">")

-- Utilities not worth an import
fromMaybe :: a -> Maybe a -> a
fromMaybe d = maybe d id

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM d m = m >>= maybe d pure


-- Evaluation (environment) monads
type EI a = Reader Stack a -- Inner, actual evaluation.
type EO a = Reader (SpanPos, Env) a   -- Outer, environment and analysis.
type Ef b a = EO (Known, b -> EI a) -- Analysis parameterized by input
type EV = EO (Known, EI Value) -- Analyze and yield a value.

bindEnvWith :: ((Known, Ofs) -> (Known, Ofs) -> (Known, Ofs)) ->
               Var -> Known -> Env -> Env
bindEnvWith c i kn (env, k) =
  (M.insertWith c i (kn, k) env, k + 1)

lookupEnv :: HasCallStack => Var -> Env -> (Known, Ofs)
lookupEnv i (env, _) =
  fromMaybe (error ("Unbound variable "++toString i)) $
    M.lookup i env

withEnv :: Env -> EO a -> EO a
withEnv env = local (\(sp, _) -> (sp, env))

getEnv :: EO Env
getEnv = asks (snd @SpanPos) -- Whyyyyy??

getVec :: EI (Vec Value)
getVec = ask

findEnv :: HasCallStack => Var -> EV
findEnv i = do
  (kn, o) <- asks (lookupEnv i . snd)
  pure (kn, asks (! o))

-- Takes a computation that computes bindings and evaluates
-- it in an env containing those bindings, then evaluates
-- the rest in that environment.
fixEnv :: (EO [(Var, (Known, EI Value))]) -> EV -> EV
fixEnv a inner = do
  (sp, (env, k)) <- ask
  let vs = runReader a (sp, (env', k'))
      k' = k + length vs
      env' = M.fromList (zipWith (\(i, (kn, _)) n -> (i,(kn, n))) vs [k..]) <> env
  (kn, inner') <- withEnv (env', k') inner
  pure (kn, do
    vec <- getVec
    let vec' = foldl (\ve (_, (_, f)) -> push ve (runReader f vec')) vec vs
    local (const vec') inner')

-- Handles a *constant* binding (constructor def)
conBinding :: Var -> Value -> EV -> EV
conBinding i v r =
  local (fmap (bindEnvWith const i (KnownValue v))) $ do
    (kn, r') <- r
    pure (kn, local (`push` v) r')

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

type MO a = State (SpanPos, Env) a -- Outer: compute match environment, handle dups
type MI a = StateT Stack Maybe a -- Inner: decide match and bind variables
type M v a = MO (Mode, v -> MI a) -- Analyze, produce matcher for v yielding a.

matched :: Var -> Known -> M Value ()
matched i kn = do
  let collide _ _ = error ("Duplicate pattern bindings for variable "++toString i)
  modify $ (fmap (bindEnvWith collide i kn))
  pure (AlwaysSucceeds, \v -> modify (`push` v))

alwaysSucceed :: M a ()
alwaysSucceed = pure (AlwaysSucceeds, \_ -> pure ())

alwaysFail :: M a ()
alwaysFail = pure (AlwaysFails, \_ -> matchFail)

mayFail :: (v -> MI a) -> M v a
mayFail r = pure (MayFail, r)

matchFail :: MI a
matchFail = lift Nothing

-- Inject match into evaluation
withMatch :: HasCallStack => M b () -> EV -> Ef b (Maybe Value)
withMatch m t = do
  (sp, (env, k)) <- ask
  let ((mode, f), (_, (env', k'))) = runState m (sp, (mempty, k))
  withEnv (env' <> env, k') $ do
    (kn, t') <- t
    pure (kn, \v -> do
      vec <- getVec
      case execStateT (f v) vec of
        Just _ | mode == AlwaysFails -> error ("AlwaysFails succeeded!")
        Just vec' -> Just <$> local (const vec') t'
        Nothing | mode == AlwaysSucceeds -> error ("AlwaysSucceeds failed!")
        Nothing -> pure Nothing)

-- Assumes length ps == length vs
matches :: HasCallStack => [Pat] -> [Known] -> M [Value] ()
matches [p] [k] = do
  (mode, f) <- match p k
  pure (mode, \case
    [v] -> f v
    vs -> error ("Pat len mismatch "++show (pp p)++" and "++showsPp vs))
matches [] _ = error "Empty pats"
matches ps ks = do
  (mode, ms) <- matches' ps ks
  pure (mode, \vs -> do
    vec <- get
    case execStateT (ms vs) vec of
      Just vec' ->
        traceSt
          (showsPp ps++" match "++showsPp vs)
          (put vec')
      Nothing -> matchFail)

matches' :: HasCallStack => [Pat] -> [Known] -> M [Value] ()
matches' ps ks = do
  let n = length ps
  fs <- zipWithM match' ps ks
  pure (foldl1 (<>) (map fst fs), \vs ->
    if length vs == n then
      zipWithM_ (($) . snd) fs vs
    else
      error ("Pat len mismatch "++showsPp ps++" and "++showsPp vs))

-- Match Pat with Value in Env and yield fresh Env or Nothing on failure
match :: HasCallStack => Pat -> Known -> M Value ()
match p kn = do
  (mode, f) <- match' p kn
  pure (mode, \val -> do
    vec <- get
    case execStateT (f val) vec of
      Just vec' -> traceSt (showPp p++" matches "++showPp val) (put vec')
      Nothing -> matchFail)

match' :: HasCallStack => Pat -> Known -> M Value ()
match' (Paren _ p) kn = match p kn
match' (Asc _ p _) kn = match' p kn
match' (Wild _) _ = alwaysSucceed
match' (Id _ _ Var var) kn = matched var kn
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
match' p@(App _ (Id _ _ Con con) as) kn = do -- Can't avoid the match now
  let len = length as
      kns = const Unknown <$> as
  (m, fs) <- matches' as kns
  let mode AlwaysSucceeds (KnownDesc (Desc con' i _)) | con == con' && i == len = AlwaysSucceeds
      mode _ (KnownDesc (Desc con' i _)) | con /= con' || i /= len = AlwaysFails
      mode _ _ = MayFail <> m
  pure (mode m kn, \case
    v@(VCon cn n rs)
      | len /= length rs -> error ("Obj ctor arity "++show n++" mismatch "++showPp v)
      | len == n && con == cn -> fs rs
      | len /= n && con == cn -> error ("Constructor pat expected arity "++show n ++ ": "++showPp p)
    _ -> matchFail)
match' p@(App _ _ _) _ = error ("No constructor at head of pattern "++showPp p)
match' p _ = error ("Unrecognized pattern "++showPp p)

matchField :: HasCallStack => (Span, Def) -> M (Map FieldName Value) ()
matchField (s, BindExp p) = matchField (s, Def p p)
matchField (_, Def (Id _ _ Var fn) p) = do
  (mode, f) <- match' p Unknown
  pure (mode, \fs -> lift (M.lookup fn fs) >>= f)
matchField (_, Def f _) = error ("Illegal struct binding lhs "++showPp f)
matchField (_, p) = error ("Illegal struct pattern "++showPp p)

isKnownValue :: Known -> Bool
isKnownValue (KnownValue _) = True
isKnownValue _ = False

knownDesc :: Known -> Maybe Desc
knownDesc (KnownDesc d) = Just d
knownDesc (KnownValue (VDesc d)) = Just d
knownDesc _ = Nothing

-- Apply value to args.
apply :: HasCallStack => (Known, EI Value) -> [(Known, EI Value)] -> (Known, EI Value)
apply (kn, f) as = app (knownDesc kn)
  where
    len = length as
    app Nothing = applyUnknown f as
    app (Just d@(Desc _ a _))
      | a == len = applyKnown kn d f as
      | a >  len = applyUnknown f as
      | otherwise = do
          let (bs, cs) = splitAt a as
          apply (applyKnown kn d f bs) cs

applyKnown :: HasCallStack => Known -> Desc -> EI Value -> [(Known, EI Value)] -> (Known, EI Value)
applyKnown (KnownValue (VDesc (Desc _ _ (CloFun f)))) _ _ as
  | all (isKnownValue . fst) as = do -- Constant fold!
      let r = runReader (f [ v | (KnownValue v, _) <- as]) mempty
      (KnownValue r, pure r)
  | otherwise =
    (Unknown, do
      vs <- mapM snd as
      f vs)
applyKnown _ (Desc i _ (CloFun f)) v as =
  (Unknown, do
    v' <- v
    vs <- mapM snd as
    case v' of
      VDesc (Desc i' _ _)
        | i == i' -> local (const mempty) $ f vs
      VPAp (Desc i' _ _) vec bs
        | i == i' -> local (const vec) $ f (bs <> vs)
      _ -> error ("applyKnown "++toString i++": bad closure "++showPp v'))

applyUnknown :: HasCallStack => EI Value -> [(Known, EI Value)] -> (Known, EI Value)
applyUnknown f as =
  (Unknown, do
    v <- f
    vs <- mapM snd as
    applyInner v vs)

applyInner :: HasCallStack => Value -> [Value] -> EI Value
applyInner (VDesc d) vs = appWithDesc d mempty (length vs) vs
applyInner (VPAp d vec as) bs = do
  let vs = as <> bs
  appWithDesc d vec (length vs) vs
applyInner v _ = error ("apply: bad closure "++showPp v)

-- Apply function to args (arities given)
appWithDesc :: HasCallStack => Desc -> Stack -> Int -> [Value] -> EI Value
appWithDesc d@(Desc _ n (CloFun f)) vec nv vs
  | n > nv = pure $ VPAp d vec vs
  | n == nv = local (const vec) $ f vs
  | otherwise = do
      let (vs', vs'') = splitAt n vs
      f' <- local (const vec) (f vs')
      applyInner f' vs''

appDisjs :: HasCallStack => Var -> [([Pat], Exp)] -> [Known] -> Ef [Value] Value
appDisjs f ds knp = do
  pes <- mapM (\(ps, e) -> withMatch (matches ps knp) (eval e)) ds
  let kn = foldr1 (<>) (map fst pes)
      ms = map snd pes
  pure (kn, \vs -> do
          let oneMatch [] = error ("Match failure in "++show f ++ " " ++ showPp vs)
              oneMatch (m:mr) = fromMaybeM (oneMatch mr) (m vs)
          oneMatch ms)

eval :: HasCallStack => Exp -> EV
eval (Paren _ e) = eval e
eval (Asc _ e _) = eval e
eval (OpExp _ e) = eval e
eval (Id _ _ _ i) = findEnv i
eval a@(App _ _ []) = error ("Empty apply "++showPp a)
eval (App _ e es) = do
  e' <- eval e
  es' <- mapM eval es -- Effects need to be l -> r
  pure $ apply e' es'
eval (Const _ c) = pure (KnownValue $ VConst c, pure $ VConst c)
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
  let d = cDesc "()" (length es')
      kn | null es = KnownValue (VDesc d)
         | otherwise = KnownDesc d
  pure (kn, VObj d <$> mapM snd es')
eval (List _ []) = do
  let v = VCon0 "[]"
  pure (KnownValue v, pure v)
eval (List s (e:es)) = eval (App s (Id s Op Con "::") [e, List s es])
eval (Case _ e (_,es)) = do
  (ekn, e') <- eval e
  (kn, m) <- appDisjs "<case>" (map toDisj es) [ekn]
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
      pure (tkn <> ekn, do
        c' >>= \case
          VCon0 "True" -> t'
          VCon0 "False" -> e'
          v -> error ("If non-boolean "++showPp v))
    _ -> error ("If statically non-boolean "++showPp ckn)
eval (IfMatch _ p c t e) = do
  (ckn, c') <- eval c
  (tkn, tm) <- withMatch (match p ckn) (eval t)
  (ekn, e') <- eval e
  pure (tkn <> ekn, do
    v <- c'
    fromMaybeM e' (tm v))
eval (Block b) = evThings (groupDefs b)
eval e = error ("eval: Unhandled expression\n  "++showPp e++"\n  "++show e)

evThings :: HasCallStack => [BlockThing] -> EV
evThings [] = do
  let v = VStruct mempty
  pure (KnownValue v, pure v)
evThings [BTS m] = do
  ms <- traverse eval m
  pure (Unknown, VStruct <$> sequenceA (snd <$> ms))
evThings (D (BindExp (Asc _ (Id _ _ _ _) _)) : ts@(_:_)) = evThings ts
evThings [D (BindExp e)] = eval e
evThings (Fns fs:ts) = fixEnv (traverse clo fs) (evThings ts)
  where clo (v, n, ves) = (v,) <$> vClo v n ves
evThings (D (BindExp e) : ts) = do
  (_, e') <- eval e
  (kn, r) <- evThings ts
  pure (kn, e' *> r)
evThings (D (Def p e) : ts) = do
  (ekn, e') <- eval e
  (kn, m) <- withMatch (match p ekn) (evThings ts)
  pure (kn, do
    v <- e'
    fromMaybeM (error ("Match failure "++showPp p++" = "++showPp v)) (m v))
evThings (D (Fix _ _ _) : ts) = evThings ts
evThings (D (Data _ (_,ds)) : ts) = foldr addCon (evThings ts) ds
evThings (D (Struct _ _) : ts) = evThings ts
evThings (t:_) = error ("evThings: unexpected thing "++showPp t)

-- Store arity information about constructors to env
addCon :: HasCallStack => (Span, Def) -> EV -> EV
addCon (_, BindExp e) = addCon' e
addCon (_, d) = error ("addCon: not a constructor def "++showPp d)

addCon' :: HasCallStack => Exp -> EV -> EV
addCon' (Paren _ e) = addCon' e
addCon' (Id _ _ Con c) = conBinding c (VCon0 c)
addCon' (App s (Paren _ e) as) = addCon' (App s e as)
addCon' (App s (App _ e as) as') = addCon' (App s e (as <> as'))
addCon' (App _ (Id _ _ Con c) as) = conBinding c (cCon c (length as))
addCon' (Asc s (Paren _ e) t) = addCon' (Asc s e t)
addCon' (Asc _ (Id _ _ Con c) t) = conBinding c (cCon c (typeArity t))
addCon' (List _ []) = conBinding "[]" (VCon0 "[]")
addCon' e = error ("addCon': not a constructor def "++showPp e)

typeArity :: HasCallStack => Exp -> Int
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

cDesc :: ConName -> Int -> Desc
cDesc v i =
  case cCon v i of
    VDesc d -> d
    r -> error ("cDesc: Unexpected value "++showPp r)

cCon :: ConName -> Int -> Value
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
  allSpans (D d) = allSpans d
  allSpans (BTS e) = allSpans (M.elems e)
  allSpans (Fns fs) = [ s | (_, _, ds) <- fs, (ps, e) <- ds, s <- allSpans ps <> allSpans e]
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

evalTop :: HasCallStack => (SpanPos, Defs) -> Value
evalTop (sp, ds) =
  let (env, vec) = expand env0
  in runReader (snd $ runReader (eval $ Block ds) (sp, env)) vec

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
  foldl (\((env, k), vec) (i, v) -> ((M.insert i (KnownValue v, k) env, k+1), push vec v))
        ((mempty, 0), mempty)
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
