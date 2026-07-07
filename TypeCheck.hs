{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}
module TypeCheck(typecheckTop) where
import AST
import Parse(SpanPos, spanPrefix)
import Primitive(env0)
import SemUtil(mkRhs, toDisj)
import Value(Val)

import Control.Monad
import Control.Monad.State
import Data.BakerVec as BV hiding (replicate)
import Data.ByteString.Char8(replicate)
import Data.ByteString.UTF8(fromString, toString)
import Data.Foldable
import Data.Map as M hiding ((!), null, foldl, foldr)
import Data.Set as S hiding (null, foldl, foldr, fold)
import GHC.Stack(HasCallStack)
import Prelude hiding (span, replicate)
import Text.PrettyPrint hiding ((<>))

import Debug.Trace(trace)

traceBind :: Bool
traceBind = False

traceUnify :: Bool
traceUnify = False

traceFunc :: Bool
traceFunc = False

tracew :: Bool -> [String] -> a -> a
tracew f w v
  | f = trace (unwords w) v
  | otherwise = v

traceb :: [String] -> a -> a
traceb = tracew traceBind

traceu :: [String] -> a -> a
traceu = tracew traceUnify

tracef :: [String] -> a -> a
tracef = tracew traceFunc

type TVar = Var
type UVar = Int

data Typ
  = UV Span UVar
  | RV Span Var
  | TTuple Span Int
  | Type
  | TArrow Span UVar UVar
  | TApp Span [UVar]
  | TScheme Span [UVar] UVar
  deriving (Eq, Show)

tySpan :: Typ -> Span
tySpan (UV s _) = s
tySpan (RV s _) = s
tySpan (TTuple s _) = s
tySpan Type = noSpan
tySpan (TArrow s _ _) = s
tySpan (TApp s _) = s
tySpan (TScheme s _ _) = s

data TCState = TCState {
    venv_ :: Map Var UVar,
    tvs_ :: Map TVar UVar,
    u_ :: Vec Typ,
    lvl_ :: Vec UVar, -- Lowest UVar that reaches.
    errs_ :: [([Span], String)]
  }
  deriving (Eq, Show)

type TCM a = State TCState a

scope :: TCM a -> TCM a
scope act = do
  st <- get
  r <- act
  st' <- get
  put (st' { venv_ = venv_ st, tvs_ = tvs_ st })
  pure r

-- Look up regular program variables
lookupV :: Span -> Var -> TCM UVar
lookupV s v = do
  venv <- gets venv_
  case M.lookup v venv of
    Nothing -> typeError [s] ("Unbound variable "++showPp v) >> newUV s
    Just uv -> pure uv

bindV :: HasCallStack => Var -> UVar -> TCM ()
bindV v uv = do
  p <- ppTy uv
  traceb ["bind", showPp v, "=", show uv, "=", showPp p] $
    modify (\st -> st { venv_ = M.insert v uv (venv_ st) } )

-- Create rigid var that must be undefined
brandNewRV :: String -> Span -> Var -> TCM UVar
brandNewRV msg s v = do
  tvs <- gets tvs_
  case M.lookup v tvs of
    Nothing -> newRV s v
    Just uv -> typeError [s] msg >> pure uv

newRV :: HasCallStack => Span -> Var -> TCM UVar
newRV s v = do
  rv <- newUV' (RV s v)
  modify (\st -> st { tvs_ = M.insert v rv (tvs_ st) } )
  pure rv

-- Create anonymous RV.  Var should start with "$".
anonRV :: Span -> Var -> TCM UVar
anonRV s v = newUV' (RV s v)

-- Get extant RV
getRV :: Span -> TVar -> TCM UVar
getRV s tv = do
  m <- gets (M.lookup tv . tvs_)
  case m of
    Just uv -> pure uv
    Nothing -> typeError [s] ("Why doesn't "++showPp tv++" exist?") >> newRV s tv

-- Find or create rigid var
rvFor :: Span -> TVar -> TCM UVar
rvFor s tv = do
  m <- gets (M.lookup tv . tvs_)
  case m of
    Just uv -> pure uv
    Nothing -> newRV s tv

-- Create unification variables
newUVf :: (UVar -> Typ) -> TCM UVar
newUVf mk = do
  let trans st = do
        let u = u_ st
            lvl = lvl_ st
            v = length u
            t = mk v
            u' = push u t
            lvl' = push lvl v
        (v, st{ u_ = u', lvl_ = lvl' })
  state trans

newUV :: Span -> TCM UVar
newUV = newUVf . UV

newUV' :: Typ -> TCM UVar
newUV' = newUVf . const

-- Assign unification variable
assignU :: UVar -> Typ -> TCM UVar
assignU uv t = do
  modify (\st -> st{ u_ = writeVec (u_ st) uv t })
  pure uv

-- Get direct uvar and typ for possibly indirect uvar.
getU :: HasCallStack => UVar -> TCM (UVar, Typ)
getU uv = do
  t <- gets ((! uv) . u_)
  case t of
    UV s u | u /= uv -> do
      tup@(uv', _) <- getU u
      when (u /= uv') (assignU uv (UV s uv') >> pure ())
      pure tup
    _ -> pure (uv, t)

-- Get level of uvar
levelU :: UVar -> TCM UVar
levelU uv =
  gets ((! uv) . lvl_)

-- Adjust level of b to match a.
adjustLevel :: UVar -> UVar -> TCM ()
adjustLevel a b = do
      modify (\st -> do
        let lvl = lvl_ st
            la = lvl!a
            lb = lvl!b
            lvl' = if la < lb then writeVec lvl b la else lvl
        st { lvl_ = lvl' })

typeError :: [Span] -> String -> TCM ()
typeError s err = do
  modify (\st -> st{ errs_ = (s, err) : errs_ st })

------------------------------------------------------------
-- Var vs Typ handling

uvFunc :: (UVar -> Typ -> TCM a) -> UVar -> TCM a
uvFunc f = \uv -> uncurry f =<< getU uv

unTy :: UVar -> TCM Exp
unTy = uvFunc ut where
  ut uv (UV s _) = pure $ Id s Ident Var ("$uv" <> fromString (show uv))
  ut uv (RV s "$rv") = pure $ Id s Ident Var ("$rv" <> fromString (show uv))
  ut _  (RV s i) -- TODO: sus
    | isVar i = pure $ Id s Ident Var i
    | otherwise = pure $ Id s Ident Con i
  ut _ (TTuple s 0) = pure $ Id s Ident Con "()"
  ut _ (TTuple s 1) = pure $ Id s Ident Con "(_,)"
  ut _ (TTuple s n) = pure $ Id s Ident Con ("(" <> replicate (n-1) ',' <> ")")
  ut _ Type = pure $ Id noSpan Ident Con "Type"
  ut _ (TArrow s a b) = do
    liftA2 (Arrow s) (unTy a) (unTy b)
  ut _ (TApp s as) = do
    App s <$> traverse unTy as
  ut _ (TScheme _ _ v) = unTy v

ppTy :: UVar -> TCM Doc
ppTy = ppTy0 False where
  ppTy0 f = uvFunc (ppTy' f)
  parenIf True d = parens <$> d
  parenIf _ d = d
  ppTy' :: Bool -> UVar -> Typ -> TCM Doc
  ppTy' _ _ (UV _ v) = pure ("$uv" <> int v)
  ppTy' _ uv (RV _ "$rv") = pure ("$rv" <> int uv)
  ppTy' _ _ (RV _ v) = pure (pp v)
  ppTy' _ _ (TTuple _ 0) = pure "()"
  ppTy' _ _ (TTuple _ 1) = pure "(_,)"
  ppTy' _ _ (TTuple _ n) = pure $ parens $ pp (replicate (n-1) ',')
  ppTy' _ _ Type = pure "Type"
  ppTy' f _ (TArrow _ a b) = parenIf f $ do
    a' <- ppTy0 True a
    b' <- ppTy b
    pure $ sep [hsep [a', "->"], b']
  ppTy' f _ (TApp _ as) = parenIf f $ do
    pas <- traverse (ppTy0 True) as
    case pas of
      [] -> error "Empty app"
      (pa:pas') ->
        pure $ sep (pa : (nest 2 <$> pas'))
  ppTy' f _ (TScheme _ vs t) = parenIf f $ do
    vs' <- traverse (ppTy0 True) vs
    t' <- ppTy t
    pure $ sep [hsep vs' <> ".", t']

------------------------------------------------------------
-- Instantiation of type schemes

-- Instantiate a type scheme with fresh rigid vars
rinst :: HasCallStack => UVar -> TCM UVar
rinst = uvFunc $ \uv0 ty0 ->
  case ty0 of
    TScheme s rts t -> do
      let oneV :: UVar -> TCM (UVar, UVar)
          oneV uv = do
            (uv', ty) <- getU uv
            (uv',) <$>
              case ty of
                RV s' v | uv == uv' -> newRV s' v
                UV s' _ | uv == uv' -> anonRV s' "$rv"
                _ -> do
                  let s' = tySpan ty
                  typeError [s, s'] "Nonsensical rigid type"
                  anonRV s' "$errv"
      m <- traverse oneV rts
      snd <$> inst' (M.fromList m) t
    _ -> pure uv0

-- Instantiate a type scheme with unification vars
inst :: UVar -> TCM UVar
inst = uvFunc $ \uv ty ->
  case ty of
    TScheme s rts t -> do
      m <- traverse (\uv' -> (uv',) <$> newUV s) rts
      snd <$> inst' (M.fromList m) t
    _ -> pure uv

-- Inner loop: instantiate the type represented by one UVar
inst' :: Map UVar UVar -> UVar -> TCM (Map UVar UVar, UVar)
inst' m uv = do
  (uv', ty) <- getU uv
  case M.lookup uv' m of
    Nothing -> instT m uv' ty
    Just t -> pure (m, t)

-- Inner loop': instantiate the Typ bound to a uv.
instT :: Map UVar UVar -> UVar -> Typ -> TCM (Map UVar UVar, UVar)
instT m uv (UV _ uv')
  | uv == uv' = pure (m, uv)
  | otherwise = inst' m uv'
instT m uv (RV _ _) = pure (m, uv)
instT m uv (TTuple _ _) = pure (m, uv)
instT m uv t@(TArrow s a b) = do
  (m1, a') <- inst' m a
  (m2, b') <- inst' m1 b
  instWith s m2 uv t (TArrow s a' b')
instT m uv t@(TApp s uvs) = do
  let act uv' tact = do
        (mm, uu) <- tact
        fmap (:uu) <$> inst' mm uv'
  (m', uvs') <- foldr act (pure (m, [])) uvs
  instWith s m' uv t (TApp s uvs')
instT m uv t@(TScheme s rs uv') = do
  (m', uv'') <- inst' m uv'
  instWith s m' uv t (TScheme s rs uv'')
instT m uv Type = pure (m, uv)

-- Instantiate uvar with the given instatiated (after) type.
instWith :: Span -> Map UVar UVar -> UVar -> Typ -> Typ -> TCM (Map UVar UVar, UVar)
instWith _ m uv t0 t
  | t0 == t = pure (M.insert uv uv m, uv)
  | otherwise = do
      r <- newUV' t
      pure (M.insert uv r m, r)

------------------------------------------------------------
-- Unification

(===) :: HasCallStack => UVar -> UVar -> TCM Bool
a === b | a == b = pure True
a === b = do
  (ua, _) <- getU a
  (ub, _) <- getU b
  if ua /= ub then do
    sa <- ppTy a
    sb <- ppTy b
    r <- (a ==== b)
    let q = if r then "===" else "=/="
    su <- ppTy a
    traceu [showPp su, "=", show a, "=", show ua, "=", showPp sa, q,
                    show b, "=", show ub, "=", showPp sb] pure r
  else
    pure True

(====) :: HasCallStack => UVar -> UVar -> TCM Bool
a ==== b = do
  (ua, a') <- getU a
  (ub, b') <- getU b
  case compare ua ub of
    LT -> unify ua a' ub b'
    EQ -> pure True
    GT -> unify ub b' ua a'

occurs :: Span -> UVar -> UVar -> Typ -> TCM Bool
occurs s uv uv0 typ = do
  let occ' :: Set UVar -> UVar -> TCM (Set UVar, Bool)
      occ' seen uv'
        | uv' `S.member` seen = pure (seen, False)
        | otherwise = uvFunc (const (occ (S.insert uv seen))) uv'
      occ :: Set UVar -> Typ -> TCM (Set UVar, Bool)
      occ seen (UV _ uv') = do
        adjustLevel uv uv'
        pure (seen, uv == uv')
      occ seen (RV _ _) = pure (seen, False)
      occ seen (TTuple _ _) = pure (seen, False)
      occ seen Type = pure (seen, False)
      occ seen (TArrow _ a b) = orr (`occ'` a) (`occ'` b) seen
      occ seen (TApp _ ts) =
        foldr orr (\see -> pure (see, False)) (fmap (flip occ') ts) seen
      occ seen (TScheme _ _ uv') = occ' seen uv'
      orr f g seen = do
        (seenf, fr) <- f seen
        if fr then
          pure (seenf, True)
        else g seenf
  (_, r) <- occ' mempty uv0
  when r $
    typeError [s, tySpan typ] "Attempt to create a circular type"
  pure r

unify :: HasCallStack => UVar -> Typ -> UVar -> Typ -> TCM Bool
unify ua ta _ (UV s ub) = do -- Prefer to point higher to lower
  nocc <- not <$> occurs s ub ua ta
  uDone ua s ub nocc
unify _ (UV s ua) ub tb = do -- Move higher to lower to point hi -> low
  nocc <- not <$> occurs s ua ub tb
  when nocc $ do
    assignU ua tb
    assignU ub (UV (tySpan tb) ua)
    pure ()
  pure nocc
unify _ (RV _ _) _ (RV _ _) = pure False -- since UV itself participates in RV naming
unify ua Type ub Type = uDone ua noSpan ub True
unify ua (TTuple s a) ub (TTuple _ b) | a == b = do
  assignU ub (UV s ua)
  pure True
unify ua (TArrow _ la ra) ub (TArrow sb lb rb) =
  uDone ua sb ub =<< liftA2 (&&) (la ==== lb) (ra ==== rb)
unify ua (TApp sa as) ub (TApp sb bs) =
  uDone ua sb ub =<< unifyApp sa (reverse as) sb (reverse bs)
unify _ (TScheme s _ _) _ _ =
  error "Scheme unification unimplemented 1" $
  typeError [s] "Scheme unification unimplemented" >> pure False
unify _ _ _ (TScheme s _ _) =
  error "Scheme unification unimplemented 2" $
  typeError [s] "Scheme unification unimplemented" >> pure False
unify _ _ _ _ = pure False

uDone :: UVar -> Span -> UVar -> Bool -> TCM Bool
uDone _  _ _ False = pure False
uDone ua s ub True = assignU ub (UV s ua) >> pure True -- Point higher to lower

unifyApp :: Span -> [UVar] -> Span -> [UVar] -> TCM Bool
unifyApp sa [] _ _ = typeError [sa] "Empty type app" >> pure False
unifyApp _ _ sb [] = typeError [sb] "Empty type app" >> pure False
unifyApp _ [a] _ [b] = a ==== b
unifyApp _ [a] sb bs = do
  uv <- newUV' (TApp sb bs)
  a ==== uv
unifyApp sa as _ [b] = do
  uv <- newUV' (TApp sa as)
  b ==== uv
unifyApp sa (a:as) sb (b:bs) =
  liftA2 (&&) (a ==== b) (unifyApp sa as sb bs)

------------------------------------------------------------
-- Generalization

-- Generalize free UVars generated within a given computation.
-- We do this by instantiating them with rigid vars and collecting
-- the set of rigid vars.
gen :: HasCallStack => Span -> TCM UVar -> TCM UVar
gen s act = do
  minUv <- gets (length . u_)
  uv <- act
  vs <- gen' minUv uv
  mkScheme s vs uv

gens :: HasCallStack => [Span] -> TCM [UVar] -> TCM [UVar]
gens spans act = do
  minUv <- gets (length . u_)
  uvs <- act
  vss <- traverse (gen' minUv) uvs
  sequence $ zipWith3 mkScheme spans vss uvs

mkScheme :: Span -> Set UVar -> UVar -> TCM UVar
mkScheme s vs uv
  | null vs = pure uv
  | otherwise = newUV' (TScheme s (S.toList vs) uv)

gen' :: HasCallStack => UVar -> UVar -> TCM (Set UVar)
gen' minUv uv0 = uvFunc g uv0 where
  g uv _ | uv < minUv = pure mempty
  g uv typ = do
    l <- levelU uv
    if l < minUv then
      pure mempty
    else
      g' uv typ
  g' uv (UV s _) = do
    assignU uv (RV s "$rv")
    pure (S.singleton uv)
  g' uv (RV _ _) = pure (S.singleton uv)
  g' _  (TTuple _ _) = pure mempty
  g' _  Type = pure mempty
  g' _  (TArrow _ a b) =
    (<>) <$> gen' minUv a <*> gen' minUv b
  g' _  (TApp _ vs) = fold <$> traverse (gen' minUv) vs
  g' _  (TScheme _ vs u) = do
    vs' <- gen' minUv u
    pure (foldr S.delete vs' vs)

------------------------------------------------------------
-- AST traversals (type creation and checking)

tupleType :: Span -> Int -> TCM UVar
tupleType s n = newUV' (TTuple s n)

expectTuple :: Span -> Int -> UVar -> Typ -> TCM UVar
expectTuple s n uv (TTuple _ n')
  | n == n' = pure uv
  | otherwise = do
      typeError [s] (" tuple size mismatch, got "++show n++" vs "++show n')
      newUV s
expectTuple s n uv (UV _ _) =
  assignU uv (TTuple s n)
expectTuple s n uv _ = do
  st <- ppTy uv
  typeError [s] (" got "<>show n<>" tuple vs "<>showPp st)
  newUV s

-- Expect a list type, return the type and its element type.
expectList :: Span -> UVar -> Typ -> TCM (UVar, UVar)
expectList s uv (TApp _ [l0, e]) = do
  l <- getRV s "[]"
  ok <- l === l0
  if ok then
    pure (uv, e)
  else
    mkList s uv
expectList s uv _ = mkList s uv

-- Expect an arrow type, return the type and its operand and result.
expectArrow :: HasCallStack => Span -> UVar -> Typ -> TCM (UVar, UVar, UVar)
expectArrow _ uv (TArrow _ a b) = pure (uv, a, b)
expectArrow s uv _ = do
  a <- newUV s
  b <- newUV s
  r <- newUV' (TArrow s a b)
  r' <- tcFin s " more arguments than expected " r uv
  return (r', a, b)

mkList :: Span -> UVar -> TCM (UVar, UVar)
mkList s uv = do
  l <- getRV s "[]"
  e <- newUV s
  uv' <- newUV' (TApp s [l, e])
  ruv <- tcFin s " got list " uv' uv
  pure (ruv, e)

-- Given an Exp representing a type, intern it.
mkTy :: Exp -> TCM UVar
mkTy (Asc _ _ t) = mkTy' t
mkTy t = mkTy' t

mkTy' :: Exp -> TCM UVar
mkTy' (Id s _ _ v) = rvFor s v
mkTy' (App s as) = do
  as' <- traverse mkTy' as
  newUV' (TApp s as')
mkTy' (Asc _ t _k) = mkTy' t
mkTy' (Arrow s a b) = do
  a' <- mkTy' a
  b' <- mkTy' b
  newUV' (TArrow s a' b')
mkTy' (Wild s) = do
  newUV s
mkTy' (Paren _ e) = mkTy' e
mkTy' (Tuple s []) = tupleType s 0
mkTy' (Tuple s es) = do
  tt <- tupleType s (length es)
  es' <- traverse mkTy' es
  newUV' (TApp s (tt : es'))
mkTy' (List s []) = mkTy' (Id s Ident Con "[]")
mkTy' (List s [t]) = mkTy' (App s [Id s Ident Con "[]", t])
mkTy' (List s _) = typeError [s] "Too many arguments to list type" >> newUV s
mkTy' (OpExp _ e) = mkTy' e
mkTy' (Block (s, _)) = typeError [s] "Record in type is TODO" >> newUV s
mkTy' (Dot s _) = typeError [s] "Dot in type is TODO" >> newUV s
mkTy' (Const s _) = typeError [s] "Constant in type is TODO" >> newUV s
mkTy' (Fn s _) = typeError [s] "Lambda in type" >> newUV s
mkTy' e@(Ops _ _) = typeError [span e] "Unresolved infix ops in type" >> newUV (span e)
mkTy' (Case s _ _) = typeError [s] "Case in type" >> newUV s
mkTy' (If s _ _ _) = typeError [s] "if in type" >> newUV s
mkTy' (IfMatch s _ _ _ _) = typeError [s] "if <- in type" >> newUV s
mkTy' (Do s _ _ _) = typeError [s] "Do in type" >> newUV s
mkTy' (Assign s _ _) = typeError [s] "Assign in type" >> newUV s

cleanTy :: Exp -> Exp
cleanTy (App s as) =
  case cleanTy <$> as of
    (App _ as') : as'' -> App s (as' <> as'')
    as' -> App s as'
cleanTy (Asc _ t _k) = cleanTy t  -- TODO: clearly this is relevant to kind checking.
cleanTy (Arrow s a b) = Arrow s (cleanTy a) (cleanTy b)
cleanTy (Paren _ t) = cleanTy t
cleanTy (Tuple s es) = Tuple s (cleanTy <$> es)
cleanTy (List s []) = Id s Ident Con "[]"
cleanTy (List s [t]) = App s [Id s Ident Con "[]", cleanTy t]
cleanTy (List s es) = List s (cleanTy <$> es)
cleanTy (OpExp _ e) = cleanTy e
cleanTy e = e

cleanCon :: Exp -> Exp
cleanCon (App s (a:as)) = do
  let as' = cleanTy <$> as
  case cleanCon a of
    (App _ as'') -> cleanCon (App s (as'' <> as'))
    c -> App s (c : as')
cleanCon (Asc s c t) = Asc s (cleanCon c) (cleanTy t)
cleanCon (Paren _ e) = cleanCon e
cleanCon (OpExp _ e) = cleanCon e
cleanCon e = e

constTypeName :: Constant -> TVar
constTypeName (EInt _) = "Int"
constTypeName (EFloat _) = "Double"
constTypeName (EChar _) = "Char"
constTypeName (EString _) = "String"

-- Type check an expr
type TC = Exp -> UVar -> TCM UVar

tcExpr :: HasCallStack => TC
tcExpr e = uvFunc (tcExpr' e)

tcExpr' :: HasCallStack => Exp -> UVar -> Typ -> TCM UVar
tcExpr' e uv (TScheme _ _ _) = do
  uv' <- rinst uv
  tcExpr e uv'
tcExpr' (Id s _ _ i) uv _ =
  tcId s "identifier doesn't match expected type " i uv
tcExpr' (App s [e]) uv typ = do
  typeError [s] "Singleton application"
  tcExpr' e uv typ
tcExpr' (App s es) uv _ = do
  tcApp tcExpr s es uv
tcExpr' (Fn s (_, b)) uv _ = uncurry (tcFun s uv) (mkRhs b)
tcExpr' (Asc s e t) uv _ = do
  uvt <- mkTy t
  uvt' <- tcFin s "Signature doesn't match expected type " uvt uv
  tcExpr e uvt'
tcExpr' (Arrow s _ _) uv _ = do
  typeError [s] "Unexpected arrow expression"
  pure uv
tcExpr' (Wild s) uv _ = do
  typeError [s] "Wildcard in expression"
  pure uv
tcExpr' (Const s c) uv _ =
  tcFin s " expected " uv =<< getRV s (constTypeName c)
tcExpr' e@(Ops _ _) uv _ = do
  typeError [span e] "Unresolved infix ops"
  pure uv
tcExpr' (Case s e (_, ds)) uv _ = do
  euv <- tcExpr e =<< newUV s
  tcMatch [euv] (fmap toDisj ds) uv
tcExpr' (If s p t e) uv _ = do
  bool <- rvFor s "Bool"
  tcExpr p bool
  tcExpr t uv
  tcExpr e uv
  pure uv
tcExpr' (IfMatch s p d t e) uv _ = do
  uvp <- tcExpr d =<< newUV s
  scope $ do
    tcPat p uvp
    tcExpr t uv
    tcExpr e uv
    pure uv
tcExpr' (Dot s _) uv _ = do
  typeError [s] "Dot typing is TODO"
  pure uv
tcExpr' (Paren _ e) uv ty = tcExpr' e uv ty
tcExpr' (Tuple s es) uv ty = tcTuple tcExpr s es uv ty
tcExpr' (List s es) uv ty = tcList tcExpr s es uv ty
tcExpr' (Do s p e ds) uv _ = do
  tp <- tcExpr e =<< newUV s
  scope $ do
    _ <- tcPat p tp
    tcDefs ds uv
tcExpr' (Assign s _ _) uv _ = do
  typeError [s] " assign typechecking TODO"
  pure uv
tcExpr' (Block bs) uv _ = tcDefs bs uv
tcExpr' (OpExp _ e) uv ty = tcExpr' e uv ty

tcFin :: HasCallStack => Span -> String -> UVar -> UVar -> TCM UVar
tcFin s msg got want = do
  ok <- got === want
  unless ok $ do
    pg <- ppTy got
    pw <- ppTy want
    typeError [s] (msg <> showPp pg <> " vs " <> showPp pw)
  pure got

-- tcPat also binds variables
tcPat :: TC
tcPat e = uvFunc (tcPat' e)

tcPat' :: Exp -> UVar -> Typ -> TCM UVar
tcPat' (Id s _ Con i) uv _ =
  tcId s "Constructor doesn't match expected type " i uv
tcPat' (Id _ _ Var i) uv _ = do
  -- TODO: we should check shadowing since we don't check it
  -- in isValid.
  bindV i uv
  pure uv
tcPat' (App s [a]) uv ty = do
  typeError [s] "Singleton app in pattern"
  tcPat' a uv ty
tcPat' (App s as) uv _ = tcApp tcPat s as uv
tcPat' (Asc s e t) uv _ = do
  uvt <- mkTy t
  uvt' <- tcFin s "Pat signature doesn't match expected type " uvt uv
  tcPat e uvt'
tcPat' (Arrow s _ _) uv _ = do
  typeError [s] "Unexpected arrow pattern"
  pure uv
tcPat' (Wild _) uv _ = pure uv
tcPat' e@(Const _ _) uv ty = tcExpr' e uv ty
tcPat' (Paren _ e) uv ty = tcPat' e uv ty
tcPat' (Tuple s e) uv ty = tcTuple tcPat s e uv ty
tcPat' (List s e) uv ty = tcList tcPat s e uv ty
tcPat' (OpExp _ e) uv ty = tcPat' e uv ty
tcPat' (Block (s, _ds)) uv _ = do
  typeError [s] "Record pat TODO"
  pure uv
tcPat' (Dot s _) uv _ = do
  typeError [s] "Dot in pat TODO"
  pure uv
tcPat' e@(Ops _ _) uv ty = tcExpr' e uv ty -- Fails
tcPat' (Fn s _) uv _ =
  typeError [s] "Fn in pat" >> pure uv
tcPat' (Case s _ _) uv _ =
  typeError [s] "Case in pat" >> pure uv
tcPat' (If s _ _ _) uv _ =
  typeError [s] "If in pat" >> pure uv
tcPat' (IfMatch s _ _ _ _) uv _ =
  typeError [s] "If <- in pat" >> pure uv
tcPat' (Do s _ _ _) uv _ =
  typeError [s] "Do in pat" >> pure uv
tcPat' (Assign s _ _) uv _ =
  typeError [s] "Assign in pat" >> pure uv

-- Type check an id (same for both Con pat and any exp id)
tcId :: Span -> String -> Var -> UVar -> TCM UVar
tcId s msg i uv = do
  uvi <- lookupV s i
  t <- inst uvi
  tcFin s msg t uv

-- Type check an application (same for both pat and exp)
tcApp :: HasCallStack => TC -> Span -> [Exp] -> UVar -> TCM UVar
tcApp _  s [] uv = do
  typeError [s] "Empty application"
  pure uv
tcApp tc s (f : es) uv = do
  tf <- tc f =<< newUV s
  tcArgs tc s es uv =<< getU tf

-- Typecheck the args of a function call of type uv returning uvr.
tcArgs :: HasCallStack => TC -> Span -> [Exp] -> UVar -> (UVar, Typ) -> TCM UVar
tcArgs _ s [] uvr (uv, _) =
  tcFin s "Result type mismatch, got " uvr uv
tcArgs tc s (e:es) uvr (uv, typ) = do
  (_, a, b) <- expectArrow s uv typ
  _ <- tc e a
  tcArgs tc s es uvr =<< getU b

tcTuple :: TC -> Span -> [Exp] -> UVar -> Typ -> TCM UVar
tcTuple _ s [] uv ty = do
  t <- expectTuple s 0 uv ty
  pure t
tcTuple tc s es uv (TApp _ (tt:ts)) | length es == length ts = do
  _ <- uncurry (expectTuple s (length es)) =<< getU tt
  zipWithM_ tc es ts
  pure uv
tcTuple tc s es uv _ = do
  let len = length es
  tt <- tupleType s len
  ts <- replicateM len (newUV s)
  t <- newUV' (TApp s (tt:ts))
  tcFin s " is tuple of type " t uv
  zipWithM tc es ts
  pure t

tcList :: TC -> Span -> [Exp] -> UVar -> Typ -> TCM UVar
tcList tc s es uv ty = do
  (ruv, e) <- expectList s uv ty
  traverse (`tc` e) es
  pure ruv

tcMatch :: [UVar] -> [Clause] -> UVar -> TCM UVar
tcMatch uvs cs uv = do
  traverse_ (tcClause uvs uv) cs
  pure uv

tcClause :: [UVar] -> UVar -> Clause -> TCM UVar
tcClause uvs uv (ps, e) = do
  zipWithM_ tcPat ps uvs
  tcExpr e uv

tcFun :: HasCallStack => Span -> UVar -> Arity -> [Clause] -> TCM UVar
tcFun s uvSig a cs = scope $ do
  p <- ppTy uvSig
  (as, r) <- tracef ["tcFun", show uvSig, "=", showPp p, " aty ", show a] $
             pullSig s a uvSig
  tcMatch as cs r
  p' <- ppTy uvSig
  tracef ["tcFun'", show uvSig, "=", showPp p', " aty ", show a] $
    pure uvSig

pullSig :: HasCallStack => Span -> Arity -> UVar -> TCM ([UVar], UVar)
pullSig _ 0 uvs = pure ([], uvs)
pullSig s arity uvs = do
  (_, a, b) <- uncurry (expectArrow s) =<< getU uvs
  (as, r) <- pullSig s (arity - 1) b
  pure (a:as, r)

tcDefs :: HasCallStack => Defs -> UVar -> TCM UVar
tcDefs ds uv =
  case groupDefs ds of
    Right gs -> do
      traverse_ tcTBind gs
      tcGroups mempty gs uv
    Left es -> do
      traverse_ (\(s, bs) -> typeError [s] (toString bs)) es
      newUV (span ds)

-- Create initial bindings for type names, so that
-- we can handle mutual type recursion.
tcTBind :: DefGroup -> TCM ()
tcTBind (D (Data e _)) = tcTLHS e
tcTBind (D (Struct e _)) = tcTLHS e
tcTBind _ = pure ()
-- TODO: type synonyms.

-- Bind LHS of data or struct def (common code).
tcTLHS :: Exp -> TCM ()
tcTLHS e = do
  let e' = cleanTy e
      isV (Id _ _ Var _) = True
      isV _ = False
      args (App _ (a:as)) = (a, as)
      args t = (t, [])
  case args e' of
    (Id s _ Con i, as) | all isV as -> do
      if i=="[]" || i == "Bool" then
        rvFor s i
      else
        brandNewRV "Type decl cannot shadow existing definition" s i
      pure ()
    (Id _ _ Con _, _) -> do
      typeError [span e] "Args to type decl must all be variables."
    _ -> do
      typeError [span e] "Type decl must start with type name."

tcGroups :: HasCallStack => Map Var Exp -> [DefGroup] -> UVar -> TCM UVar
tcGroups _ [] uv = typeError [] "Expected final expr in block" >> pure uv
tcGroups sigs [Record m] _ = do
  mapM_ (\(i, sig) ->
           typeError [span sig] ("signature without definition for "++toString i))
    (M.toList sigs)
  let s = foldMap' span (M.elems m)
  typeError [s] "Record binding TODO"
  newUV s
tcGroups sigs [D (BindExp e)] uv = do
  mapM_ (\(i, sig) ->
           typeError [span sig] ("signature without definition for "++toString i))
    (M.toList sigs)
  tcExpr e uv
tcGroups sigs (D (Fix _ _ _) : ds) uv = do
  tcGroups sigs ds uv
tcGroups sigs (D (BindExp a@(Asc _ (Id _ _ Var i) _)) : ds) uv =
  tcGroups (M.insert i a sigs) ds uv
tcGroups sigs (D (Data e ds) : gs) uv = do
  -- TODO kind checking!  That's just recursion, right?  Right?
  traverse_ (bindCon (cleanTy e)) (snd ds)
  tcGroups sigs gs uv
tcGroups sigs (D (Struct e ds) : gs) uv = do
  typeError [span e <> span ds] "Struct def TODO"
  tcGroups sigs gs uv
tcGroups sigs (D (Def (Id s _ Var i) e) : gs) uv = do
  let genn | isValue e = gen
           | otherwise = const id
  uve <- genn s $ do
    uve0 <- maybe (newUV s) mkTy $ M.lookup i sigs
    tcExpr e uve0
  bindV i uve
  tcGroups (M.delete i sigs) gs uv
tcGroups sigs (D d@(Def p e) : gs) uv = do
  -- TODO: Can we have sigs for vars bound by p?
  uve <- tcExpr e =<< newUV (span d)
  _ <- tcPat p uve
  tcGroups sigs gs uv
tcGroups sigs (D (BindExp e) : gs) uv = do
  _ <- tcExpr e =<< newUV (span e)
  tcGroups sigs gs uv
tcGroups sigs (Fns g : gs) uvf = do
  gss <- regroup g
  sigs' <- foldM tcRecGroup sigs gss
  tcGroups sigs' gs uvf
tcGroups sigs (g:gs) uv = do
  typeError [span g] "Unrecognized Def."
  tcGroups sigs gs uv

-- We require binding groups to be ordered by dependency,
-- so rather than running a full SCC we look for forward
-- edges and group bindings until we run out of forward
-- edges.
regroup :: [GroupFun] -> TCM [[GroupFun]]
regroup g = do
  let vs = S.fromList [ v | (_, v, _, _, _) <- g ]
      groupZ = ([], mempty, mempty, False)
      -- todo: still unresolved groups.
      -- group: proposed group.
      -- groupVs: remaining unseen fvs in group.
      iter :: Set Var -> ([(GroupFun, Set Var)], Set Var, Set Var, Bool) -> [GroupFun] -> TCM [[GroupFun]]
      iter todo (group, groupBV, groupRFV, groupErr) (f@(_, v, _, _, _) : gs) = do
        let todo' = S.delete v todo
            fvs = fv (Fns [f]) `S.intersection` todo'
            rfvs = fvs `S.difference` groupBV -- remaining fvs to add to group
            group' = (f, rfvs) : group
            groupBV' = S.insert v groupBV
            groupRFV' = S.delete v groupRFV <> rfvs
            groupErr' = groupErr || not (null fvs)
        if null groupRFV' then do -- No group dependencies remaining
          let l = reverse group'
          when groupErr' $
            traverse_ unorderedGroup l
          (reverse (fmap fst l) :) <$> iter (todo `S.difference` groupBV') groupZ gs
        else -- Add to group
          iter todo (group', groupBV', groupRFV', groupErr') gs
      iter _ ([], _, _, _) [] = pure []
      iter _ (group, _, _, groupErr) [] = do
        let l = reverse group
        when groupErr $ traverse_ unorderedGroup l
        pure [fmap fst l]
      unorderedGroup ((s, v, _, _, _), fvs) = do
        if null fvs then
          typeError [s] ("Later definition of "++showPp v)
        else
          typeError [s] (showPp v++" contains non-recursive forward references to "++
                         showPp (hsep $ punctuate "," $ fmap pp $ S.toList fvs))
  iter vs groupZ g

tcRecGroup :: Map Var Exp -> [GroupFun] -> TCM (Map Var Exp)
tcRecGroup sigs g = do
  let vars = [ v | (_, v, _, _, _) <- g ]
      spans = [ s | (s, _, _, _, _) <- g ]
      bindSigs (s, v, a, sig, ds) = do
        uvSig <- scope $ do
          uvp <- bindSigM s v (M.lookup v sigs)
          uvs <- bindSigM s v sig
          tcFin s "Multiple signatures don't match " uvp uvs
        bindV v uvSig
        pure (s, a, uvSig, ds)
      checkFunc (s, a, uvSig, cs) = scope $ do
        uvr <- rinst uvSig
        tcFun s uvr a cs
  uvs <- gens spans $ do
    g' <- traverse bindSigs g
    traverse checkFunc g'
  zipWithM_ bindV vars uvs
  return (foldr M.delete sigs vars)

bindCon :: Exp -> (Span, Def) -> TCM ()
bindCon hdr (s, BindExp e) = bindCon' hdr s (cleanCon e)
bindCon _   (s, _) = typeError [s] "Not a constructor def"

bindCon' :: Exp -> Span -> Exp -> TCM ()
bindCon' hdr _ (Asc s (Id _ _ Con c) ty) =
  bindV c =<< scope (gen s (validateConTy hdr ty >> mkTy ty))
bindCon' hdr s (Id _ _ Con c) =
  bindV c =<< scope (gen s (mkTy hdr))
bindCon' hdr s (App s' (Id _ _ Con c : as)) =
  bindV c =<< scope (gen s (mkArrowTy s' as hdr))
bindCon' hdr s (List _ []) =
  bindV "[]" =<< scope (gen s (mkTy hdr))
bindCon' _ s _ =
  typeError [s] "Not a constructor def"

validateConTy :: Exp -> Exp -> TCM ()
validateConTy r (Arrow _ _a b) = validateConTy r b
-- TODO: Validate a in some fashion.  Eg it must have kind Type.
validateConTy (Id _ _ _ t) (Id s _ Con t')
  | t /= t' = typeError [s] "Ascribed constructor result must match type name"
  | otherwise = pure ()
validateConTy (App _ (Id _ _ _ t:as)) (App s (Id _ _ Con t' : as'))
  | t /= t' = typeError [s] "Ascribed constructor result must match type name"
  | length as /= length as' =
      typeError [s] "Ascribed constructor result must match arg count of type name"
  | otherwise = pure ()
validateConTy _ t =
  typeError [span t] "Ascribed constructor result does not look like type head"

mkArrowTy :: Span -> [Exp] -> Exp -> TCM UVar
mkArrowTy _ [] r = mkTy r
mkArrowTy s (t:ts) r = do
  a <- mkTy t
  b <- mkArrowTy s ts r
  newUV' (TArrow s a b)

-- Bind the signature for given var.  Return the type bound.
bindSig :: Var -> Exp -> TCM UVar
bindSig i (Asc _ (Id _ _ _ i') t) | i == i' = bindSig i t
bindSig _ t = do
  uv <- gen (span t) $ mkTy t
  pure uv

-- Bind possible signature for var, return the type bound or fresh UV.
bindSigM :: Span -> Var -> Maybe Exp -> TCM UVar
bindSigM s _ Nothing = newUV s
bindSigM _ v (Just e) = bindSig v e

------------------------------------------------------------
-- Top level driver and environment setup

goTop :: HasCallStack => Defs -> TCM Defs
goTop ds = do
  traverse (brandNewRV "initial env" noSpan) ["Int", "Char", "String", "Double", "[]"]
  voidTy <- tupleType noSpan 0
  bool <- brandNewRV "initial bool" noSpan "Bool"
  traverse (\n -> bindV n bool) ["False", "True"]
  let prims = (M.toList env0) :: [(Var, (Val Maybe, Exp))]
  traverse_ (\(i, (_, t)) -> bindV i =<< (gen noSpan $ scope $ mkTy t)) prims
  tcDefs ds voidTy
  pure ds

typecheckTop :: HasCallStack => (SpanPos, Defs) -> (SpanPos, Defs)
typecheckTop (sp, ds) = do
  let st0 = TCState mempty mempty mempty mempty mempty
      (ds', stf) = runState (goTop ds) st0
      fmt ([s], msg) = spanPrefix s sp ++ msg
      fmt (ss, msg) = concatMap (`spanPrefix` sp) ss ++ msg
  if null (errs_ stf) then
    (sp, ds')
  else
    error $ unlines $ fmap fmt $ reverse (errs_ stf)
