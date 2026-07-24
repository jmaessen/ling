{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}
module TypeCheck(typecheckTop) where
import AST
import Parse(SpanPos, spanPrefix)
import Primitive(env0)
import SemUtil(fromRhs, mkRhs, toDisj, fromDisj)
import Value(Val)

import Control.Monad
import Control.Monad.State
import Data.BakerVec hiding (replicate)
import qualified Data.BakerVec as BV
import Data.ByteString.Char8(replicate)
import Data.ByteString.UTF8(fromString, toString)
import Data.Foldable
import Data.List(sortOn, transpose)
import Data.Ord(Down(..))
import Data.Map hiding ((!), null, filter, foldl, foldr, splitAt)
import qualified Data.Map as M
import Data.Set as S hiding (null, foldl, filter, foldr, fold, splitAt)
import qualified GHC.Exts as IL
import GHC.Stack(HasCallStack)
import Prelude hiding (span, replicate)
import Text.PrettyPrint as PP hiding ((<>))

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
  deriving (Eq, Ord, Show)

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
inst :: UVar -> TCM (Bool, UVar)
inst = uvFunc $ \uv ty ->
  case ty of
    TScheme s rts t -> do
      m <- traverse (\uv' -> (uv',) <$> newUV s) rts
      (True,) . snd <$> inst' (M.fromList m) t
    _ -> pure (False, uv)

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
-- Hash consing of types prior to anti-unification
-- This enables easy checking of type equality.

-- Hash cons the set of types, returning a mapping
-- from original types to new types and the new types.
hashCons :: Vec Typ -> (Vec UVar, Vec Typ)
hashCons u = do
  let l = length u
      toNew0 = BV.replicate l (-1)
      (toNew, new, _) =
        foldl (\s i -> fst $ hc u i s) (toNew0, mempty, mempty) [0..l-1]
  (toNew, new)

type HCState = (Vec UVar, Vec Typ, Map Typ UVar)

hc :: Vec Typ -> UVar -> HCState -> (HCState, UVar)
hc old uv s@(toNew, new, mapping)
  | nuv == (-1) = hc' old uv (old!uv) (toNew, new, mapping)
  | otherwise = (s, nuv)
  where nuv = toNew!uv

hc' :: Vec Typ -> UVar -> Typ -> HCState -> (HCState, UVar)
hc' _ uv (UV s uv') s0@(_, new, _)
  | uv == uv' = hcNew uv (UV s uvn) s0
  where uvn = length new
hc' old uv (UV _ uv') s0 = do
  let (s1, uvn) = hc old uv' s0
  hcFin uv uvn s1
hc' _ uv (RV s v) s0 =
  hcNew uv (RV s v) s0
hc' _ uv e@(TTuple _ _) s0 =
  hcAdd uv e s0
hc' _ uv Type s =
  hcAdd uv Type s
hc' old uv (TArrow s a b) s0 = do
  let (s1, uva) = hc old a s0
      (s2, uvb) = hc old b s1
  hcAdd uv (TArrow s uva uvb) s2
hc' old uv (TApp s vs) s0 = do
  case hcs old vs s0 of
    (s1@(_, new, _), uvf:uvs)
      | TApp _ vs' <- new!uvf ->
        hcAdd uv (TApp s (vs' <> uvs)) s1
    (s1, uvs) -> hcAdd uv (TApp s uvs) s1
hc' old uv (TScheme s uvs uv') s0 = do
  case hcs old (uv':uvs) s0 of
    (_, []) -> error "impossible hc'"
    (s1, uvn:uvsn) ->
      hcAdd uv (TScheme s uvsn uvn) s1

hcs :: Vec Typ -> [UVar] -> HCState -> (HCState, [UVar])
hcs old uvs s = do
  let arg a (sk, uvsk) = fmap (:uvsk) $ hc old a sk
  foldr arg (s, []) uvs

hcFin :: UVar -> UVar -> HCState -> (HCState, UVar)
hcFin uv uvn (toNew, new, mapping) =
  ((writeVec toNew uv uvn, new, mapping), uvn)

hcNew :: UVar -> Typ -> HCState -> (HCState, UVar)
hcNew uv typ (toNew, new, mapping) = do
  let uvn = length new
  hcFin uv uvn (toNew, push new typ, mapping)

hcAdd :: UVar -> Typ -> HCState -> (HCState, UVar)
hcAdd uv typ s@(toNew, new, mapping)
  | Just uvn <- M.lookup typ mapping =
    hcFin uv uvn s
  | otherwise = do
    let uvn = length new
    hcNew uv typ (toNew, new, M.insert typ uvn mapping)

------------------------------------------------------------
-- Anti-unification: Compute least generalization of
-- use sites.  These must be keyed by skolem variables
-- (ie generic calls should be distinguished).
--
-- Unlike fully general anti-unification, here we
-- assume we're also passed an original polymorphic
-- type scheme which we're generalizing.  That's
-- important in propagating changes to other signatures
-- in the program.

antiUnify :: UVar -> [UVar] -> TCM UVar
antiUnify sig uvs =
  withUngen sig $ \sig' ->
    au0 sig' uvs mempty >> pure ()

withUngen :: UVar -> (UVar -> TCM ()) -> TCM UVar
withUngen uv act = do
  (_, scheme) <- getU uv
  case scheme of
    TScheme s vs sig -> gen s $ do
      unGen (S.fromList vs) sig
      act sig
      pure sig
    _ -> error "antiUnify non-schema"

-- Un-generalize the set of variables s in the given type.
unGen :: Set UVar -> UVar -> TCM ()
unGen s = ug where
  ug :: UVar -> TCM ()
  ug = uvFunc ug'
  ug' :: UVar -> Typ -> TCM ()
  ug' uv (RV sp _)
    | uv `S.member` s = assignU uv (UV sp uv) >> pure ()
  ug' _ (TApp _ es) = traverse_ ug es
  ug' _ (TArrow _ a b) = traverse_ ug [a,b]
  ug' _ _ = pure ()

type AUMap = Map [UVar] UVar

assignSafe :: HasCallStack => UVar -> UVar -> TCM UVar
assignSafe uv new = do
  -- Use unification to get ordering, equality, and level right.
  ok <- uv === new
  when (not ok) $ error "assignSafe not ok"
  pure uv

-- AntiUnify vars, storing in sig and hash consing as we go.
au0 :: HasCallStack => UVar -> [UVar] -> AUMap -> TCM AUMap
au0 _ [] _ = error "antiUnify []"
au0 sig uvs m = au1 sig (filter (/= sig) uvs) m

au1 :: HasCallStack => UVar -> [UVar] -> AUMap -> TCM AUMap
au1 _ [] m = pure m
au1 sig (uv:uvs) m
  | all (==uv) uvs = assignSafe sig uv >> pure m
au1 sig uvs m
  | Just uv <- M.lookup uvs m = assignSafe sig uv >> pure m
au1 sig uvs m = do
  ts <- traverse getU uvs
  au sig ts m

au :: HasCallStack => UVar -> [(UVar, Typ)] -> AUMap -> TCM AUMap
au _ [] _ = error "au [], shouldn't happen."
au sig ts@((_, UV _ _) : _) m = newAU sig ts m -- Distinguished by uv
au sig ts@((_, RV _ _) : _) m = newAU sig ts m -- Ditto
au sig ts@((_, TTuple _ _) : _) m = newAU sig ts m -- And again.
au sig ts@((_, Type) : _) m = newAU sig ts m -- Only one of these, others differ.
au sig ts@((_, (TArrow s _ _)) : _) m = do
  let ab = [(a, b) | (_, TArrow _ a b) <- ts]
  if length ab == length ts then do
    (a', b') <- uncurry (expectArrow s) =<< getU sig
    m' <- au0 a' (fmap fst ab) m
    m'' <- au0 b' (fmap snd ab) m'
    newAU sig ts m''
  else
    newAU sig ts m
au sig ts@((_, TApp s vs0) : _) m = do
  let vss = [vs | (_, TApp _ vs) <- ts]
      one :: (UVar, [UVar]) -> TCM AUMap -> TCM AUMap
      one (sig', vs) act = do
        m' <- act
        au0 sig' vs m'
  if length vss == length ts && all ((length vs0==) . length) vss then do
    as <- uncurry (expectTApp s (length vs0)) =<< getU sig
    foldr one (pure m) $ zip as $ transpose vss
  else
    newAU sig ts m
au _ ((_, TScheme _ _ _) : _) _ = error "au TScheme"

newAU :: UVar -> [(UVar, Typ)] -> AUMap -> TCM AUMap
newAU sig ts m =
  pure (M.insert (fmap fst ts) sig m)

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
  fst <$> mkScheme s vs (uv, ())

gen1 :: HasCallStack => Span -> TCM (UVar, a) -> TCM (UVar, a)
gen1 s act = do
  minUv <- gets (length . u_)
  (uv, e) <- act
  vs <- gen' minUv uv
  mkScheme s vs (uv, e)

gens :: HasCallStack => [Span] -> TCM [(UVar, a)] -> TCM [(UVar, a)]
gens spans act = do
  minUv <- gets (length . u_)
  uves <- act
  vss <- traverse (gen' minUv . fst) uves
  (sequence $ zipWith3 mkScheme spans vss uves)

mkScheme :: Span -> Set UVar -> (UVar, a) -> TCM (UVar, a)
mkScheme s vs (uv, a)
  | null vs = pure (uv, a)
  | otherwise = (,a) <$> newUV' (TScheme s (S.toList vs) uv)

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

expectTApp :: HasCallStack => Span -> Int -> UVar -> Typ -> TCM [UVar]
expectTApp s arity _ (TApp s' as) = do
  let l = length as
  case (compare arity l, as) of
    (EQ, _) -> pure as
    (LT, _) -> do
      let (bs, cs) = splitAt (l - arity + 1) as
      uv' <- newUV' (TApp s' bs)
      pure (uv':cs)
    (GT, []) -> error "empty TApp"
    (GT, f:cs) -> do
      bs <- uncurry (expectTApp s (arity - l + 1)) =<< getU f
      pure (bs <> cs)
expectTApp s arity uv (UV _ _) = do
  as <- replicateM arity (newUV s)
  assignU uv (TApp s as)
  pure as
expectTApp _ _ _ _ = error "expectTApp not TApp or UV"

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

mkList :: Span -> UVar -> TCM (UVar, UVar)
mkList s uv = do
  l <- getRV s "[]"
  e <- newUV s
  uv' <- newUV' (TApp s [l, e])
  ruv <- tcFin id s " got list " uv' uv
  pure (ruv, e)

-- Expect an arrow type, return its operand and result.
expectArrow :: HasCallStack => Span -> UVar -> Typ -> TCM (UVar, UVar)
expectArrow _ _ (TArrow _ a b) = pure (a, b)
expectArrow s uv _ = do
  a <- newUV s
  b <- newUV s
  r <- newUV' (TArrow s a b)
  _ <- tcFin id s " more arguments than expected " r uv
  return (a, b)

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
mkTy' (Wild s) = newUV s -- _ just means "Any old type here".
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
type TC = Exp -> UVar -> TCM (UVar, Exp)

asc :: Exp -> UVar -> Exp
asc e uv = Asc s e (Const s (EInt (toInteger uv)))
  where s = span e

asc' :: Bool -> Exp -> UVar -> Exp
asc' True e uv = asc e uv
asc' _ e _ = e

tcExpr :: HasCallStack => TC
tcExpr e = uvFunc (tcExpr' e)

tcExpr' :: HasCallStack => Exp -> UVar -> Typ -> TCM (UVar, Exp)
tcExpr' e uv (TScheme _ _ _) = do
  uv' <- rinst uv
  tcExpr e uv'
tcExpr' e@(Id _ _ _ _) uv _ =
  tcId "identifier doesn't match expected type " e uv
tcExpr' (App s [e]) uv typ = do
  typeError [s] "Singleton application"
  tcExpr' e uv typ
tcExpr' (App s es) uv _ = do
  tcApp tcExpr s es uv
tcExpr' (Fn s (s', b)) uv _ =
  fmap (Fn s . (s',) . fromRhs) <$> uncurry (tcFun s uv) (mkRhs b)
tcExpr' (Asc s e t) uv _ = do
  uvt <- mkTy t
  uvt' <- tcFin id s "Signature doesn't match expected type " uvt uv
  tcExpr e uvt'
tcExpr' e@(Arrow s _ _) uv _ = do
  typeError [s] "Unexpected arrow expression"
  pure (uv, e)
tcExpr' e@(Wild s) uv _ = do
  typeError [s] "Wildcard in expression"
  pure (uv, e)
tcExpr' e@(Const s c) uv _ =
  tcFin (,e) s " expected " uv =<< getRV s (constTypeName c)
tcExpr' e@(Ops _ _) uv _ = do
  typeError [span e] "Unresolved infix ops"
  pure (uv, e)
tcExpr' (Case s e (s', ds)) uv _ = do
  (euv, e') <- tcExpr e =<< newUV s
  (uv', cs) <- tcMatch [euv] (fmap toDisj ds) uv
  pure (uv', Case s e' (s', fmap fromDisj cs))
tcExpr' (If s p t e) uv _ = do
  bool <- rvFor s "Bool"
  (_, p') <- tcExpr p bool
  (_, t') <- tcExpr t uv
  (_, e') <- tcExpr e uv
  pure (uv, If s p' t' e')
tcExpr' (IfMatch s p d t e) uv _ = do
  (uvp, d') <- tcExpr d =<< newUV s
  scope $ do
    (_, p') <- tcPat p uvp
    (_, t') <- tcExpr t uv
    (_, e') <- tcExpr e uv
    pure (uv, IfMatch s p' d' t' e')
tcExpr' e@(Dot s _) uv _ = do
  typeError [s] "Dot typing is TODO"
  pure (uv, e)
tcExpr' (Paren s e) uv ty =
  fmap (Paren s) <$> tcExpr' e uv ty
tcExpr' (Tuple s es) uv ty = tcTuple tcExpr s es uv ty
tcExpr' (List s es) uv ty = tcList tcExpr s es uv ty
tcExpr' (Do s p e ds) uv _ = do
  (tp, e') <- tcExpr e =<< newUV s
  scope $ do
    (_, p') <- tcPat p tp
    fmap (Do s p' e') <$> tcDefs ds uv
tcExpr' (Assign s l r) uv _ = do
  (_, l') <- tcExpr l =<< newUV s
  (_, r') <- tcExpr r =<< newUV s
  typeError [s] " assign typechecking TODO"
  pure (uv, Assign s l' r')
tcExpr' (Block bs) uv _ = fmap Block <$> tcDefs bs uv
tcExpr' (OpExp s e) uv ty = fmap (OpExp s) <$> tcExpr' e uv ty

tcFin :: HasCallStack => (UVar -> a) -> Span -> String -> UVar -> UVar -> TCM a
tcFin f s msg got want = do
  ok <- got === want
  unless ok $ do
    pg <- ppTy got
    pw <- ppTy want
    typeError [s] (msg <> showPp pg <> " vs " <> showPp pw)
  pure (f got)

-- tcPat also binds variables
tcPat :: TC
tcPat e = uvFunc (tcPat' e)

tcPat' :: Pat -> UVar -> Typ -> TCM (UVar, Pat)
tcPat' e@(Id _ _ Con _) uv _ =
  tcId "Constructor doesn't match expected type " e uv
tcPat' e@(Id _ _ Var i) uv _ = do
  -- TODO: we should check shadowing since we don't check it
  -- in isValid.
  bindV i uv
  pure (uv, asc e uv)
tcPat' (App s [a]) uv ty = do
  typeError [s] "Singleton app in pattern"
  tcPat' a uv ty
tcPat' (App s as) uv _ = tcApp tcPat s as uv
tcPat' (Asc s e t) uv _ = do
  uvt <- mkTy t
  uvt' <- tcFin id s "Pat signature doesn't match expected type " uvt uv
  tcPat e uvt'
tcPat' e@(Arrow s _ _) uv _ = do
  typeError [s] "Unexpected arrow pattern"
  pure (uv, e)
tcPat' e@(Wild _) uv _ = pure (uv, e)
tcPat' e@(Const _ _) uv ty = tcExpr' e uv ty
tcPat' (Paren _ e) uv ty = tcPat' e uv ty
tcPat' (Tuple s e) uv ty = tcTuple tcPat s e uv ty
tcPat' (List s e) uv ty = tcList tcPat s e uv ty
tcPat' (OpExp s e) uv ty =
  fmap (OpExp s) <$> tcPat' e uv ty
tcPat' e@(Block (s, _ds)) uv _ = do
  typeError [s] "Record pat TODO"
  pure (uv, e)
tcPat' e@(Dot s _) uv _ = do
  typeError [s] "Dot in pat TODO"
  pure (uv, e)
tcPat' e@(Ops _ _) uv ty = tcExpr' e uv ty -- Fails
tcPat' e@(Fn s _) uv _ =
  typeError [s] "Fn in pat" >> pure (uv, e)
tcPat' e@(Case s _ _) uv _ =
  typeError [s] "Case in pat" >> pure (uv, e)
tcPat' e@(If s _ _ _) uv _ =
  typeError [s] "If in pat" >> pure (uv, e)
tcPat' e@(IfMatch s _ _ _ _) uv _ =
  typeError [s] "If <- in pat" >> pure (uv, e)
tcPat' e@(Do s _ _ _) uv _ =
  typeError [s] "Do in pat" >> pure (uv, e)
tcPat' e@(Assign s _ _) uv _ =
  typeError [s] "Assign in pat" >> pure (uv, e)

-- Type check an id (same for both Con pat and any exp id)
tcId :: String -> Exp -> UVar -> TCM (UVar, Exp)
tcId msg e@(Id s _ cv i) uv = do
  uvi <- lookupV s i
  (ins, t) <- inst uvi
  tcFin (\uv' -> (uv', asc' (ins && Var == cv) e uv')) s msg t uv
tcId _ e _ = error ("Bad tcId " <> showPp e)

-- Type check an application (same for both pat and exp)
tcApp :: HasCallStack => TC -> Span -> [Exp] -> UVar -> TCM (UVar, Exp)
tcApp _  s [] uv = do
  typeError [s] "Empty application"
  pure (uv, App s [])
tcApp tc s (f : es) uv = do
  (tf, f') <- tc f =<< newUV s
  fmap (App s . (f':)) <$> (tcArgs tc s es uv =<< getU tf)

-- Typecheck the args of a function call of type uv returning uvr.
tcArgs :: HasCallStack => TC -> Span -> [Exp] -> UVar -> (UVar, Typ) -> TCM (UVar, [Exp])
tcArgs _ s [] uvr (uv, _) =
  tcFin (,[]) s "Result type mismatch, got " uvr uv
tcArgs tc s (e:es) uvr (uv, typ) = do
  (a, b) <- expectArrow s uv typ
  (_, e') <- tc e a
  fmap (e':) <$> (tcArgs tc s es uvr =<< getU b)

tcTuple :: TC -> Span -> [Exp] -> UVar -> Typ -> TCM (UVar, Exp)
tcTuple _ s [] uv ty = do
  t <- expectTuple s 0 uv ty
  pure (t, Tuple s [])
tcTuple tc s es uv (TApp _ (tt:ts)) | length es == length ts = do
  _ <- uncurry (expectTuple s (length es)) =<< getU tt
  es' <- fmap snd <$> zipWithM tc es ts
  pure (uv, Tuple s es')
tcTuple tc s es uv _ = do
  let len = length es
  tt <- tupleType s len
  ts <- replicateM len (newUV s)
  t <- newUV' (TApp s (tt:ts))
  tcFin id s " is tuple of type " t uv
  es' <- fmap snd <$> zipWithM tc es ts
  pure (t, Tuple s es')

tcList :: TC -> Span -> [Exp] -> UVar -> Typ -> TCM (UVar, Exp)
tcList tc s es uv ty = do
  (ruv, e) <- expectList s uv ty
  es' <- fmap snd <$> traverse (`tc` e) es
  pure (ruv, List s es')

tcMatch :: [UVar] -> [Clause] -> UVar -> TCM (UVar, [Clause])
tcMatch uvs cs uv = do
  cs' <- fmap snd <$> traverse (tcClause uvs uv) cs
  pure (uv, cs')

tcClause :: [UVar] -> UVar -> Clause -> TCM (UVar, Clause)
tcClause uvs uv (s, ps, e) = do
  ps' <- fmap snd <$> zipWithM tcPat ps uvs
  fmap (s, ps',) <$> tcExpr e uv

tcFun :: HasCallStack => Span -> UVar -> Arity -> [Clause] -> TCM (UVar, [Clause])
tcFun s uvSig a cs = scope $ do
  p <- ppTy uvSig
  (as, r) <- tracef ["tcFun", show uvSig, "=", showPp p, " aty ", show a] $
             pullSig s a uvSig
  (_, cs') <- tcMatch as cs r
  p' <- ppTy uvSig
  tracef ["tcFun'", show uvSig, "=", showPp p', " aty ", show a] $
    pure (uvSig, cs')

pullSig :: HasCallStack => Span -> Arity -> UVar -> TCM ([UVar], UVar)
pullSig _ 0 uvs = pure ([], uvs)
pullSig s arity uvs = do
  (a, b) <- uncurry (expectArrow s) =<< getU uvs
  (as, r) <- pullSig s (arity - 1) b
  pure (a:as, r)

tcDefs :: HasCallStack => Defs -> UVar -> TCM (UVar, Defs)
tcDefs ds uv =
  case groupDefs ds of
    Right gs -> do
      traverse_ tcTBind gs
      fmap (fst ds,) <$> tcGroups mempty gs uv
    Left es -> do
      traverse_ (\(s, bs) -> typeError [s] (toString bs)) es
      (,ds) <$> newUV (span ds)

-- Create initial bindings for type names, so that
-- we can handle mutual type recursion.
tcTBind :: DefGroup -> TCM ()
tcTBind (D _ (Data e _)) = tcTLHS e
tcTBind (D _ (Struct e _)) = tcTLHS e
tcTBind _ = pure ()
-- TODO: type synonyms.

-- Bind LHS of data or struct def (common code).
tcTLHS :: Pat -> TCM ()
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

tcGroups :: HasCallStack => Map Var Exp -> [DefGroup] -> UVar -> TCM (UVar, [(Span, Def)])
tcGroups _ [] uv =
  typeError [] "Expected final expr in block" >> pure (uv, [])
tcGroups sigs [Record m] _ = do
  mapM_ (\(i, sig) ->
           typeError [span sig] ("signature without definition for "++toString i))
    (M.toList sigs)
  let s = foldMap' span (M.elems m)
  typeError [s] "Record binding TODO"
  uv <- newUV s
  pure (uv, [ (s', Def (Id s' Ident Var i) e) | (i, e) <- M.toList m, let s' = span e ])
tcGroups sigs [D s (BindExp e)] uv = do
  mapM_ (\(i, sig) ->
           typeError [span sig] ("signature without definition for "++toString i))
    (M.toList sigs)
  (uv', e') <- tcExpr e uv
  pure (uv', [(s, BindExp e')])
tcGroups sigs (D _ (Fix _ _ _) : ds) uv = do
  tcGroups sigs ds uv
tcGroups sigs (D _ (BindExp a@(Asc _ (Id _ _ Var i) _)) : ds) uv =
  tcGroups (M.insert i a sigs) ds uv
tcGroups sigs (D s (Data e (s', ds)) : gs) uv = do
  -- TODO kind checking!  That's just recursion, right?  Right?
  dss <- traverse (bindCon (cleanTy e)) ds
  fmap ((s, Data e (s', concat dss)):) <$> tcGroups sigs gs uv
tcGroups sigs (D s (Struct e ds) : gs) uv = do
  typeError [span e <> span ds] "Struct def TODO"
  fmap ((s, Struct e ds):) <$> tcGroups sigs gs uv
tcGroups sigs (D s (Def v@(Id _ _ Var i) e) : gs) uv = do
  let genn | isValue e = gen1
           | otherwise = const id
  (uve, e') <- genn s $ do
    uve0 <- maybe (newUV s) mkTy $ M.lookup i sigs
    tcExpr e uve0
  bindV i uve
  (uv', ds) <- tcGroups (M.delete i sigs) gs uv
  pure (uv', (s, Def (asc v uve) e') : ds)
tcGroups sigs (D s d@(Def p e) : gs) uv = do
  -- TODO: Can we have sigs for vars bound by p?
  (uve, e') <- tcExpr e =<< newUV (span d)
  (_, p') <- tcPat p uve
  fmap ((s, Def p' e'):) <$> tcGroups sigs gs uv
tcGroups sigs (D s (BindExp e) : gs) uv = do
  (_, e') <- tcExpr e =<< newUV (span e)
  fmap ((s, BindExp e'):) <$> tcGroups sigs gs uv
tcGroups sigs (Fns g : gs) uvf = do
  gss <- regroup g
  (sigs', dss) <- foldM tcRecGroup (sigs, []) gss
  (uv, ds) <- tcGroups sigs' gs uvf
  pure (uv, concat (reverse dss) <> ds)
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

tcRecGroup :: (Map Var Exp, [[(Span, Def)]]) -> [GroupFun] -> TCM (Map Var Exp, [[(Span, Def)]])
tcRecGroup (sigs, dss) g = do
  let vars = [ v | (_, v, _, _, _) <- g ]
      spans = [ s | (s, _, _, _, _) <- g ]
      sigs' = foldr M.delete sigs vars
      bindSigs (s, v, a, sig, ds) = do
        uvSig <- scope $ do
          uvp <- bindSigM s v (M.lookup v sigs)
          uvs <- bindSigM s v sig
          tcFin id s "Multiple signatures don't match " uvp uvs
        bindV v uvSig
        pure (s, a, uvSig, ds)
      checkFunc (s, a, uvSig, cs) = scope $ do
        uvr <- rinst uvSig
        tcFun s uvr a cs
      mkFunc (s, v, _, _, _) (uv, cs) = do
        let f = Fn s (s, fromRhs cs)
        (s, Def (asc (Id s Ident Var v) uv) f)
  uvcs <- gens spans $ do
    g' <- traverse bindSigs g
    traverse checkFunc g'
  zipWithM_ bindV vars (fmap fst uvcs)
  let ds = zipWith mkFunc g uvcs
  pure (sigs', ds : dss)

bindCon :: Exp -> (Span, Def) -> TCM [(Span, Def)]
bindCon hdr (s, BindExp e) = bindCon' hdr s (cleanCon e)
bindCon _   (s, _) = typeError [s] "Not a constructor def" >> pure []

bindCon' :: Exp -> Span -> Exp -> TCM [(Span, Def)]
bindCon' hdr _ (Asc s v@(Id _ _ Con c) ty) = do
  bindConF s v c (validateConTy hdr ty >> mkTy ty)
bindCon' hdr s v@(Id _ _ Con c) = do
  bindConF s v c (mkTy hdr)
bindCon' hdr s (App s' (v@(Id _ _ Con c) : as)) = do
  bindConF s v c (mkArrowTy s' as hdr)
bindCon' hdr s v@(List _ []) =
  bindConF s v "[]" (mkTy hdr)
bindCon' _ s _ =
  typeError [s] "Not a constructor def" >> pure []

bindConF :: Span -> Exp -> Var -> TCM UVar -> TCM [(Span, Def)]
bindConF s v c mkSig = do
  uv <- scope $ gen s mkSig
  bindV c uv
  pure $ [(s, BindExp (asc v uv))]

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
  gen (span t) (mkTy t)

-- Bind possible signature for var, return the type bound or fresh UV.
bindSigM :: Span -> Var -> Maybe Exp -> TCM UVar
bindSigM s _ Nothing = newUV s
bindSigM _ v (Just e) = bindSig v e

------------------------------------------------------------
-- Minimal polymorphism
-- As in Bjorner's Minimal Typing Derivations, ML workshop '94
-- (His algorithm M, not to be confused with the folklore
-- algorithm M we use for type inference above!)

newtype JoinMap k v = JM (Map k v) deriving (Eq, Ord)

instance (Ord k, Semigroup v) => Semigroup (JoinMap k v) where
  JM a <> JM b = JM $ M.unionWith (<>) a b

instance (Ord k, Semigroup v) => Monoid (JoinMap k v) where
  mempty = JM mempty

-- NOTE TODO: This assumes alpha-uniqueness of function names.
-- That's not *actually* something we have today.
minPoly :: Vec UVar -> Vec Typ -> Defs -> (Vec Typ, Defs)
minPoly renames typs ds = do
  let -- Collect schemes and occurrences
      mp (Asc _ (Id _ _ _ i) (Const _ (EInt uv0))) m = do
        let uv = fromInteger uv0
            uv' = renames!uv
        case typs!uv' of
          TScheme _ _ _ -> (M.singleton i uv', mempty) <> m
          _ -> (mempty, JM $ M.singleton i (S.singleton uv')) <> m
      mp _ m = m
      (pbs, JM occs) = gather mp (const id) ds
      -- For each scheme and its occurrences in reverse
      -- unification order, antiUnify.  Reverse order ensures
      -- later variable instantiations affect earlier signatures.
      minify (i, sig, sigs) = do
        sig0 <- ppTy sig
        res <- antiUnify sig sigs
        resS <- ppTy res
        tracew True [show i, "orig", showPp sig0, "new", showPp resS] $
          pure (i,res)
      st = TCState mempty mempty typs (BV.replicate (length typs) 0) []
      todo = sortOn (\(_, a, _)  -> Down a) $
        [ (i, sig, S.toList sigs)
        | (i, sig) <- M.toList pbs,
          Just sigs <- [M.lookup i occs]]
      (newPbs0, st') = runState (traverse minify todo) st
      -- Now replace signatures with their anti-unified equivalents.
      typs' = u_ st'
      newPbs = M.fromList newPbs0
      -- FIX: replaces instantiations as well!
      newSig (Asc s v (Const s' (EInt uv0))) = do
        let uv = fromInteger uv0
            uv1 = renames!uv
            uv' =
              case (v, typs!uv1) of
                (Id _ _ _ i, TScheme _ _ _)
                  | Just uv2 <- M.lookup i newPbs -> uv2
                _ -> uv1
        Asc s v (Const s' (EInt (fromIntegral uv')))
      newSig e = e
  trace (unlines ("minPoly" : fmap (\(i, uv, uvs) -> unwords [show i, ":", show uv, ";", show uvs, "->", show (newPbs M.! i)]) todo <> ["minPoly done"])) $
    (typs',) $ bottomUp newSig id ds

------------------------------------------------------------
-- Relabeling

-- When we label the code with signatures, we just record the
-- UVar since many signature variables aren't settled until
-- subsequent unification.  So we walk the program and expand
-- them into types when we're done.

uVarTypes :: Vec Typ -> Vec Exp
uVarTypes typs = trace (unlines $ zipWith (\i t -> showPp (PP.int i <> ": "<> pp (fullParen t) <> "       = "<> text (show (typs!i)))) [(0::Int)..] $ IL.toList exps) exps where
  l = length typs
  exps = IL.fromListN l $ zipWith ut [(0::Int)..] (IL.toList typs)
  -- Note that we're tying the knot with exps itself here.
  ut uv (UV _ uv') | uv /= uv' = exps!uv'
  ut uv (UV s _) = Id s Ident Var ("$uv" <> fromString (show uv))
  ut uv (RV s "$rv") = Id s Ident Var ("$rv" <> fromString (show uv))
  ut _  (RV s i)
    | isVar i = Id s Ident Var i
    | otherwise = Id s Ident Con i
  ut _ (TTuple s 0) = Id s Ident Con "()"
  ut _ (TTuple s 1) = Id s Ident Con "(_,)"
  ut _ (TTuple s n) = Id s Ident Con ("(" <> replicate (n-1) ',' <> ")")
  ut _ Type = Id noSpan Ident Con "Type"
  ut _ (TArrow s a b) = Arrow s (exps!a) (exps!b)
  ut uv (TApp s as@(a:at)) =
    case typs!a of
      TTuple _ n | length at == n -> Tuple s (fmap (exps!) at)
      RV _ "[]" | length at == 1 -> List s (fmap (exps!) at)
      TApp _ as' -> ut uv (TApp s (as' <> at))
      UV _ uv' | a /= uv' -> ut uv (TApp s (uv':at))
      _ -> App s (fmap (exps!) as)
  ut _ (TApp _ []) = error "Empty TApp"
  ut _ (TScheme _ _ v) = exps!v

relabel :: Vec Typ -> Defs -> Defs
relabel typs ds = bottomUp ef id ds where
  exps = uVarTypes typs
  ef (Asc s i (Const _ (EInt uv))) =
    Asc s i (exps!fromInteger uv)
  ef e = e

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
  (_, ds') <- tcDefs ds voidTy
  pure ds'

typecheckTop :: HasCallStack => (SpanPos, Defs) -> (SpanPos, Defs)
typecheckTop (sp, ds) = do
  let st0 = TCState mempty mempty mempty mempty mempty
      (ds1, stf) = runState (goTop ds) st0
      tys = u_ stf
      (renames, tys1) = uVarTypes tys `seq` trace (showPp ds1) $ hashCons tys
      (tys2, ds2) = minPoly renames tys1 ds1
      ds3 = relabel tys2 ds2
      fmt ([s], msg) = spanPrefix s sp ++ msg
      fmt (ss, msg) = concatMap (`spanPrefix` sp) ss ++ msg
  if null (errs_ stf) then
    (sp, ds3)
  else
    error $ unlines $ fmap fmt $ reverse (errs_ stf)
