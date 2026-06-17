module SemUtil(
  cDesc, cCon,
  patToPats, patsToPat, typeArity,
  toDisj, mkRhs) where
import AST
import Data.ByteString.UTF8(toString)
import GHC.Stack(HasCallStack)
import Parse
import Value

-- Constructor descriptor
cDesc :: Applicative m => ConName -> Arity -> Desc m
cDesc v i = d where
  d = Desc v i Fold (CloFun cf)
  cf | i == 0 = error ("Applying 0-ary "++toString v)
     | otherwise = pure . VObj d

-- Constructor closure
cCon :: Applicative m => ConName -> Arity -> Val m
cCon v i = VDesc (cDesc v i)

-- Arity based on arrow counting
typeArity :: HasCallStack => Exp -> Arity
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

-- Turn a case disjunct (lhs is a singleton pat) into
-- a clause (lhs is a list of pats).
toDisj :: HasCallStack => SpanPos -> (Span, Def) -> Clause
toDisj _ (_, Def p e) = ([p], e)
toDisj sp (s, d) = spanError s ("Illegal case disjunct "++showPp d) sp

-- Turn a list of Fn arg bindings into an arity-tagged list of clauses.
mkRhs :: HasCallStack => Span -> [(Span, Def)] -> SpanPos -> (Arity, [Clause])
mkRhs s0 ds sp = do
  let one (_, Def p e) = (patToPats p, e)
      one (_, d) = spanError s0 ("Unexpected disjunct "++showPp d) sp
  case fmap one ds of
    [] -> spanError s0 "Empty anonymous function." sp
    c:cs
      | all ((==a) . length . fst) cs -> (a, c:cs)
      | otherwise -> spanError s0 ("Inconsistent arities, expect "++show a) sp
      where a = length . fst $ c
