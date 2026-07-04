module SemUtil(
  conDesc, conClo,
  patToPats, patsToPat, typeArity,
  toDisj, mkRhs) where
import AST
import Data.ByteString.UTF8(toString)
import GHC.Stack(HasCallStack)
import Value

-- Constructor descriptor
conDesc :: Applicative m => ConName -> Arity -> Desc m
conDesc v i = d where
  d = Desc v i Fold (CloFun cf)
  cf | i == 0 = error ("Applying 0-ary "++toString v)
     | otherwise = pure . VObj d

-- Constructor closure
conClo :: Applicative m => ConName -> Arity -> Val m
conClo v i = VDesc (conDesc v i)

-- Arity based on arrow counting
typeArity :: HasCallStack => Exp -> Arity
typeArity (Paren _ t) = typeArity t
typeArity (Asc _ t _) = typeArity t
typeArity (Arrow _ _ b) = 1 + typeArity b
typeArity _ = 0

-- Turn a case disjunct (lhs is a singleton pat) into
-- a clause (lhs is a list of pats).
toDisj :: HasCallStack => (Span, Def) -> Clause
toDisj (_, Def p e) = ([p], e)
toDisj (_, d) = error ("Illegal case disjunct "++showPp d)

-- Turn a list of Fn arg bindings into an arity-tagged list of clauses.
mkRhs :: HasCallStack => [(Span, Def)] -> (Arity, [Clause])
mkRhs ds = do
  let one (_, Def p e) = (patToPats p, e)
      one (_, d) = error ("Unexpected disjunct "++showPp d)
  case fmap one ds of
    [] -> error "Empty anonymous function."
    c:cs
      | all ((==a) . length . fst) cs -> (a, c:cs)
      | otherwise -> error ("Inconsistent arities, expect "++show a++"\n"++showPp ds)
      where a = length . fst $ c
