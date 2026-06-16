{-# LANGUAGE OverloadedStrings #-}
module Desugar where
import AST
import Parse

import Data.Map as M hiding (foldr)
import Prelude hiding (span)

desugar :: (SpanPos, Defs) -> (SpanPos, Defs)
desugar (sp, ds) = (sp, desugarDefs ds)

desugarDefs :: Defs -> Defs
desugarDefs ds@(s, ds') =
  case groupDefs ds of
    Left _ -> (s, concatMap desugarDef ds')
    Right gs -> (s, trimSigs $ concatMap desugarGroup gs)

desugarDef :: (Span, Def) -> [(Span, Def)]
desugarDef (s, Def i e) = [(s, Def (desugarPat i) (desugarExp e))]
desugarDef (s, BindExp (Asc s' e t)) = [(s, BindExp (Asc s' (desugarExp e) t))]
desugarDef (s, BindExp e) = [(s, BindExp (desugarExp e))]
desugarDef (s, Data e (s', ds)) =
  [(s, Data e (s', fmap (desugarCon e) ds))]
desugarDef (_, Struct _ _) = []
desugarDef (_, Fix _ _ _) = []

desugarCon :: Exp -> (Span, Def) -> (Span, Def)
desugarCon t (s, BindExp e) = (s, BindExp $ desugarCon' t e)
desugarCon _ d = error ("desugarCon: not a constructor def "++showPp d)

desugarCon' :: Exp -> Exp -> Exp
desugarCon' t (Paren _ e) = desugarCon' t e
desugarCon' t i@(Id s _ Con _) = Asc s i t
desugarCon' t (List s []) = Asc s (Id s Ident Con "[]") t
desugarCon' t (App s (Paren _ e) ts) = desugarCon' t (App s e ts)
desugarCon' t (App s (App _ e es) ts) = desugarCon' t (App s e (es <> ts))
desugarCon' t (App s i@(Id _ _ Con _) ts) =
  Asc s i (foldr (Arrow s) t ts)
desugarCon' t (Asc s (Paren _ e) t') = desugarCon' t (Asc s e t')
desugarCon' _ a@(Asc _ (Id _ _ Con _) _) = a
desugarCon' _ (Asc s (List s' []) t) = Asc s (Id s' Ident Con "[]") t
desugarCon' _ (Asc _ e t') = desugarCon' t' e
desugarCon' _ e = error ("not a constructor def "++showPp e)

desugarGroup :: DefGroup -> [(Span, Def)]
desugarGroup (D d) = desugarDef (span d, d)
desugarGroup (Fns fns) = fmap desugarFunc fns
desugarGroup (Record m) =
  [ (se, Def (Id se Ident Var i) (desugarExp e)) |
    (i, e) <- M.toAscList m,
    let se = span e ]

desugarFunc :: (Span, Var, Arity, [([Exp], Exp)]) -> (Span, Def)
desugarFunc (s, f, _, ps) =
  (s, Def (Id s Ident Var f) (Fn s (s, fmap desugarClause ps)))

desugarClause :: ([Exp], Exp) -> (Span, Def)
desugarClause (ps, e) =
  (span ps <> span e, desugarOneFMatch (Def (patsToPat ps) e))

trimSigs :: [(Span, Def)] -> [(Span, Def)]
trimSigs ((_, BindExp (Asc _ (Id _ _ _ _) _)) : ds@(_:_)) = trimSigs ds
trimSigs (d:ds) = d : trimSigs ds
trimSigs [] = []

-- Expression desugaring.  Full paren and asc eraure.
-- TODO: decide which Asc survive type checking.
desugarExp :: Exp -> Exp
desugarExp e@(Id _ _ _ _) = e
desugarExp (App s e1 es) = do
  let es' = fmap desugarExp es
  case desugarExp e1 of
    App _ e es'' -> App s e (es'' <> es')
    e -> App s e es'
desugarExp (Fn s ds) = Fn s (desugarFMatch ds)
desugarExp (Asc _ e _) = e
desugarExp (Arrow _ _ _) = error "Desugar: Arrow"
desugarExp e@(Wild _) = e
desugarExp e@(Const _ _) = e
desugarExp (Ops _ _) = error "Desugar: Residual ops"
desugarExp (Case s e ds) = Case s (desugarExp e) (desugarMatch ds)
desugarExp (If s i t e) = do
  let st = span t
      se = span e
  Case s (desugarExp i) $ desugarMatch (s, [
    (st, Def (Id st Ident Con "True") t),
    (se, Def (Id st Ident Con "False") e)])
desugarExp (IfMatch s p i t e) =  do
  let se = span e
  Case s (desugarExp i) $ desugarMatch (s, [
    (span p <> span t, Def p t),
    (se, Def (Wild se) e)])
desugarExp (Dot s es) = Dot s (fmap desugarExp es)
desugarExp (Paren _ e) = desugarExp e
desugarExp (Tuple s es) = Tuple s (desugarExp <$> es)
desugarExp (List s []) = Id s Ident Con "[]"
desugarExp (List s (e:es)) =
  App s (Id s Op Con "::") [desugarExp e, desugarExp (List s es)]
desugarExp (Do s p e ds) = Do s (desugarPat p) (desugarExp e) (desugarDefs ds)
desugarExp (Assign s l e) = Assign s (desugarExp l) (desugarExp e)
desugarExp (Block ds) = Block (desugarDefs ds)
desugarExp (OpExp _ e) = e

-- TODO: Full pattern match compile.  But that may require
-- decl information and definitely requires gensym.
desugarPat :: Exp -> Exp
desugarPat e@(Id _ _ _ _) = e
desugarPat (App s e1 es) = do
  let es' = fmap desugarPat es
  case desugarPat e1 of
    App _ e es'' -> App s e (es'' <> es')
    e -> App s e es'
desugarPat (Asc _ e _) = e
desugarPat e@(Wild _) = e
desugarPat e@(Const _ _) = e
desugarPat (Dot s es) = Dot s (fmap desugarPat es)
desugarPat (Paren _ e) = desugarPat e
desugarPat (Tuple s []) = Id s Ident Con "()"
desugarPat (Tuple s es) = App s (Id s Ident Con "()") es
desugarPat (List s []) = Id s Ident Con "[]"
desugarPat (List s (e:es)) =
  App s (Id s Op Con "::") [desugarPat e, desugarPat (List s es)]
desugarPat (Block ds) = Block (desugarStructPat ds)
desugarPat (OpExp _ e) = e
desugarPat e = error ("Residual exp in pat "++showPp e)

-- Fn (multi-arg) match
desugarFMatch :: Defs -> Defs
desugarFMatch (s, ds) = (s, fmap (fmap desugarOneFMatch) ds)

desugarOneFMatch :: Def -> Def
desugarOneFMatch (Def (Asc _ p _) e) =
  desugarOneFMatch (Def p e)
desugarOneFMatch (Def (Paren s p) e) =
  Def (Paren s (desugarPat p)) (desugarExp e)
desugarOneFMatch (Def t@(Tuple _ []) e) =
  Def (desugarPat t) e
desugarOneFMatch (Def t@(Tuple s _) e) =
  Def (Paren s (desugarPat t)) e
desugarOneFMatch (Def (App s p ps) e) =
  Def (App s (desugarPat p) (fmap desugarPat ps)) (desugarExp e)
desugarOneFMatch d = desugarOneMatch d

-- Case (single-arg) match
desugarMatch :: Defs -> Defs
desugarMatch (s, ds) = (s, fmap (fmap desugarOneMatch) ds)

desugarOneMatch :: Def -> Def
desugarOneMatch (Def p e) = Def (desugarPat p) (desugarExp e)
desugarOneMatch d = error ("Bad match disjunct "++showPp d)

-- Struct match
desugarStructPat :: Defs -> Defs
desugarStructPat (s, ds) = (s, fmap (fmap desugarFieldMatch) ds)

desugarFieldMatch :: Def -> Def
desugarFieldMatch (BindExp i@(Id _ _ _ _)) = Def i i
desugarFieldMatch (Def i@(Id _ _ _ _) p) = Def i (desugarPat p)
desugarFieldMatch d = error ("Bad field match "++showPp d)
