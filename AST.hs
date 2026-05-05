{-# LANGUAGE OverloadedStrings #-}
module AST where
import Data.ByteString(ByteString)
import qualified Data.ByteString.UTF8 as UTF8
import Prelude hiding (span)
import Text.Megaparsec(SourcePos)
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint(
  Doc, (<+>), lbrace, rbrace, brackets, double, hang, hcat, hsep,
  int, integer, nest, parens, punctuate, vcat)

-- A span is a pair of file offsets.
type Span = (Int, Int)

uSpan :: Span -> Span -> Span
uSpan (p0, _) (_, p3) = (p0, p3)

type Id = (Span, ByteString)
type Op = (Span, ByteString)
type Con = (Span, ByteString)
type ConOp = (Span, ByteString)

data Mod = Mod SourcePos Defs Imports Defs
  deriving (Show)

type Imports = [Import]

data Import = Import Span Id Defs
  deriving (Show)

type Defs = (Span, [(Span, Def)])

data FixDir = L | R | None deriving (Eq, Show)

data Def
  = BindExp Exp
  | Def Exp Exp
  | Data Exp Defs
  | Struct Exp Defs
  | Fix FixDir Int Op
  deriving (Show)

data Exp
  = Id Id
  | App Span Exp Exp
  | RevApp Span Exp Exp -- Reverse apply exp to op
  | Fn Span Exp Exp
  | Asc Span Exp Exp
  | Arrow Span Exp Exp
  | Op Op
  | Con Con
  | ConOp ConOp
  | Wild Span
  | EInt Span Integer
  | EFloat Span Double
  | EChar Span ByteString
  | EString Span ByteString
  | Ops Exp [(Exp, Exp)]
  | Case Span Exp Defs
  | If Span Exp Exp Exp
  | IfMatch Span Exp Exp Exp Exp
  | Dot Span [Exp]
  | Paren Span Exp
  | Tuple Span [Exp]
  | List Span [Exp]
  | Do Span Exp Exp Defs
  | Assign Span Exp Exp
  | Block Defs
  | OpExp Span Exp -- `exp`
  deriving (Show)

type ValidErrs = [(Span, ByteString)]

par :: Exp -> Exp
par e = Paren (span e) e

unpar :: Exp -> Exp
unpar (Paren _ e) = e
unpar e = e

fp :: IsAST t => t -> t
fp = fullParen

fpe :: Exp -> Exp
fpe = unpar . fp

class IsAST t where
  isValid :: t -> ValidErrs
  span :: t -> Span
  fullParen :: t -> t
  pp :: t -> Doc


instance IsAST t => IsAST (Span, t) where
  isValid (_, t) = isValid t
  span (s, _) = s
  fullParen (s, t) = (s, fullParen t)
  pp (_, t) = pp t

instance IsAST t => IsAST [t] where
  isValid ts = concatMap isValid ts
  span [] = error "span []"
  span [a] = span a
  span (a:as) = span a `uSpan` span as
  fullParen ts = fullParen <$> ts
  pp = vcat . fmap pp

ppOp :: Exp -> Doc -> Exp -> Doc
ppOp e1 op e2 = hang (pp e1 <+> op) 2 (pp e2)

text :: ByteString -> Doc
text = PP.text . UTF8.toString

instance IsAST Exp where
  isValid (Id _) = []
  isValid (App _ e1 e2) = isValid e1 <> isValid e2
  isValid (RevApp _ e1 e2) = isValid e1 <> isOppy e2
  isValid (Fn _ args body) = isArgs args <> isValid body
  isValid (Asc _ e t) = isValid e <> isTy t
  isValid (Arrow s _ _) = [(s, "Arrow type in expression")]
  isValid (Op _) = []
  isValid (Con _) = []
  isValid (ConOp _) = []
  isValid (Wild s) = [(s, "Wildcard in expression")]
  isValid (EInt _ _) = []
  isValid (EFloat _ _) = []
  isValid (EChar _ _) = []
  isValid (EString _ _) = []
  isValid (Ops e ops) =
    isValid e <> concatMap (\(op, e2) -> isOppy op <> isValid e2) ops
  isValid (Case _ e ds) = isValid e <> isCase ds
  isValid (If _ i t e) = isValid i <> isValid t <> isValid e
  isValid (IfMatch _ p i t e) = isPat p <> isValid i <> isValid t <> isValid e
  isValid (Dot _ es) = concatMap isValid es
  isValid (Paren _ e) = isValid e
  isValid (Tuple _ es) = concatMap isValid es
  isValid (List _ es) = concatMap isValid es
  isValid (Do _ p e ds) = isPat p <> isValid e <> isValid ds
  isValid (Assign _ l e) = isValid l <> isValid e
  isValid (Block ds) = isValid ds
  isValid (OpExp _ o) = isValid o
  span (Id (s, _)) = s
  span (App s _ _) = s
  span (RevApp s _ _) = s
  span (Fn s _ _) = s
  span (Asc s _ _) = s
  span (Arrow s _ _) = s
  span (Op (s, _)) = s
  span (Con (s, _)) = s
  span (ConOp (s, _)) = s
  span (Wild s) = s
  span (EInt s _) = s
  span (EFloat s _) = s
  span (EChar s _) = s
  span (EString s _) = s
  span (Ops e []) = span e
  span (Ops e os) = span e `uSpan` span (snd $ last os)
  span (Case s _ _) = s
  span (If s _ _ _) = s
  span (IfMatch s _ _ _ _) = s
  span (Dot s _) = s
  span (Paren s _) = s
  span (Tuple s _) = s
  span (List s _) = s
  span (Do s _ _ _) = s
  span (Assign s _ _) = s
  span (Block ds) = span ds
  span (OpExp s _) = s
  fullParen e@(Id _) = e
  fullParen (App s e1 e2) = par (App s (fp e1) (fp e2))
  fullParen (RevApp s e1 e2) = par (RevApp s (fp e1) (fp e2))
  fullParen (Fn s args body) = par (Fn s (fpe args) (fpe body))
  fullParen (Asc s e t) = par (Asc s (fp e) (fp t))
  fullParen (Arrow s a b) = par (Arrow s (fp a) (fp b))
  fullParen e@(Op _) = par e
  fullParen e@(Con _) = e
  fullParen e@(ConOp _) = par e
  fullParen e@(Wild _) = e
  fullParen e@(EInt _ _) = e
  fullParen e@(EFloat _ _) = e
  fullParen e@(EChar _ _) = e
  fullParen e@(EString _ _) = e
  fullParen (Ops e ops) =
    par (Ops (fp e) ((\(op, e2) -> (fpe op, fp e2)) <$> ops))
  fullParen (Case s e ds) = par (Case s (fp e) (fp ds))
  fullParen (If s i t e) =
    par (If s (fpe i) (fpe t) (fpe e))
  fullParen (IfMatch s p i t e) =
    par (IfMatch s (fp p) (fp i) (fpe t) (fpe e))
  fullParen (Dot s es) = par (Dot s (map fp es))
  fullParen (Paren s e) = Paren s (fpe e)
  fullParen (Tuple s es) = Tuple s (fpe <$> es)
  fullParen (List s es) = List s (fpe <$> es)
  fullParen (Do s p e ds) = par (Do s (fp p) (fp e) (fp ds))
  fullParen (Assign s l e) = par (Assign s (fp l) (fp e))
  fullParen (Block ds) = Block (fp ds)
  fullParen (OpExp s e) = OpExp s (fpe e)
  pp (Id (_, e)) = text e
  pp (App _ (RevApp _ e1 o) e2) = ppOp e1 (ppOppy o) e2
  pp (App _ e1 e2) = pp e1 <+> pp e2
  pp (RevApp _ e1 p) = parens (pp e1 <+> ppOppy p)
  pp (Fn _ args body) =
    hang (PP.text "fn" <+> pp args <+> PP.text "=") 2 (pp body)
  pp (Asc _ e t) = ppOp e (PP.text ":") t
  pp (Arrow _ a b) = ppOp a (PP.text "->") b
  pp (Op (_, o)) = parens (text o)
  pp (Con (_, c)) = text c
  pp (ConOp (_, o)) = parens (text o)
  pp (Wild _) = PP.text "_"
  pp (EInt _ i) = integer i
  pp (EFloat _ d) = double d
  pp (EChar _ c) = PP.text (show c)
  pp (EString _ s) = PP.text (show s)
  pp (Ops e []) = pp e
  pp (Ops e ((o, e2) : es)) = ppOp e (ppOppy o) (Ops e2 es)
  pp (Case _ e ds) = hang (PP.text "case" <+> pp e) 2 (pp (Block ds))
  pp (If _ i t e) =
    vcat [PP.text "if" <+> pp i,
          hang (PP.text "then") 2 (pp t), hang (PP.text "else") 2 (pp e)]
  pp (IfMatch _ p i t e) =
    vcat [PP.text "if" <+> hang (pp p <+> PP.text "<-") 4 (pp i),
          hang (PP.text "then") 2 (pp t), hang (PP.text "else") 2 (pp e)]
  pp (Dot _ (e:es)) = pp e <> hcat ((PP.text "." <>) . pp <$> es)
  pp (Dot _ []) = PP.empty
  pp (Paren _ e) = parens (pp e)
  pp (Tuple _ es) = parens (hsep $ punctuate (PP.text ",") (pp <$> es))
  pp (List _ es) = brackets (hsep $ punctuate (PP.text ",") (pp <$> es))
  pp (Do _ p e ds) =
    vcat [PP.text "do" <+> hang (pp p <+> PP.text "<-") 4 (pp e),
          pp (Block ds)]
  pp (Assign _ l e) = ppOp l (PP.text ":=") e
  pp (Block ds) = vcat [lbrace, nest 2 (pp ds), rbrace]
  pp (OpExp _ e) = hcat [PP.text "`", pp e, PP.text "`"]

isOppy :: Exp -> ValidErrs
isOppy (Op _) = []
isOppy (ConOp _) = []
isOppy (OpExp _ e) = isValid e
isOppy e = [(span e, "Not a valid operator")]

ppOppy :: Exp -> Doc
ppOppy (Op (_, o)) = text o
ppOppy (ConOp (_, o)) = text o
ppOppy e@(OpExp _ _) = pp e
ppOppy (Paren _ e) = ppOppy e
ppOppy e = pp (OpExp (span e) e)

isArgs :: Exp -> ValidErrs
isArgs (App _ a e) = isArgs a <> isPat e
isArgs e = isPat e

isPat :: Exp -> ValidErrs
isPat (App _ a e) = isPatL a <> isPat e
isPat (Asc _ e t) = isPat e <> isTy t
isPat (Id _) = []
isPat (Con _) = []
isPat (Op _) = []
isPat (ConOp _) = []
isPat (Wild _) = []
isPat (EInt _ _) = []
isPat (EFloat _ _) = []
isPat (EChar _ _) = []
isPat (EString _ _) = []
isPat (Paren _ e) = isPat e
isPat (Tuple _ es) = concatMap isPat es
isPat (List _ es) = concatMap isPat es
isPat (Block ds) = isRecPat ds
isPat e = [(span e, "Not a valid pattern")]

isPatL :: Exp -> ValidErrs
isPatL (App _ a e) = isPatL a <> isPat e
isPatL (Asc _ e t) = isPatL e <> isTy t
isPatL (Paren _ e) = isPatL e
isPatL (Con _) = []
isPatL (ConOp _) = []
isPatL e = [(span e, "Not a valid pattern head")]

isRecPat :: Defs -> ValidErrs
isRecPat (_, ps) = concatMap isFieldBind ps

isFieldBind :: (Span, Def) -> ValidErrs
isFieldBind (_, Def (Id _) e) = isPat e
isFieldBind (s, _) = [(s, "Not a valid field pattern")]

instance IsAST Def where
  isValid (BindExp e) = isValid e
  isValid (Def pat e) = isLHS pat <> isValid e
  isValid (Data pat ds) = isTyCon pat <> isData ds
  isValid (Struct pat ds) = isTyCon pat <> isStruct ds
  -- isValid (Fun e ds) = isFunDef e <> isValid ds
  isValid (Fix _ _ _) = []
  span = error "span Def bereft of its span"
  fullParen (BindExp e) = BindExp (fp e)
  fullParen (Def pat e) = Def (fp pat) (fp e)
  fullParen (Data pat ds) = Data (fp pat) (fp ds)
  fullParen (Struct pat ds) = Struct (fp pat) (fp ds)
  fullParen d@(Fix _ _ _) = d
  pp (BindExp e) = pp e
  pp (Def pat e) = ppOp pat (PP.text "=") e
  pp (Data pat ds) = ppOp pat (PP.text "= data") (Block ds)
  pp (Struct pat ds) = ppOp pat (PP.text "= struct") (Block ds)
  pp (Fix L i (_, o)) = PP.text "infixl" <+> int i <+> text o
  pp (Fix R i (_, o)) = PP.text "infixr" <+> int i <+> text o
  pp (Fix None i (_, o)) = PP.text "infix" <+> int i <+> text o

isLHS :: Exp -> ValidErrs
isLHS (App _ a e) = isLHS a <> isPat e
isLHS (Asc _ a t) = isLHS a <> isTy t
isLHS (Id _) = []
isLHS (Op _) = []
isLHS (Con _) = []
isLHS (ConOp _) = []
isLHS (Paren _ e) = isLHS e
isLHS e = [(span e, "Not a valid LHS head")]


-- isFunDef :: Exp -> ValidErrs
-- isFunDef (App _ a e) = isFunDef a <> isPat e
-- isFunDef (Asc _ a t) = isFunDef a <> isTy t
-- isFunDef (Id _) = []
-- isFunDef (Paren _ e) = isFunDef e
-- isFunDef (Op _) = []
-- isFunDef e = [(span e, "Not a valid function head")]

isTyCon :: Exp -> ValidErrs
isTyCon (App _ a e) = isTyCon a <> isTyArg e
isTyCon (Asc _ e t) = isTyCon e <> isTy t
isTyCon (Con _) = []
isTyCon (ConOp _) = []
isTyCon (Paren _ e) = isTyCon e
isTyCon e = [(span e, "Not a valid Type Constructor")]

isTyArg :: Exp -> ValidErrs
isTyArg (Asc _ e t) = isTyArg e <> isTy t
isTyArg (Id _) = []
isTyArg (Op _) = []
isTyArg (Paren _ e) = isTyArg e
isTyArg e = [(span e, "Not a valid type argument")]

isData :: Defs -> ValidErrs
isData (_, ps) = concatMap isConDef ps

isConDef :: (Span, Def) -> ValidErrs
isConDef (_, BindExp (Asc _ c t)) = isCon c <> isTy t
isConDef (_, BindExp e) = isConDefApp e
isConDef (s, _) = [(s, "Not a valid constructor definition")]

isCon :: Exp -> ValidErrs
isCon (Paren _ e) = isCon e
isCon (Con _) = []
isCon (ConOp _) = []
isCon e = [(span e, "Not a constructor name in ascribed constructor def")]

isConDefApp :: Exp -> ValidErrs
isConDefApp (App _ a e) = isConDefApp a <> isTy e
isConDefApp (Con _) = []
isConDefApp (ConOp _) = []
isConDefApp (Paren _ e) = isConDefApp e
isConDefApp e = [(span e, "Not a valid constructor name in short constructor def")]

isStruct :: Defs -> ValidErrs
isStruct (_, ps) = concatMap isFieldDef ps

isFieldDef :: (Span, Def) -> ValidErrs
isFieldDef (_, BindExp (Asc _ c t)) = isFieldName c <> isTy t
isFieldDef (s, _) = [(s, "Invalid field definition")]

isFieldName :: Exp -> ValidErrs
isFieldName (Id _) = []
isFieldName (Op _) = []
isFieldName (Paren _ e) = isFieldName e
isFieldName e = [(span e, "Invalid field name")]

isTy :: Exp -> ValidErrs
isTy (Id _) = []
isTy (App _ a b) = isTy a <> isTy b
isTy (Asc _ t k) = isTy t <> isTy k
isTy (Arrow _ a b) = isTy a <> isTy b
isTy (Op _) = []
isTy (Con _) = []
isTy (ConOp _) = []
isTy (Wild _) = []
isTy (Paren _ t) = isTy t
isTy (Tuple _ es) = concatMap isTy es
isTy (List _ [t]) = isTy t
isTy (List s _) = [(s, "Wrong number of type parameters for list type.")]
isTy (Block ds) = isStruct ds
isTy e = [(span e, "Not a valid type")]

isCase :: Defs -> ValidErrs
isCase (s, []) = [(s, "empty case")]
isCase (_, ds) = concatMap isDisjunct ds

isDisjunct :: (Span, Def) -> ValidErrs
isDisjunct (_, Def p e) = isPat p <> isValid e
isDisjunct (s, _) = [(s, "Not a valid case disjunct")]
