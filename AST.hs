{-# LANGUAGE OverloadedStrings #-}
module AST where
import Data.ByteString(ByteString)
import qualified Data.ByteString.UTF8 as UTF8
import Prelude hiding (span)
import Text.Megaparsec(SourcePos)
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint(
  Doc, (<+>), lbrace, rbrace, brackets, double, hang, hcat, hsep, sep,
  int, integer, nest, parens, punctuate, vcat)

noSpan :: Span
noSpan = S 0 0

-- A span is a pair of file offsets.
data Span = S Int Int
  deriving (Show)

-- We don't care about source location for equality.
instance Eq Span where
  _ == _ = True

instance Semigroup Span where
  S p0 p1 <> S p2 p3 = S (min p0 p1) (max p2 p3)


data Mod = Mod SourcePos Defs Imports Defs
  deriving (Eq, Show)

type Imports = [Import]

type Id = (Span, ByteString)

data Import = Import Span Id Defs
  deriving (Eq, Show)

type Defs = (Span, [(Span, Def)])

data FixDir = L | R | None deriving (Eq, Show)

data Def
  = BindExp Exp
  | Def Exp Exp
  | Data Exp Defs
  | Struct Exp Defs
  | Fix FixDir Int Id
  deriving (Eq, Show)

data OpOrIdent = Op | Ident
  deriving (Eq, Show)

data ConOrVar = Con | Var
  deriving (Eq, Show)

data Exp
  = Id Span OpOrIdent ConOrVar ByteString
  | App Span Exp [Exp]
  | Fn Span Defs
  | Asc Span Exp Exp
  | Arrow Span Exp Exp
  | Wild Span
  | Const Span Constant
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
  deriving (Eq, Show)

data Constant
  = EInt Integer
  | EFloat Double
  | EChar ByteString
  | EString ByteString
  deriving (Eq, Show)

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

class PP t where
  pp :: t -> Doc

class PP t => IsAST t where
  isValid :: t -> ValidErrs
  span :: t -> Span
  allSpans :: t -> [Span]
  fullParen :: t -> t
  noParen :: t -> t

instance PP t => PP (Span, t) where
  pp (_, t) = pp t

instance IsAST t => IsAST (Span, t) where
  isValid (_, t) = isValid t
  span (s, _) = s
  allSpans (s, t) = s : allSpans t
  fullParen (s, t) = (s, fullParen t)
  noParen (s, t) = (s, noParen t)

instance PP t => PP [t] where
  pp = vcat . fmap pp

instance IsAST t => IsAST [t] where
  isValid ts = concatMap isValid ts
  span [] = error "span []"
  span [a] = span a
  span (a:as) = span a <> span as
  allSpans = concatMap allSpans
  fullParen ts = fullParen <$> ts
  noParen ts = noParen <$> ts

ppOp :: Exp -> Doc -> Exp -> Doc
ppOp e1 op e2 = hang (pp e1 <+> op) 2 (pp e2)

text :: ByteString -> Doc
text = PP.text . UTF8.toString

ppBlock :: Doc -> Defs -> Doc
ppBlock lhs (_, []) = lhs <+> text "{}"
ppBlock lhs (_, [d]) = hsep [lhs, lbrace, nest 2 (pp d), rbrace]
ppBlock lhs (_, ds) = vcat [lhs <+> lbrace, text "", nest 2 (pp ds), rbrace]

ppDef :: Doc -> Doc -> Exp -> Doc
ppDef lhs eq (Block ds) = ppBlock (lhs <+> eq) ds
ppDef lhs eq e = hang (lhs <+> eq) 2 (pp e)

allSpans2 :: (IsAST a, IsAST b) => a -> b -> [Span]
allSpans2 a b = allSpans a <> allSpans b

instance PP Exp where
  pp (Id _ Ident _ e) = text e
  pp (Id _ Op _ o) = parens (text o)
  pp (App _ o [a, b]) | null $ isOppy o = pp a <+> ppOppy o <+> pp b
  pp (App _ e1 e2) = pp e1 <+> sep (pp <$> e2)
  pp (Fn _ body) = ppBlock (text "fn") body
  pp (Asc _ e t) = ppOp e (text ":") t
  pp (Arrow _ a b) = ppOp a (text "->") b
  pp (Wild _) = text "_"
  pp (Const _ (EInt i)) = integer i
  pp (Const _ (EFloat d)) = double d
  pp (Const _ (EChar c)) = PP.text (show c)
  pp (Const _ (EString s)) = PP.text (show s)
  pp (Ops e []) = pp e
  pp (Ops e ((o, e2) : es)) = ppOp e (ppOppy o) (Ops e2 es)
  pp (Case _ e ds) = ppDef (text "case") (pp e) (Block ds)
  pp (If _ i t e) =
    vcat [text "if" <+> pp i,
          hang (text "then") 2 (pp t), hang (text "else") 2 (pp e)]
  pp (IfMatch _ p i t e) =
    vcat [text "if" <+> hang (pp p <+> text "=") 4 (pp i),
          hang (text "then") 2 (pp t), hang (text "else") 2 (pp e)]
  pp (Dot _ (e:es)) = pp e <> hcat ((text "." <>) . pp <$> es)
  pp (Dot _ []) = PP.empty
  pp (Paren _ e) = parens (pp e)
  pp (Tuple _ es) = parens (hsep $ punctuate (text ",") (pp <$> es))
  pp (List _ es) = brackets (hsep $ punctuate (text ",") (pp <$> es))
  pp (Do _ p e ds) =
    ppDef (text "do") (hang (pp p <+> text "<-") 4 (pp e)) (Block ds)
  pp (Assign _ l e) = ppOp l (text ":=") e
  pp (Block ds) = ppBlock mempty ds
  pp (OpExp _ e) = hcat [text "`", pp e, text "`"]

instance IsAST Exp where
  isValid (Id _ _ _ _) = []
  isValid (App _ e1 e2) = isValid e1 <> isValid e2
  isValid (Fn _ body) = isFn body
  isValid (Asc _ e t) = isValid e <> isTy t
  isValid (Arrow s _ _) = [(s, "Arrow type in expression")]
  isValid (Wild s) = [(s, "Wildcard in expression")]
  isValid (Const _ _) = []
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
  span (Id s _ _ _) = s
  span (App s _ _) = s
  span (Fn s _) = s
  span (Asc s _ _) = s
  span (Arrow s _ _) = s
  span (Wild s) = s
  span (Const s _) = s
  span (Ops e []) = span e
  span (Ops e os) = span e <> span (snd $ last os)
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
  allSpans (Id s _ _ _) = [s]
  allSpans (App s e es) = s : allSpans (e:es)
  allSpans (Fn s ds) = s : allSpans ds
  allSpans (Asc s t e) = s : allSpans2 t e
  allSpans (Arrow s a b) = s : allSpans2 a b
  allSpans (Wild s) = [s]
  allSpans (Const s _) = [s]
  allSpans (Ops e []) = allSpans e
  allSpans (Ops e os) = allSpans e <> concatMap (\(a,b) -> allSpans a <> allSpans b) os
  allSpans (Case s e bs) = s : allSpans2 e bs
  allSpans (If s c t e) = s : allSpans [c, t, e]
  allSpans (IfMatch s p c t e) = s : allSpans [p, c, t, e]
  allSpans (Dot s es) = s : allSpans es
  allSpans (Paren s e) = s : allSpans e
  allSpans (Tuple s es) = s : allSpans es
  allSpans (List s es) = s : allSpans es
  allSpans (Do s p e bs) = s : allSpans2 p e <> allSpans bs
  allSpans (Assign s p e) = s : allSpans2 p e
  allSpans (Block ds) = allSpans ds
  allSpans (OpExp s e) = s : allSpans e
  fullParen e@(Id _ _ _ _) = e
  fullParen (App s e1 es) = par (App s (fp e1) (fmap fp es))
  fullParen (Fn s body) = par (Fn s (fp body))
  fullParen (Asc s e t) = par (Asc s (fp e) (fp t))
  fullParen (Arrow s a b) = par (Arrow s (fp a) (fp b))
  fullParen e@(Wild _) = e
  fullParen e@(Const _ _) = e
  fullParen (Ops e ops) =
    par (Ops (fp e) ((\(op, e2) -> (fpe op, fp e2)) <$> ops))
  fullParen (Case s e ds) = par (Case s (fp e) (fp ds))
  fullParen (If s i t e) =
    par (If s (fpe i) (fpe t) (fpe e))
  fullParen (IfMatch s p i t e) =
    par (IfMatch s (fp p) (fp i) (fpe t) (fpe e))
  fullParen (Dot s es) = Dot s (map fp es)
  fullParen (Paren s e) = Paren s (fpe e)
  fullParen (Tuple s es) = Tuple s (fpe <$> es)
  fullParen (List s es) = List s (fpe <$> es)
  fullParen (Do s p e ds) = par (Do s (fp p) (fp e) (fp ds))
  fullParen (Assign s l e) = par (Assign s (fp l) (fp e))
  fullParen (Block ds) = Block (fp ds)
  fullParen (OpExp s e) = OpExp s (fpe e)
  noParen e@(Id _ _ _ _) = e
  noParen (App s e1 es) = App s (noParen e1) (noParen es)
  noParen (Fn s ds) = Fn s (noParen ds)
  noParen (Asc s e t) = Asc s (noParen e) (noParen t)
  noParen (Arrow s a b) = Arrow s (noParen a) (noParen b)
  noParen e@(Wild _) = e
  noParen e@(Const _ _) = e
  noParen (Ops e ops) =
    Ops (noParen e) ((\(op, e2) -> (noParen op, noParen e2)) <$> ops)
  noParen (Case s e ds) = Case s (noParen e) (noParen ds)
  noParen (If s i t e) = If s (noParen i) (noParen t) (noParen e)
  noParen (IfMatch s p i t e) = IfMatch s (noParen p) (noParen i) (noParen t) (noParen e)
  noParen (Dot s es) = Dot s (map noParen es)
  noParen (Paren _ e) = noParen e
  noParen (Tuple s es) = Tuple s (noParen <$> es)
  noParen (List s es) = List s (noParen <$> es)
  noParen (Do s p e ds) = Do s (noParen p) (noParen e) (noParen ds)
  noParen (Assign s l e) = Assign s (noParen l) (noParen e)
  noParen (Block ds) = Block (noParen ds)
  noParen (OpExp s e) = OpExp s (noParen e)

isOppy :: Exp -> ValidErrs
isOppy (Id _ Op _ _) = []
isOppy (OpExp _ e) = isValid e
isOppy e = [(span e, "Not a valid operator")]

ppOppy :: Exp -> Doc
ppOppy (Id _ Op _ o) = text o
ppOppy e@(OpExp _ _) = pp e
ppOppy (Paren _ e) = ppOppy e
ppOppy e = pp (OpExp (span e) e)

isArgs :: Exp -> ValidErrs
isArgs (App _ a e) = isArgs a <> concatMap isPat e
isArgs e = isPat e

isFnBind :: (Span, Def) -> ValidErrs
isFnBind (_, Def p e) = isArgs p ++ isValid e
isFnBind (s, _) = [(s, "Not a valid function disjunct")]

isFn :: Defs -> ValidErrs
isFn (s, []) = [(s, "Empty function definiton")]
isFn (_, ps) = concatMap isFnBind ps

isPat :: Exp -> ValidErrs
isPat (App _ a es) = isPatL a <> concatMap isPat es
isPat (Asc _ e t) = isPat e <> isTy t
isPat (Id _ _ _ _) = []
isPat (Wild _) = []
isPat (Const _ _) = []
isPat (Paren _ e) = isPat e
isPat (Tuple _ es) = concatMap isPat es
isPat (List _ es) = concatMap isPat es
isPat (Block ds) = isRecPat ds
isPat e = [(span e, "Not a valid pattern")]

isPatL :: Exp -> ValidErrs
isPatL (Id _ _ Con _) = []
isPatL (App _ a es) = isPatL a <> concatMap isPat es
isPatL (Asc _ e t) = isPatL e <> isTy t
isPatL (Paren _ e) = isPatL e
isPatL e = [(span e, "Not a valid pattern head")]

isRecPat :: Defs -> ValidErrs
isRecPat (_, ps) = concatMap isFieldBind ps

isFieldBind :: (Span, Def) -> ValidErrs
isFieldBind (_, Def (Id _ _ Var _) e) = isPat e
isFieldBind (s, _) = [(s, "Not a valid field pattern")]

instance PP Def where
  pp (BindExp e) = pp e
  pp (Def pat e) = ppDef (pp pat) (text "=") e
  pp (Data pat ds) = ppDef (pp pat) (text "= data") (Block ds)
  pp (Struct pat ds) = ppDef (pp pat) (text "= struct") (Block ds)
  pp (Fix L i (_, o)) = text "infixl" <+> int i <+> text o
  pp (Fix R i (_, o)) = text "infixr" <+> int i <+> text o
  pp (Fix None i (_, o)) = text "infix" <+> int i <+> text o

instance IsAST Def where
  isValid (BindExp e) = isValid e
  isValid (Def pat e) = isLHS pat <> isValid e
  isValid (Data pat ds) = isTyCon pat <> isData ds
  isValid (Struct pat ds) = isTyCon pat <> isStruct ds
  -- isValid (Fun e ds) = isFunDef e <> isValid ds
  isValid (Fix _ _ _) = []
  span = error "span Def bereft of its span"
  allSpans (BindExp e) = allSpans e
  allSpans (Def p e) = allSpans2 p e
  allSpans (Data p ds) = allSpans2 p ds
  allSpans (Struct p ds) = allSpans2 p ds
  allSpans (Fix _ _ _) = []
  fullParen (BindExp e) = BindExp (fpe e)
  fullParen (Def pat e) = Def (fpe pat) (fpe e)
  fullParen (Data pat ds) = Data (fpe pat) (fp ds)
  fullParen (Struct pat ds) = Struct (fpe pat) (fp ds)
  fullParen d@(Fix _ _ _) = d
  noParen (BindExp e) = BindExp (noParen e)
  noParen (Def pat e) = Def (noParen pat) (noParen e)
  noParen (Data pat ds) = Data (noParen pat) (noParen ds)
  noParen (Struct pat ds) = Struct (noParen pat) (noParen ds)
  noParen d@(Fix _ _ _) = d

isLHS :: Exp -> ValidErrs
isLHS (App _ a es) = isLHS a <> concatMap isPat es
isLHS (Asc _ a t) = isLHS a <> isTy t
isLHS (Id _ _ _ _) = []
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
isTyCon (Id _ _ Con _) = []
isTyCon (App _ a e) = isTyCon a <> concatMap isTyArg e
isTyCon (Asc _ e t) = isTyCon e <> isTy t
isTyCon (Paren _ e) = isTyCon e
isTyCon e = [(span e, "Not a valid Type Constructor")]

isTyArg :: Exp -> ValidErrs
isTyArg (Asc _ e t) = isTyArg e <> isTy t
isTyArg (Id _ _ Var _) = []
isTyArg (Paren _ e) = isTyArg e
isTyArg e = [(span e, "Not a valid type argument")]

isData :: Defs -> ValidErrs
isData (_, ps) = concatMap isConDef ps

isConDef :: (Span, Def) -> ValidErrs
isConDef (_, BindExp (Asc _ c t)) = isCon c <> isTy t
isConDef (_, BindExp e) = isConDefApp e
isConDef (s, _) = [(s, "Not a valid constructor definition")]

isCon :: Exp -> ValidErrs
isCon (Id _ _ Con _) = []
isCon (Paren _ e) = isCon e
isCon e = [(span e, "Not a constructor name in ascribed constructor def")]

isConDefApp :: Exp -> ValidErrs
isConDefApp (Id _ _ Con _) = []
isConDefApp (App _ a e) = isConDefApp a <> concatMap isTy e
isConDefApp (Paren _ e) = isConDefApp e
isConDefApp e = [(span e, "Not a valid constructor name in short constructor def")]

isStruct :: Defs -> ValidErrs
isStruct (_, ps) = concatMap isFieldDef ps

isFieldDef :: (Span, Def) -> ValidErrs
isFieldDef (_, BindExp (Asc _ c t)) = isFieldName c <> isTy t
isFieldDef (s, _) = [(s, "Invalid field definition")]

isFieldName :: Exp -> ValidErrs
isFieldName (Id _ _ Var _) = []
isFieldName (Paren _ e) = isFieldName e
isFieldName e = [(span e, "Invalid field name")]

isTy :: Exp -> ValidErrs
isTy (Id _ _ _ _) = []
isTy (App _ a b) = isTy a <> concatMap isTy b
isTy (Asc _ t k) = isTy t <> isTy k
isTy (Arrow _ a b) = isTy a <> isTy b
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
