{-# LANGUAGE OverloadedStrings #-}
module AST(
  Span(..), noSpan, Mod(Mod), Imports, Var, Id, Import, Defs, FixDir(..),
  Def(..), OpOrIdent(..), ConOrVar(..), Pat, Exp(..), Constant(..),
  ValidErrs, PP(..), showPp, showsPp, IsAST(..),
  Arity, DefGroup(..), Clause, GroupFun, groupDefs, patToPats, patsToPat, isVar
) where
import Data.ByteString(ByteString)
import Data.Char(isUpper)
import Data.Set hiding (null, map, foldr, difference)
import qualified Data.Set as S
import Data.Map as M hiding (null, map, foldr, difference)
import Data.ByteString.UTF8(toString, fromString)
import GHC.Stack(HasCallStack)
import Prelude hiding (span)
import Text.Megaparsec(SourcePos)
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint(
  Doc, (<+>), braces, lbrace, rbrace,
  brackets, double, hang,
  fsep, int, integer, hcat, hsep, sep, text,
  nest, parens, punctuate, vcat)

noSpan :: Span
noSpan = S 0 0

-- A span is a pair of file offsets.
data Span = S Int Int
  deriving (Show)

-- We don't care about source location for equality.
instance Eq Span where
  _ == _ = True

instance Semigroup Span where
  S 0 0 <> b = b
  a <> S 0 0 = a
  S p0 p1 <> S p2 p3 = S (min p0 p1) (max p2 p3)

instance Monoid Span where
  mempty = noSpan

data Mod = Mod SourcePos Defs Imports Defs
  deriving (Eq, Show)

type Imports = [Import]

type Var = ByteString
type Id = (Span, Var)

data Import = Import Span Id Defs
  deriving (Eq, Show)

type Defs = (Span, [(Span, Def)])

data FixDir = L | R | None deriving (Eq, Show)

data Def
  = BindExp Exp
  | Def Pat Exp
  | Data Exp Defs
  | Struct Exp Defs
  | Fix FixDir Int Id
  deriving (Eq, Show)

data OpOrIdent = Op | Ident
  deriving (Eq, Show)

data ConOrVar = Con | Var
  deriving (Eq, Show)

type Pat = Exp

data Exp
  = Id Span OpOrIdent ConOrVar ByteString
  | App Span [Exp]
  | Fn Span Defs
  | Asc Span Exp Exp
  | Arrow Span Exp Exp
  | Wild Span
  | Const Span Constant
  | Ops Exp [(Exp, Exp)]
  | Case Span Exp Defs
  | If Span Exp Exp Exp
  | IfMatch Span Pat Exp Exp Exp
  | Dot Span [Exp]
  | Paren Span Exp
  | Tuple Span [Exp]
  | List Span [Exp]
  | Do Span Pat Exp Defs
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

instance PP Doc where
  pp = id

instance PP ByteString where
  pp = text . toString

showPp :: PP a => a -> String
showPp = show . pp

showsPp :: PP a => [a] -> String
showsPp as = show (fsep (pp <$> as))

class PP t => IsAST t where
  isValid :: t -> ValidErrs
  span :: t -> Span
  allSpans :: t -> [Span]
  fullParen :: t -> t
  noParen :: t -> t
  isValue :: t -> Bool
  fv :: t -> Set Var

instance PP t => PP (Span, t) where
  pp (_, t) = pp t

instance IsAST t => IsAST (Span, t) where
  isValid (_, t) = isValid t
  span (s, _) = s
  allSpans (s, t) = s : allSpans t
  fullParen (s, t) = (s, fullParen t)
  noParen (s, t) = (s, noParen t)
  isValue (_, t) = isValue t
  fv (_, t) = fv t

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
  isValue ts = all isValue ts
  fv ts = foldMap fv ts

instance (PP k, PP v) => PP (Map k v) where
  pp m = braces $ hsep $ punctuate "," $ fmap (\(k,v) -> pp k <+> "->" <+> pp v) $ M.toList m

ppOp :: Exp -> Doc -> Exp -> Doc
ppOp e1 op e2 = hang (pp e1 <+> op) 2 (pp e2)

ppBlock :: Doc -> Defs -> Doc
ppBlock lhs (_, []) = lhs <+> "{}"
ppBlock lhs (_, [d]) = hsep [lhs, lbrace, nest 2 (pp d), rbrace]
ppBlock lhs (_, ds) = vcat [lhs <+> lbrace, "", nest 2 (pp ds), rbrace]

ppDef :: Doc -> Doc -> Exp -> Doc
ppDef lhs eq (Block ds) = ppBlock (lhs <+> eq) ds
ppDef lhs eq e = hang (lhs <+> eq) 2 (pp e)

allSpans2 :: (IsAST a, IsAST b) => a -> b -> [Span]
allSpans2 a b = allSpans a <> allSpans b

instance PP Constant where
  pp (EInt i) = integer i
  pp (EFloat d) = double d
  pp (EChar c) = PP.text (show c)
  pp (EString s) = PP.text (show s)

instance PP Exp where
  pp (Id _ Ident _ e) = pp e
  pp (Id _ Op _ o) = parens (pp o)
  pp (App _ [o, a, b]) | null $ isOppy o = pp a <+> ppOppy o <+> pp b
  pp (App _ []) = "<BAD: empty app>"
  pp (App _ es) = sep (pp <$> es)
  pp (Fn _ body) = ppBlock "fn" body
  pp (Asc _ e t) = ppOp e ":" t
  pp (Arrow _ a b) = ppOp a "->" b
  pp (Wild _) = "_"
  pp (Const _ c) = pp c
  pp (Ops e []) = pp e
  pp (Ops e ((o, e2) : es)) = ppOp e (ppOppy o) (Ops e2 es)
  pp (Case _ e ds) = ppDef "case" (pp e) (Block ds)
  pp (If _ i t e) =
    vcat ["if" <+> pp i,
          hang "then" 2 (pp t), hang "else" 2 (pp e)]
  pp (IfMatch _ p i t e) =
    vcat ["if" <+> hang (pp p <+> "=") 4 (pp i),
          hang "then" 2 (pp t), hang "else" 2 (pp e)]
  pp (Dot _ (e:es)) = pp e <> hcat (("." <>) . pp <$> es)
  pp (Dot _ []) = PP.empty
  pp (Paren _ e) = parens (pp e)
  pp (Tuple _ es) = parens (hsep $ punctuate "," (pp <$> es))
  pp (List _ es) = brackets (hsep $ punctuate "," (pp <$> es))
  pp (Do _ p e ds) =
    ppDef "do" (hang (pp p <+> "<-") 4 (pp e)) (Block ds)
  pp (Assign _ l e) = ppOp l ":=" e
  pp (Block ds) = ppBlock mempty ds
  pp (OpExp _ e) = hcat ["`", pp e, "`"]

instance IsAST Exp where
  isValid (Id _ _ _ _) = []
  isValid (App s []) = [(s, "Empty App")]
  isValid (App _ es) = isValid es
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
  span (App s _) = s
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
  allSpans (App s es) = s : allSpans es
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
  fullParen (App s es) = par (App s (fmap fp es))
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
  noParen (App s es) = App s (noParen es)
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
  isValue (Id _ _ _ _) = True
  isValue (App _ (f:es)) | all isValue (f:es) = isValueH f where
    isValueH (Id _ _ Con _) = True
    isValueH a@(App _ _) = isValue a
    isValueH (Asc _ e _) = isValueH e
    isValueH (Paren _ e) = isValueH e
    isValueH (OpExp _ e) = isValueH e
    isValueH _ = False
  isValue (Fn _ _) = True
  isValue (Asc _ e _) = isValue e
  isValue (Const _ _) = True
  isValue (Paren _ e) = isValue e
  isValue (Tuple _ es) = all isValue es
  isValue (List _ es) = all isValue es
  isValue (Block ds) = all isValue ds
  isValue (OpExp _ e) = isValue e
  isValue _ = False
  fv (Id _ _ _ v) = S.singleton v
  fv (App _ es) = fv es
  fv (Fn _ ds) = fv ds
  fv (Asc _ e t) = fv e <> fv t
  fv (Arrow _ a b) = fv a <> fv b
  fv (Wild _) = mempty
  fv (Const _ _) = mempty
  fv (Ops e ops) = fv e <> foldMap (\(op, e2) -> fv op <> fv e2) ops
  fv (Case _ e ds) = fv e <> fv ds
  fv (If _ i t e) = fv i <> fv t <> fv e
  fv (IfMatch _ p i t e) = fv i <> ((fv t <> fv e) `difference` fv p)
  fv (Dot _ es) = fv es
  fv (Paren _ e) = fv e
  fv (Tuple _ es) = foldMap fv es
  fv (List _ es) = foldMap fv es
  fv (Do _ p e ds) = fv e <> (fvDefs ds `difference` fv p)
  fv (Assign _ l e) = fv e `difference` fv l
  fv (Block ds) = fvDefs ds
  fv (OpExp _ e) = fv e

-- Subtract away variables bound by a match.
-- Note that this must not include constructors!
difference :: Set Var -> Set Var -> Set Var
difference as bs = as `S.difference` S.filter isVar bs where

-- Based on the name, is this a variable, rather than a constructor?
isVar :: Var -> Bool
isVar "[]" = False -- Used internally as list type constructor and nil.
isVar v =
  case toString v of
    (c:_) -> not (isUpper c || c == ':' || c == '(')
    _ -> error "Var is the empty string"

isOppy :: Exp -> ValidErrs
isOppy (Id _ Op _ _) = []
isOppy (OpExp _ e) = isValid e
isOppy e = [(span e, "Not a valid operator")]

ppOppy :: Exp -> Doc
ppOppy (Id _ Op _ o) = pp o
ppOppy e@(OpExp _ _) = pp e
ppOppy (Paren _ e) = ppOppy e
ppOppy e = pp (OpExp (span e) e)

isArgs :: Exp -> ValidErrs
isArgs (App _ (a:e)) = isArgs a <> concatMap isPat e
isArgs e = isPat e

isFnBind :: (Span, Def) -> ValidErrs
isFnBind (_, Def p e) = isArgs p ++ isValid e
isFnBind (s, _) = [(s, "Not a valid function disjunct")]

isFn :: Defs -> ValidErrs
isFn (s, []) = [(s, "Empty function definiton")]
isFn (_, ps) = concatMap isFnBind ps

isPat :: Exp -> ValidErrs
isPat a@(App _ _) = isPatL a
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
isPatL (App s []) = [(s, "Empty app in pat")]
isPatL (App _ (a:es)) = isPatL a <> concatMap isPat es
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
  pp (Def pat e) = ppDef (pp pat) "=" e
  pp (Data pat ds) = ppDef (pp pat) "= data" (Block ds)
  pp (Struct pat ds) = ppDef (pp pat) "= struct" (Block ds)
  pp (Fix L i (_, o)) = "infixl" <+> int i <+> pp o
  pp (Fix R i (_, o)) = "infixr" <+> int i <+> pp o
  pp (Fix None i (_, o)) = "infix" <+> int i <+> pp o

instance IsAST Def where
  isValid (BindExp e) = isValid e
  isValid (Def pat e) = isLHS pat <> isValid e
  isValid (Data pat ds) = isTyCon pat <> isData ds
  isValid (Struct pat ds) = isTyCon pat <> isStruct ds
  isValid (Fix _ _ _) = []
  span (BindExp e) = span e
  span (Def pat e) = span pat <> span e
  span (Data pat ds) = span pat <> span ds
  span (Struct pat ds) = span pat <> span ds
  span (Fix _ _ (s, _)) = s
  allSpans (BindExp e) = allSpans e
  allSpans (Def p e) = allSpans2 p e
  allSpans (Data p ds) = allSpans2 p ds
  allSpans (Struct p ds) = allSpans2 p ds
  allSpans (Fix _ _ (s, _)) = [s]
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
  isValue (BindExp e) = isValue e
  isValue (Def _ e) = isValue e
  isValue _ = True
  fv (BindExp e) = fv e
  fv (Def pat e) = fv pat <> fv e
  fv (Data _ _) = mempty
  fv (Struct _ _) = mempty
  fv (Fix _ _ _) = mempty

isLHS :: Exp -> ValidErrs
isLHS (App s []) = [(s, "Empty app in LHS")]
isLHS (App _ (a:es)) = isLHS a <> concatMap isPat es
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
isTyCon (App s []) = [(s, "Empty app in TyCon")]
isTyCon (App _ (a:e)) = isTyCon a <> concatMap isTyArg e
isTyCon (Asc _ e t) = isTyCon e <> isTy t
isTyCon (Paren _ e) = isTyCon e
isTyCon (List _ []) = []
isTyCon (List _ [t]) = isTy t
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
isConDefApp (App s []) = [(s, "Empty app in ConDef")]
isConDefApp (App _ (a:e)) = isConDefApp a <> concatMap isTy e
isConDefApp (Paren _ e) = isConDefApp e
isConDefApp (List _ []) = []
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
isTy (App s []) = [(s, "Empty app in Ty")]
isTy (App _ b) = concatMap isTy b
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

type Arity = Int

type Clause = (Span, [Pat], Exp)
type GroupFun = (Span, Var, Arity, Maybe Exp, [Clause])
data DefGroup
  = D Span Def
  | Fns [GroupFun]
  | Record (Map Var Exp)
  deriving (Eq, Show)

instance PP DefGroup where
  pp (D _ d) = pp d
  pp (Record m) = pp [(Def (Id noSpan Ident Var f) e) | (f, e) <- M.toList m]
  pp (Fns m) = PP.vcat $ concat [
    ["-- Group:"],
    [pp d |
      (s, nm, _, sig, pes) <- m,
      let i = Id s Ident Var nm,
      d <- maybe id (\t -> (BindExp (Asc (span t) i t):)) sig $
           [ Def (App s (i:ps)) e | (_, ps, e) <- pes ]],
    ["-- End group"]]

instance IsAST DefGroup where
  isValid (D _ d) = isValid d
  isValid (Record m) = concatMap isValid (M.elems m)
  isValid (Fns gs) =
    [ err |
      (_, _, _, sig, ds) <- gs,
      (_, as, e) <- ds,
      err <- maybe [] isTy sig <> concatMap isPat as <> isValid e ]
  span (D s _) = s
  span (Record m) = foldl1 (<>) (span <$> M.elems m)
  span (Fns gs) = foldl1 (<>) [ s | (s, _, _, _, _) <- gs]
  allSpans (D s d) = s : allSpans d
  allSpans (Record m) = concatMap allSpans $ M.elems m
  allSpans (Fns gs) =
    [ s | (s0, _, _, sig, ds) <- gs,
          s <- s0 : maybe [] allSpans sig <>
               [ s1 | (sd, as, e) <- ds, s1 <- sd : allSpans as <> allSpans e]]
  fullParen (D s d) = D s (fullParen d)
  fullParen (Record m) = Record (fullParen <$> m)
  fullParen (Fns gs) =
    Fns [ (s, v, a, fullParen <$> sig,
           [(sd, fullParen as, fullParen e) | (sd, as, e) <- ds]) |
          (s,v,a,sig,ds) <- gs ]
  noParen (D s d) = D s (noParen d)
  noParen (Record m) = Record (noParen <$> m)
  noParen (Fns gs) =
    Fns [ (s, v, a, noParen <$> sig,
           [(sd, noParen as, noParen e) | (sd, as, e) <- ds]) |
          (s,v,a,sig,ds) <- gs ]
  isValue (D _ d) = isValue d
  isValue (Record m) = all isValue (M.elems m)
  isValue (Fns _) = True
  fv (Fns fs) = S.unions [ fv e `difference` fv ps |
                           (_, _, _, _, rs) <- fs, (_, ps, e) <- rs ]
  fv g = fvGroup g mempty

fvDefs :: Defs -> Set Var
fvDefs ds =
  case groupDefs ds of
    Left _ -> fv ds
    Right gs -> foldr fvGroup mempty gs

fvGroup :: DefGroup -> Set Var -> Set Var
fvGroup (Record r) later = later <> fv (M.elems r)
fvGroup (D _ (BindExp (Asc _ (Id _ _ _ i) _))) later =
  later `difference` S.singleton i
fvGroup (D s (BindExp (Paren _ e))) later =
  fvGroup (D s (BindExp e)) later
fvGroup (D s (BindExp (Asc s' (Paren _ e) t))) later =
  fvGroup (D s (BindExp (Asc s' e t))) later
fvGroup (D _ (Def pat e)) later = fv e <> (later `difference` fv pat)
fvGroup (D _ d) later = later <> fv d
fvGroup (Fns fs) later = (later <> rhs) `difference` vs
  where vs = S.fromList [ v | (_, v, _, _, _) <- fs ]
        rhs = fv (Fns fs)

groupDefs :: HasCallStack => Defs -> Either ValidErrs [DefGroup]
groupDefs (_, ds) =
  case foldr groupDef (Right []) ds of
    Right [] -> Right [Record mempty]
    r -> r

groupDef :: HasCallStack => (Span, Def) -> Either ValidErrs [DefGroup] -> Either ValidErrs [DefGroup]
-- groupDef (s, Def (App s' (Asc _ p t : ps)) e) ts =
--   groupDef (s, Def (App s' (p : ps)) e) ts
-- Turn in-expr ascriptions into standalone
groupDef (s, Def a@(Asc s' i@(Id _ _ Var _) _) e) ts =
  groupDef (s', BindExp a) $ groupDef (s, Def i e) ts
groupDef (s, Def i@(Id _ _ _ _) (Asc s' e t)) ts =
  groupDef (s', BindExp (Asc s' i t)) $ groupDef (s, Def i e) ts
-- App flattening to improve binding group identification
groupDef (s, Def (App s' (App _ ps : ps')) e) ts =
  groupDef (s, Def (App s' (ps ++ ps')) e) ts
-- Binding group handling.  Fndef with existing group
groupDef (s, Def (App _ (Id _ _ Var f : ps)) e)
         (Right (Fns (c@(s', ff, n, sig, pes): fns) : ts))
  | f == ff =
    if sig /= Nothing then
      Left [(s, ("Partial definition before signature of "<>f))]
    else if n /= length ps then
      Left [(s, ("Arity mismatch in definition of " <> f))]
    else
      Right (Fns ((s <> s', ff, n, Nothing, (s, ps, e):pes) : fns) : ts)
  | otherwise =
    Right (Fns ((s, f, length ps, Nothing, [(s, ps, e)]) : c : fns) : ts)
-- New fndef binding group
groupDef (s, Def (App _ (Id _ _ Var f : ps)) e) (Right ts) =
  Right (Fns [(s, f, length ps, Nothing, [(s, ps, e)])] : ts)
-- Ascription in binding group
groupDef (s, BindExp (Asc _ (Id _ _ Var f) t))
         (Right (Fns ((s', ff, n, sig, pes): fns) : ts))
  | f == ff =
    case sig of
      Just sg ->
        Left [(s, ("Doubled signature for " <> f)), (span sg, "Second signature")]
      Nothing ->
        Right (Fns ((s', ff, n, Just t, pes): fns) : ts)
groupDef (s, Def i@(Id _ _ _ _) (Paren _ e)) ts = groupDef (s, Def i e) ts
groupDef (s, Def (Id _ _ Var f) (Fn _ ds)) (Right (Fns m : bs)) =
  Right (Fns (fnToGroup s f ds : m) : bs)
groupDef (s, Def (Id _ _ Var f) (Fn _ ds)) (Right bs) =
  Right (Fns [fnToGroup s f ds] : bs)
groupDef (s, BindExp (Asc s' (Paren _ e) t)) ts =
  groupDef (s, BindExp (Asc s' e t)) ts
groupDef (_, Def (Id _ _ Var var) e) (Right []) = Right [Record (M.singleton var e)]
groupDef (_, Def (Id _ _ Var var) e) (Right [Record m]) = Right [Record (M.insert var e m)]
groupDef (s, d) (Right (Record _ : _)) = Left [(s, fromString (show (pp d)) <> " is not a struct binding")]
groupDef (s, d@(BindExp _)) (Right ts) = Right ((D s d):ts)
groupDef (s, Def (Asc _ p _) e) ts = groupDef (s, Def p e) ts
groupDef (s, d) (Right ts) = Right (D s d : ts)
groupDef _ (Left e) = Left e

fnToGroup :: Span -> Var -> Defs -> (Span, Var, Arity, Maybe Exp, [Clause])
fnToGroup s f (_, ds) = (s, f, aty cs, Nothing, cs) where
  cs :: [Clause] = map defToClause ds
  aty [] = error "Empty clauses"
  aty ((_, ps, _):_) = length ps
  defToClause (sd, Def p e) = (sd, patToPats p, e)
  defToClause (_, d) = error ("Bad clause " <> showPp d)

-- Turn a singleton pattern from case to a clausal list of patterns
patToPats :: Pat -> [Pat]
patToPats (Asc _ p _) = patToPats p
patToPats (Paren _ p) = [p]
patToPats (App _ ps) = ps
patToPats p = [p]

-- Turn a clausal list of patterns into a match pattern
patsToPat :: [Pat] -> Pat
patsToPat [] = error "patsToPat []"
patsToPat [p] = Paren (span p) p
patsToPat ps = App (span ps) ps
