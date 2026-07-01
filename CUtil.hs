{-# LANGUAGE OverloadedStrings #-}
module CUtil(
  ($*$), Var, Doc, Code, PP(..),
  cCommas,
  cCall, cObjDeclAssign, cObjDecl, cObjAssign,
  cFuncDecl, cFuncHeader, cReturn, cIf,
  cArray, cArgArray,
  Label, cLabel, cGoto,
  cMatchError,
  cDesc, cDescRHS,
  gRef, gString, gInt, gFloat, gChar, gDesc,
  aDesc
) where
import AST(Var, PP(..))
import Names(Name(..), contextArg, funcOf)

import Text.PrettyPrint hiding ((<>))

infixl 5 $*$

-- Vertical separation with blank line,
-- handling mempty properly.
($*$) :: Doc -> Doc -> Doc
a $*$ b
  | isEmpty a = b
  | isEmpty b = a
  | otherwise = a $$ "" $$ b

type Code = Doc
type Label = Integer

cCommas :: [Code] -> Code
cCommas = nest 2 . fsep . punctuate comma

cCall :: Code -> [Code] -> Code
cCall f xs = f <> parens (cCommas xs)

cObjDeclAssign :: Name -> Code -> Code
cObjDeclAssign v code = hang ("ling_obj" <+> pp v <+> equals) 2 (code <> semi)

cObjDecl :: Name -> Code
cObjDecl v = "ling_obj" <+> (pp v <> semi)

cObjAssign :: Name -> Code -> Code
cObjAssign v code = hang (pp v <+> equals) 2 (code <> semi)

cFuncDecl :: Name -> Int -> Code
cFuncDecl n a =
  cCall ("ling_obj" <+> funcOf n) ("ling_context *" : replicate a "ling_obj")

cFuncHeader :: Name -> [Name] -> Code
cFuncHeader n as = do
  let arg a = "ling_obj" <+> pp a
      ps = ("ling_context" <+> ("*" <> pp contextArg)) : fmap arg as
  cCall ("ling_obj" <+> funcOf n) ps

cReturn :: Code -> Code
cReturn c = hang "return" 2 (c <> semi)

cLabel :: Doc -> Label -> Code
cLabel s l = nest (-1) (s <> integer l <> colon <> semi)

cGoto :: Doc -> Label -> Code
cGoto s l = "goto" <+> (s <> integer l <> semi)

cArray :: [Code] -> Code
cArray = braces . cCommas

-- Used in lieu of varargs.
cArgArray :: [Code] -> Code
cArgArray = ("(ling_obj[])" <>) . cArray

-- One-sided if statement
cIf :: Code -> Code -> Code
cIf p t = sep [ hsep [ "if", parens p, lbrace ], nest 2 t, rbrace ]

cMatchError :: String -> Code
cMatchError sloc = cReturn (cCall "ling_match_error" [text (show sloc)])

-- Static descriptor value
cDesc :: Doc -> Var -> Int -> Code
cDesc mangled name arity =
  hsep ["const", "ling_desc", mangled <> "[]", equals] <+> (cDescRHS mangled name arity <> semi)

cDescRHS :: Doc -> Var -> Int -> Code
cDescRHS mangled name arity =
  cArray [cCall "LING_MK_DESC" [ int arity, "&"<>funcOf mangled, text (show name)]]

-- getter forms
gRef :: Doc -> Code
gRef = (<> ".ref")

gDesc :: Doc -> Code
gDesc = (<> ".desc")

gString :: Doc -> Code
gString = (<> ".string")

gInt :: Doc -> Code
gInt = (<> ".int_val")

gFloat :: Doc -> Code
gFloat = (<> ".double_val")

gChar :: Doc -> Code
gChar c = "(char)" <> gInt c

-- argument forms
aDesc :: Doc -> Code
aDesc = cCall "LING_DESC" . (:[])
