{-# LANGUAGE OverloadedStrings #-}
module Names(
  Name(..), TakenNames, taken0,
  GL(..),
  mangle, takeName, untaken,
  orig, mangling, funcOf,
  contextArg, envArg
) where
import AST(Var, PP(..))
import Parse(isIdCont)

import Data.ByteString(ByteString)
import Data.ByteString.UTF8(fromString)
import qualified Data.ByteString.Char8 as CS
import Data.Char(isDigit)
import Data.Map as M
import Data.Set as S
import Numeric(showHex)
import qualified Text.PrettyPrint as PP

-- CodeGen names, as opposed to the Variables and Identifiers in the input language.
type Mangled = ByteString

-- Should we use global or local name mangling?  Local is still unique within a file,
-- but they mangle differently.
data GL = Global | Local
  deriving (Eq, Show)

data Name = N Var Mangled Integer -- orig, mangled, suffix
  deriving (Show)

instance Eq Name where
  N _ b i == N _ b' i' = b == b' && i == i'

instance Ord Name where
  compare (N _ b i) (N _ b' i') = compare b b' <> compare i i'

instance PP Name where
  pp (N _ m (-1)) = pp m
  pp (N _ m i) = pp m <> PP.integer i

type TakenNames = Map ByteString (Set Integer)

unPrime :: Var -> Mangled
unPrime s = CS.intercalate "_P" $ CS.split '\'' s

-- Given a proposed name, search for the
-- first untaken version (approximated by the
-- first available trailing digit after the
-- maximum one seen).
untaken :: Var -> Mangled -> GL -> TakenNames -> Name
untaken o m gl = untaken' o m (initNum gl)

untaken' :: Var -> Mangled -> Integer -> TakenNames -> Name
untaken' o m n taken = do
  let s = M.findWithDefault mempty m taken
      sf = M.findWithDefault mempty (m <> "_FUNC") taken
  if n `S.notMember` s && n `S.notMember` sf then
    N o m n
  else if n == (-1) then
    untaken' o ("_" <> m) n taken
  else
    N o m (1 + S.findMax s)

initNum :: GL -> Integer
initNum Global = -1
initNum _ = 0

opEncodings :: Map Char ByteString
opEncodings = M.fromList [
  ('\'', "P"),
  ('_', "_"),
  (':', "C"),
  (';', "S"),
  ('+', "p"),
  ('-', "m"),
  ('*', "t"),
  ('/', "d"),
  ('%', "m"),
  ('&', "a"),
  ('|', "o"),
  ('!', "n"),
  ('~', "T"),
  ('=', "e"),
  ('>', "g"),
  ('<', "l"),
  ('@', "A"),
  ('#', "s"),
  ('$', "D"),
  ('^', "x"),
  ('?', "q"),
  ('\\', "b")
  ]

contextArg :: Name
contextArg = N "ling_ctxt" "ling_ctxt" (-1)

envArg :: Name
envArg = N "ling_env" "ling_env" (-1)

cKeys :: [Var]
cKeys =  [
  "alignas",
  "alignof",
  "auto",
  "bool",
  "break",
  "case",
  "catch",
  "char",
  "class",
  "const",
  "consteval",
  "constexpr",
  "constinit",
  "continue",
  "decltype",
  "default",
  "delete",
  "do",
  "double",
  "enum",
  "explicit",
  "extern",
  "false",
  "float",
  "for",
  "friend",
  "goto",
  "int",
  "long",
  "mutable",
  "namespace",
  "new",
  "Nil",
  "NULL",
  "nullptr",
  "noexcept",
  "operator",
  "private",
  "protected",
  "public",
  "register",
  "return",
  "short",
  "signed",
  "sizeof",
  "static",
  "static_assert",
  "struct",
  "switch",
  "template",
  "this",
  "thread_local",
  "throw",
  "true",
  "try",
  "Tuple",
  "typedef",
  "typeid",
  "typename",
  "union",
  "unsigned",
  "using",
  "virtual",
  "void",
  "volatile",
  "while"
  ]

rts :: [Var]
rts = [
  "ling_apply", -- general apply (ctxt, clo, n, args...)
  "ling_context", -- context type
  "ling_ctxt", -- context arg
  "ling_desc", -- desc type
  "ling_desc_is",
  "ling_env", -- env arg
  "ling_field", -- field getter (obj, n) numbering from 0
  "ling_new_obj", -- allocate (ctxt, desc, args...)
  "LING_OBJ", -- static object creation
  "ling_obj", -- object type
  "ling_pap", -- partial app (ctxt, desc, n, args...)
  "ling_tuple", -- tuple (ctxt, n, args...)
  "ling_unreachable" -- 0-ary error function
  ]

taken0 :: TakenNames
taken0 = M.fromList . fmap (, S.singleton (-1)) $ (cKeys <> rts)


encodeOp :: Char -> ByteString
encodeOp c =
  case M.lookup c opEncodings of
    Just s -> s
    Nothing -> "X"<> fromString (showHex (fromEnum c) "_")

mangle :: Var -> GL -> TakenNames -> Name
mangle "()" = \_ _ -> N "()" "Tuple" (-1)
mangle "[]" = \_ _ -> N "[]" "Nil" (-1)
mangle v = do
  let v' = unPrime v
  case CS.spanEnd isDigit v' of
    (v'', n) | Just (n', "") <- CS.readInteger n ->
      -- Ident123 -> Ident 123
      const (untaken' v v'' n')
    _ | CS.all isIdCont v -> untaken v v' -- Ident
      | otherwise -> -- Op
        untaken v ("_0p_" <> CS.concatMap encodeOp v)

takeName :: Name -> TakenNames -> TakenNames
takeName (N _ m n) taken =
  M.insertWith (<>) (m <> "_FUNC") (S.singleton n) $
  M.insertWith (<>) m (S.singleton n) taken

orig :: Name -> Var
orig (N o _ _) = o

mangling :: Name -> Mangled
mangling (N _ m _) = m

funcOf :: Name -> PP.Doc
funcOf nm = pp nm <> "_FUNC"
