{-# LANGUAGE ApplicativeDo, OverloadedStrings #-}
module Parse(file, partialFile, toplevel,
             def, defs, block, exp,
             unfix, unfixExp) where
import AST
import Control.Monad
import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char
import Data.Functor
import Data.Maybe
import Data.Void(Void)
import Data.Map hiding (empty)
import Data.Word(Word8)
import Text.Megaparsec as P
import Text.Megaparsec.Byte
import Text.Megaparsec.Byte.Lexer as L
import Text.Megaparsec.State as PS
import Prelude hiding (exp, span, lookup)

type Error = Void

type MP m = MonadParsec Error ByteString m

data Spacing = NoNL | NL | BT deriving (Eq, Ord, Show)

utf8satisfy :: MP m => (Char -> Bool) -> m ByteString
utf8satisfy p = do
  bs <- getInput
  case UTF8.decode bs of
    Just (c, n) | p c -> BS.take n bs <$ takeP Nothing n
    _ -> empty

utf8span1 :: MP m => (Char -> Bool) -> m ByteString
utf8span1 p = do
  bs <- getInput
  case UTF8.span p bs of
    (rs, _)
      | BS.null rs -> empty
      | otherwise -> rs <$ takeP Nothing (BS.length rs)

quotedString :: MP m => m ByteString
quotedString = do
  let b :: Word8 = fromIntegral (ord '"')
      s :: Word8 = fromIntegral (ord '\\')
      converter bs =
        case reads ('"':UTF8.toString bs ++"\"") of
          [(s, "")] -> return (UTF8.fromString s)
          _ -> empty
      parser = do
        bs <- takeWhileP Nothing (\c -> c /= b)
        single b
        case BS.unsnoc bs of
          Just (_, ss) | s == ss -> (BS.snoc bs b <>) <$> parser
          _ -> return bs
  single b *> parser >>= converter

charLiteral :: MP m => m ByteString
charLiteral = do
  bs <- getInput
  let seg = UTF8.toString (BS.take 16 bs) :: String
  case readLitChar seg of
    [(_, r)] -> do
      let l = UTF8.take (length r - length seg) bs
      l <$ takeP Nothing (BS.length l)
    _ -> empty

utf8span :: MP m => (Char -> Bool) -> m ByteString
utf8span p = do
  bs <- getInput
  case UTF8.span p bs of
    (rs, _) -> rs <$ takeP Nothing (BS.length rs)

sp1 :: MP m => m ()
sp1 = () <$ utf8span1 isSpace

isHSpace :: Char -> Bool
isHSpace c = isSpace c && c /= '\n' && c /= '\r'

hsp1 :: MP m => m ()
hsp1 = () <$ utf8span1 isHSpace

lineSpace :: MP m => m ()
lineSpace = L.space hsp1 empty (skipBlockCommentNested "/*" "*/")

anySpace :: MP m => m ()
anySpace = L.space sp1 (skipLineComment "//") (skipBlockCommentNested "/*" "*/")

spaces :: MP m => Spacing -> m ()
spaces NoNL = lineSpace
spaces _ = anySpace

tok :: MP m => Spacing -> m a -> m (Span, a)
tok s p = do
  start <- getOffset
  r <- p
  end <- getOffset
  spaces s
  pure (S start end, r)

bare :: MP m => Spacing -> m a -> m a
bare s p = p <* optional (spaces s)

semi :: MP m => m ()
semi =() <$ keyOp ";"

isIdCont :: Char -> Bool
isIdCont c = isAlphaNum c || c == '\'' || c == '_'

isIdStart :: Char -> Bool
isIdStart c = isIdCont c && not (isUpper c || isDigit c)

ident :: MP m => Spacing -> m Id
ident s = tok s $ label "id" $ do
  front <- utf8satisfy isIdStart
  rest <- utf8span isIdCont
  let res = front <> rest
  guard (res `notElem` ["fn", "if", "then", "else", "infix", "infixl", "infixr", "data", "struct", "case", "do"])
  pure (front <> rest)

con :: MP m => Spacing -> m Id
con s = tok s $ label "con" $ do
  front <- takeWhileP Nothing (\c -> c == fromIntegral (fromEnum '\'') || c == fromIntegral (fromEnum '_'))
  cap <- utf8satisfy isUpper
  rest <- utf8span isIdCont
  pure (front <> cap <> rest)

key :: MP m => ByteString -> Spacing -> m Span
key kw s = fmap fst $ tok s $ label (UTF8.toString kw) $
  (string kw *> notFollowedBy (utf8satisfy isIdCont))

isOpChar :: Char -> Bool
isOpChar c = (isSymbol c || isPunctuation c) && (c `notElem` ("\'\",()[]{}`" :: String))

isOpStart :: Char -> Bool
isOpStart c = isOpChar c && c /= ':' && c /= '_'

opr :: MP m => m Id
opr = tok NL $ label "op" $ do
  front <- utf8satisfy isOpStart
  rest <- utf8span isOpChar
  let r = front <> rest
  guard (r /= "=" && r /= "->" && r /= ";")
  pure r

conop :: MP m => m Id
conop = tok NL $ label ":conop" $ do
  front <- string ":"
  rest <- utf8span isOpChar
  guard (rest /= "" && rest /= "=")
  pure (front <> rest)

keyOp :: MP m => ByteString -> m Span
keyOp kw = fmap fst $ tok NL $ label (UTF8.toString kw) $
  (string kw *> notFollowedBy (utf8satisfy isOpChar))

parens :: MP m => Spacing -> m t -> m (Span, t)
parens s p = tok s (between (bare NL (string "(")) (string ")") p)

tuple :: MP m => m (Bool, [Exp])
tuple = (fmap . (:) <$> exp NL <*> tupleC) <|> pure (False, [])

-- tuple prefixed by a comma
tupleC :: MP m => m (Bool, [Exp])
tupleC = (comma *> ((True,) . snd <$> tuple)) <|> pure (False, [])


comma :: MP m => m ()
comma = () <$ bare NL (string ",")

-- sign must be tightly spaced, this is how we avoid some ambiguity with operators.
sign :: Num n => MP m => m (n -> n)
sign = (negate <$ string "-") <|> (id <$ string "+") <|> pure id

int :: MP m => Spacing -> m (Span, Integer)
int s = tok s $ label "<integer>" $
  (sign <*> ((string "0" *> (octal <|> (string' "x" *> hexadecimal) <|> (string' "b" *> binary) <|> pure 0)) <|> decimal))

double :: MP m => Spacing -> m (Span, Double)
double s = tok s $ label "<double>" (sign <*> float)

binSpan :: (MP m, IsAST a, IsAST b) => (Span -> a -> b -> c) -> m a -> m b -> m c
binSpan f pa pb = (\a b -> f (span a `uSpan` span b) a b) <$> pa <*> pb

constant :: (a -> Constant) -> (Span, a) -> Exp
constant c (s, v) = Const s (c v)

expSimp :: MP m => Spacing -> m Exp
expSimp s =
  -- delimited things first
  ((\(sp, f) -> f sp) <$> parens s expParens) <|>
  label "[list]" (uncurry List <$> tok s (between (bare NL (string "[")) (string "]") (snd <$> tuple))) <|>
  (Block <$> block s) <|>
  label "\"string\"" (constant EString <$> tok s quotedString) <|>
  label "'char'" (try (constant EChar <$>
                       tok s (between (string "'") (string "'") charLiteral))) <|>
  -- Keyword expressions must come before ids and ops.
  label "fn" ((\f a b -> Fn (f `uSpan` span b) a b) <$> key "fn" NL <*> exp NL <* keyOp "=" <*> exp s) <|>
  label "if" ((\f i t e -> If (f `uSpan` span e) i t e) <$>
              key "if" NL <*> exp NL <* key "then" NL <*> exp NL <* key "else" NL <*> exp s) <|>
  -- ids and ops go next.
  (Wild <$> key "_" s) <|>
  ((\(s, i) -> Id s Ident Var i) <$> ident s) <|>
  ((\(s, i) -> Id s Ident Con i) <$> con s) <|>
  (constant EInt <$> int s) <|>
  (constant EFloat <$> double s)

-- Parse some stuff inside parens
expParens :: MP m => m (Span -> Exp)
expParens =
  ((\(_, o) s -> Id s Op Var o) <$> opr) <|>
  ((\(_, o) s -> Id s Op Con o) <$> conop) <|>
  do t <- tuple
     pure $ case t of
       (False, [e]) -> flip Paren e
       (_, es) -> flip Tuple es

app :: [Exp] -> Exp
app [e] = e
app (e:es) = App (span e `uSpan` span (last es)) e es
app [] = error ("app []")

ops :: Exp -> [(Exp, Exp)] -> Exp
ops e [] = e
ops e es = Ops e es

exp :: MP m => Spacing -> m Exp
exp s = label "exp" $ do
  a <- expArrow s
  (label ": ascription" (binSpan Asc (a <$ keyOp ":") (exp s)) <|>
   pure a)

expArrow :: MP m => Spacing -> m Exp
expArrow s = do
  a <- expOp s
  (label "t1 -> t2" (binSpan Arrow (a <$ keyOp "->") (expArrow s)) <|>
   pure a)

expOp :: MP m => Spacing -> m Exp
expOp s = do
  a <- expApp s
  (ops a <$> many (try ((,) <$> iop s <*> expApp s)))

iop :: MP m => Spacing -> m Exp
iop BT =
  ((\(s, o) -> Id s Op Var o) <$> opr) <|>
  ((\(s, o) -> Id s Op Con o) <$> conop)
iop _ =
  (uncurry OpExp <$> tok NL (between (bare NL (string "`")) (string "`") (exp BT))) <|> iop BT

expApp :: MP m => Spacing -> m Exp
expApp s = label "application or simple expr" $ do
  app <$> some (try $ expSimp s)

block :: MP m => Spacing -> m Defs
block s = label "{block}" (between (bare NL (string "{")) (bare s (string "}")) defs)

defs :: MP m => m Defs
defs = tok NL $ label "list of definitions" $
  (skipMany semi *> sepEndBy def (skipMany semi))

fixity :: MP m => ByteString -> FixDir -> m Def
fixity kw dir = label (UTF8.toString kw) $
  ((\(_, n) o -> Fix dir (fromInteger n) o) <$
   key kw NL <*> int NL <*> (opr <|> conop))

def :: MP m => m (Span, Def)
def = label "definition" $ tok NoNL (
  fixity "infixl" L <|>
  fixity "infixr" R <|>
  fixity "infix" None <|>
  ((exp NoNL >>= defExp) <* spaces NL)
  )

defExp :: MP m => Exp -> m Def
defExp e =
  (keyOp "=" *> defEq e) <|>
  label "bare exp" (pure (BindExp e))

defEq :: MP m => Exp -> m Def
defEq e =
  label "struct" (Struct e <$ key "struct" NL <*> block NoNL) <|>
  label "data" (Data e <$ key "data" NL <*> block NoNL) <|>
  label "binding" (Def e <$> exp NoNL)

toplevel :: MP m => m (SourcePos, Defs)
toplevel = (,) <$> getSourcePos <* optional anySpace <*> defs <* eof

partialFile :: [Char] -> IO (Exp, ByteString)
partialFile f = do
  c <- BS.readFile f
  case runParser' (optional anySpace *> defs) (initialState f c) of
    (st, Right ds) -> pure (unfixExp mempty $ Block ds, stateInput st)
    (_, Left err) -> fail $ errorBundlePretty err

file :: [Char] -> IO (SourcePos, Exp)
file f = do
  c <- BS.readFile f
  case runParser toplevel f c of
    Right (p, ds) -> pure (p, unfixExp mempty $ Block ds)
    Left err -> fail $ errorBundlePretty err

-- unfix functions resolve operator fixity.
type Fixities = Map ByteString (FixDir, Int)

-- Find fixities in given defs
getFix :: [(Span, Def)] -> Fixities
getFix ds = fromList [(op, (dir, prec)) | (_, Fix dir prec (_, op)) <- ds]

-- unfix starts at definitions level, since fixities are
-- found in defs.  We take in a set of already-known fixities.
unfix :: Fixities -> Defs -> Defs
unfix fs0 (s, ds) =
  let fsNew = getFix ds
      fs = fsNew <> fs0
  in  (s, fmap (unfixDef fs) <$> ds)

unfixDef :: Fixities -> Def -> Def
unfixDef fs (BindExp e) = BindExp $ unfixExp fs e
unfixDef fs (Def a b) = Def (unfixExp fs a) (unfixExp fs b)
unfixDef fs (Data a ds) = Data (unfixExp fs a) (unfix fs ds)
unfixDef fs (Struct a ds) = Data (unfixExp fs a) (unfix fs ds)
unfixDef _  f@(Fix _ _ _) = f -- Or strip?

unfixExp :: Fixities -> Exp -> Exp
unfixExp _ e@(Id _ _ _ _) = e
unfixExp fs (App s a b) = App s (unfixExp fs a) (unfixExp fs <$> b)
unfixExp fs (Fn s a b) = Fn s (unfixExp fs a) (unfixExp fs b)
unfixExp fs (Asc s a b) = Asc s (unfixExp fs a) (unfixExp fs b)
unfixExp fs (Arrow s a b) = Arrow s (unfixExp fs a) (unfixExp fs b)
unfixExp _ e@(Wild _) = e
unfixExp _ e@(Const _ _) = e
unfixExp fs (Case s e ds) = Case s (unfixExp fs e) (unfix fs ds)
unfixExp fs (If s b t e) =
  If s (unfixExp fs b) (unfixExp fs t) (unfixExp fs e)
unfixExp fs (IfMatch s p b t e) =
  IfMatch s (unfixExp fs p) (unfixExp fs b) (unfixExp fs t) (unfixExp fs e)
unfixExp fs (Dot s es) = Dot s $ fmap (unfixExp fs) es
unfixExp fs (Paren s e) = Paren s $ unfixExp fs e
unfixExp fs (Tuple s es) = Tuple s $ fmap (unfixExp fs) es
unfixExp fs (List s es) = List s $ fmap (unfixExp fs) es
unfixExp fs (Do s p e ds) =
  Do s (unfixExp fs p) (unfixExp fs e) (unfix fs ds)
unfixExp fs (Assign s a b) = Assign s (unfixExp fs a) (unfixExp fs b)
unfixExp fs (Block ds) = Block $ unfix fs ds
unfixExp fs (OpExp s e) = OpExp s $ unfixExp fs e
unfixExp fs (Ops e oes) = unfixOps fs e oes

opApp :: Exp -> Exp -> Exp -> Exp
opApp a op b = App (span a `uSpan` span b) op [a, b]

unfixOps :: Fixities -> Exp -> [(Exp, Exp)] -> Exp
unfixOps fs a [] = unfixExp fs a
unfixOps fs a [(op, b)] = unfixExp fs (opApp a op b)
unfixOps fs a oes = shunt [] a oes where
  -- left and right precedence for given op
  prec :: Exp -> (Int, Int)
  prec (Id _ Op _ o) = oPrec o
  prec (Paren _ e) = prec e
  prec _ = (maxBound, maxBound)

  oPrec :: ByteString -> (Int, Int)
  oPrec o =
    case lookup o fs of
      Nothing -> (maxBound, maxBound)
      Just (L, p) -> (p, p-1)
      Just (R, p) -> (p-1, p)
      Just (None, p) -> (p, p)
  -- Dijkstra's shunting yard algorithm:
  -- https://en.wikipedia.org/wiki/Shunting_yard_algorithm
  -- The incoming stuff is all of the form (op, exp)
  -- and thus the siding of ops is always one longer than the main line of exps.
  -- We can thus encode them together in a single stack with a special case for
  -- top of stack.
  shunt :: [(Exp, Int, Exp)] -> Exp -> [(Exp, Exp)] -> Exp
  shunt [] eTop [] = unfixExp fs eTop
  shunt ((e, _, op):s) eTop [] = shunt s (opApp e op eTop) []
  shunt [] eTop ((op, e) : os) =
    shunt [(eTop, snd (prec op), op)] e os
  shunt ((eS, pS, opS): s) eTop ((o, e):os)
    | pS < lp = shunt s (opApp eS opS eTop) ((o, e):os)
    | pS == lp = shunt s (Ops eS [(opS, eTop), (o, e)]) os
    | otherwise = shunt ((eTop, rp, o):(eS, pS, opS):s) e os
    where (lp, rp) = prec o
