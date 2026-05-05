{-# LANGUAGE ApplicativeDo, OverloadedStrings #-}
module Parse(toplevel, def, defs, block, exp) where
import AST
import Control.Monad
import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char
import Data.Functor
import Data.Maybe
import Text.Megaparsec as P
import Text.Megaparsec.Byte
import Text.Megaparsec.Byte.Lexer as L
import Prelude hiding (exp, span)

type MP e m = MonadParsec e ByteString m

data Spacing = NoNL | NL deriving (Eq, Ord, Show)

utf8satisfy :: MP e m => (Char -> Bool) -> m ByteString
utf8satisfy p = do
  bs <- getInput
  case UTF8.decode bs of
    Just (c, n) | p c -> BS.take n bs <$ takeP Nothing n
    _ -> empty

utf8span1 :: MP e m => (Char -> Bool) -> m ByteString
utf8span1 p = do
  bs <- getInput
  case UTF8.span p bs of
    (rs, _)
      | BS.null rs -> empty
      | otherwise -> rs <$ takeP Nothing (BS.length rs)

charLiteral :: MP e m => m ByteString
charLiteral = do
  bs <- getInput
  let seg = UTF8.toString (BS.take 16 bs) :: String
  case readLitChar seg of
    [(_, r)] -> do
      let l = UTF8.take (length r - length seg) bs
      l <$ takeP Nothing (BS.length l)
    _ -> empty

utf8span :: MP e m => (Char -> Bool) -> m ByteString
utf8span p = do
  bs <- getInput
  case UTF8.span p bs of
    (rs, _) -> rs <$ takeP Nothing (BS.length rs)

sp1 :: MP e m => m ()
sp1 = () <$ utf8span1 isSpace

isHSpace :: Char -> Bool
isHSpace c = isSpace c && c /= '\n' && c /= '\r'

hsp1 :: MP e m => m ()
hsp1 = () <$ utf8span1 isHSpace

lineSpace :: MP e m => m ()
lineSpace = L.space hsp1 empty (skipBlockCommentNested "/*" "*/")

anySpace :: MP e m => m ()
anySpace = L.space sp1 (skipLineComment "//") (skipBlockCommentNested "/*" "*/")

newlineSpace :: MP e m => m ()
newlineSpace = skipLineComment "//" <|> (() <$ eol)

spaces :: MP e m => Spacing -> m ()
spaces NoNL = lineSpace
spaces NL = anySpace

tok :: MP e m => Spacing -> m a -> m (Span, a)
tok s p = do
  start <- getOffset
  r <- p
  end <- getOffset
  spaces s
  pure ((start, end), r)

bare :: MP e m => Spacing -> m a -> m a
bare s p = p <* optional (spaces s)

newlineOrSemi :: MP e m => m ()
newlineOrSemi =
  ((() <$ string ";" <* notFollowedBy (utf8satisfy isOpChar)) <|> newlineSpace)
  <* spaces NL

isIdCont :: Char -> Bool
isIdCont c = isAlphaNum c || c == '\'' || c == '_'

isIdStart :: Char -> Bool
isIdStart c = isIdCont c && not (isUpper c)

ident :: MP e m => Spacing -> m Id
ident s = tok s $ label "id" $ do
  front <- utf8satisfy isIdStart
  rest <- utf8span isIdCont
  pure (front <> rest)

con :: MP e m => Spacing -> m Con
con s = tok s $ label "con" $ do
  front <- takeWhileP Nothing (\c -> c == fromIntegral (fromEnum '\'') || c == fromIntegral (fromEnum '_'))
  cap <- utf8satisfy isUpper
  rest <- utf8span isIdCont
  pure (front <> cap <> rest)

key :: MP e m => ByteString -> Spacing -> m Span
key kw s = fmap fst $ tok s $ label (UTF8.toString kw) $
  (string kw *> notFollowedBy (utf8satisfy isIdCont))

isOpChar :: Char -> Bool
isOpChar c = (isSymbol c || isPunctuation c) && (c `notElem` ("\",()[]{}`" :: String))

isOpStart :: Char -> Bool
isOpStart c = isOpChar c && c /= ':' && c /= '_' && c /= ';'

op :: MP e m => Spacing -> m Op
op s = tok s $ label "op" $ do
  front <- utf8satisfy isOpStart
  rest <- utf8span isOpChar
  let r = front <> rest
  guard (r /= "=" && r /= "->")
  pure r

conop :: MP e m => Spacing -> m ConOp
conop s = tok s $ label ":conop" $ do
  front <- string ":"
  rest <- utf8span isOpChar
  guard (rest /= "=")
  pure (front <> rest)

keyOp :: MP e m => ByteString -> m Span
keyOp kw = fmap fst $ tok NL $ label (UTF8.toString kw) $
  (string kw *> notFollowedBy (utf8satisfy isOpChar))

parens :: MP e m => Spacing -> m t -> m (Span, t)
parens s p = tok s (between (bare NL (string "(")) (string ")") p)

tuple :: MP e m => m (Bool, [Exp])
tuple = (fmap . (:) <$> exp NL <*> tupleC) <|> pure (False, [])

-- tuple prefixed by a comma
tupleC :: MP e m => m (Bool, [Exp])
tupleC = (comma *> ((True,) . snd <$> tuple)) <|> pure (False, [])


comma :: MP e m => m ()
comma = () <$ bare NL (string ",")

-- sign must be tightly spaced, this is how we avoid some ambiguity with operators.
sign :: Num n => MP e m => m (n -> n)
sign = (negate <$ string "-") <|> (id <$ string "+") <|> pure id

int :: MP e m => Spacing -> m (Span, Integer)
int s = tok s $ label "<integer>" $
  (sign <*> ((string "0" *> (octal <|> (string' "x" *> hexadecimal) <|> (string' "b" *> binary))) <|> decimal))

double :: MP e m => Spacing -> m (Span, Double)
double s = tok s $ label "<double>" (sign <*> float)

binSpan :: (MP e m, IsAST a, IsAST b) => (Span -> a -> b -> c) -> m a -> m b -> m c
binSpan f pa pb = (\a b -> f (span a `uSpan` span b) a b) <$> pa <*> pb

expSimp :: MP e m => Spacing -> m Exp
expSimp s =
  -- delimited things first
  ((\(sp, f) -> f sp) <$> parens s expParens) <|>
  label "[list]" (uncurry List <$> tok s (between (bare NL (string "[")) (string "]") (snd <$> tuple))) <|>
  (Block <$> block s) <|>
  label "\"string\"" (uncurry EString <$>
                      tok s (between (string "\"") (string "\"") (BS.concat <$> many charLiteral))) <|>
  label "'char'" (uncurry EChar <$> tok s (between (string "'") (string "'") charLiteral)) <|>
  -- Keyword expressions must come before ids and ops.
  label "fn" ((\f a b -> Fn (f `uSpan` span b) a b) <$> key "fn" NL <*> exp NL <* keyOp "=" <*> exp s) <|>
  -- ids and ops go next.
  (Wild <$> key "_" s) <|>
  (Id <$> ident s) <|>
  (Con <$> con s) <|>
  (uncurry EInt <$> int s) <|>
  (uncurry EFloat <$> double s)

-- Parse some stuff inside parens
expParens :: MP e m => m (Span -> Exp)
expParens =
  ((\(_, o) s -> Op (s,o)) <$> op NL) <|>
  ((\(_, o) s -> ConOp (s,o)) <$> conop NL) <|>
  do t <- tuple
     pure $ case t of
       (False, [e]) -> flip Paren e
       (_, es) -> flip Tuple es

exp :: MP e m => Spacing -> m Exp
exp s = label "exp" $ do
  l <- expSimp s
  expR s l

expR :: MP e m => Spacing -> Exp -> m Exp
expR s e =
  -- Next should be operator parsing.
  label ": ascription" (binSpan Asc (e <$ keyOp ":") (exp s)) <|>
  label "t1 -> t2" (binSpan Arrow (e <$ keyOp "->") (exp s)) <|>
  (expR s =<< label "app" (binSpan App (pure e) (expSimp s))) <|>
  pure e

block :: MP e m => Spacing -> m Defs
block s = tok s $ label "{block}" (between (bare NL (string "{")) (string "}") defs)

defs :: MP e m => m [(Span, Def)]
defs = label "list of definitions" $
  (skipMany newlineOrSemi *> sepEndBy def (some newlineOrSemi))

fixity :: MP e m => ByteString -> FixDir -> m Def
fixity kw dir = label (UTF8.toString kw) $
  ((\(_, n) o -> Fix dir (fromInteger n) o) <$
   key kw NL <*> int NL <*> (op NoNL <|> conop NoNL))

def :: MP e m => m (Span, Def)
def = label "definition" $ tok NoNL (
  fixity "infixl" L <|>
  fixity "infixr" R <|>
  fixity "infix" None <|>
  (exp NoNL >>= defExp)
  )

defExp :: MP e m => Exp -> m Def
defExp e =
  (keyOp "=" *> defEq e) <|>
  label "bare exp" (pure (BindExp e))

defEq :: MP e m => Exp -> m Def
defEq e =
  label "struct" (Struct e <$ key "struct" NL <*> block NoNL) <|>
  label "data" (Data e <$ key "data" NL <*> block NoNL) <|>
  label "binding" (Def e <$> exp NoNL)

toplevel :: MP e m => m (SourcePos, [(Span, Def)])
toplevel = (,) <$> getSourcePos <* optional anySpace <*> many def <* eof
