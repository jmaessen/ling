module Ling where
import AST
import Desugar
import GHC.Stack(HasCallStack)
import Parse
import Semantics
import System.Environment(getArgs)

data What
  = Go
  | Pp
  | Show
  | FParen
  | Desugar
  deriving (Show, Eq)

args :: [String] -> (What, [String])
args ("--go" : as) = (Go, as)
args ("--pp" : as) = (Pp, as)
args ("--show" : as) = (Show, as)
args ("--paren" : as) = (FParen, as)
args ("--desugar" : as) = (Desugar, as)
args (a:as) = (a:) <$> args as
args [] = (Go, [])

main :: HasCallStack => IO ()
main = do
  as <- getArgs
  let (what, files) = args as
  (fs :: [(SpanPos, Defs)]) <- mapM file files
  case what of
    Go -> mapM_ (print . pp . evalTop . validate) $ fs
    Pp -> mapM_ (print . pp . snd) $ fs
    Show -> mapM_ (mapM_ print . snd . snd) $ fs
    FParen -> mapM_ (print . pp . fullParen . snd) $ fs
    Desugar -> mapM_ (print .  pp . fullParen . snd . desugar . validate) $ fs
