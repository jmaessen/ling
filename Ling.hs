module Ling where
import AST
import GHC.Stack(HasCallStack)
import Parse
import Semantics
import System.Environment(getArgs)

data What
  = Go
  | Pp
  | Show
  | FParen
  deriving (Show, Eq)

args :: [String] -> (What, [String])
args ("--go" : as) = (Go, as)
args ("--pp" : as) = (Pp, as)
args ("--show" : as) = (Show, as)
args ("--paren" : as) = (FParen, as)
args (a:as) = (a:) <$> args as
args [] = (Go, [])

main :: HasCallStack => IO ()
main = do
  as <- getArgs
  let (what, files) = args as
  (fs :: [Defs]) <- fmap (\(_, Block ds) -> ds) <$> mapM file files
  case what of
    Go -> mapM_ (print . pp . evalTop) $ fs
    Pp -> mapM_ (print . pp) $ fs
    Show -> mapM_ print $ fs
    FParen -> mapM_ (print . pp . fullParen) $ fs
