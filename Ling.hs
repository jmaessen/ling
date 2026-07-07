module Ling where
import AST
import Compile
import Desugar
import qualified GenTuple
import Parse
import Semantics
import TypeCheck
import qualified SimpleSemantics as Simple

import GHC.Stack(HasCallStack)
import System.Environment(getArgs)

data What
  = Go
  | Compile
  | Simple
  | Pp
  | Show
  | FParen
  | Desugar
  | TypeCheck
  | All
  | GenTuple
  deriving (Show, Eq)

args :: [String] -> (What, [String])
args ("--go" : as) = (Go, as)
args ("--pp" : as) = (Pp, as)
args ("--show" : as) = (Show, as)
args ("--simple" : as) = (Simple, as)
args ("--paren" : as) = (FParen, as)
args ("--desugar" : as) = (Desugar, as)
args ("-C" : as) = (Compile, as)
args ("--tc" : as) = (TypeCheck, as)
args ("--all" : as) = (All, as)
args ("--gen-tuple" : as) = (GenTuple, as)
args (a:as) = (a:) <$> args as
args [] = (Go, [])

doit :: What -> [(SpanPos, Defs)] -> IO ()
doit what fs =
  case what of
    Go -> mapM_ (print . pp . evalTop . desugar . validate) $ fs
    Simple -> mapM_ (print . pp . Simple.evalTop . desugar . validate) $ fs
    Compile -> mapM_ (print . Compile.compileTop . desugar . validate) $ fs
    Pp -> mapM_ (print . pp . snd) $ fs
    Show -> mapM_ (mapM_ print . snd . snd) $ fs
    FParen -> mapM_ (print . pp . fullParen . snd) $ fs
    Desugar -> mapM_ (print . pp . fullParen . snd . desugar . validate) $ fs
    TypeCheck -> mapM_ (print . pp . snd . typecheckTop . validate) $ fs
    All -> do
      doit Pp fs
      let vs = validate <$> fs
          ds = desugar <$> vs
      mapM_ (print . pp . fullParen . snd) ds
      mapM_ (print . pp . Simple.evalTop) ds
      mapM_ (print . pp . evalTop) ds
      mapM_ (print . Compile.compileTop) ds
      mapM_ (print . pp . snd . typecheckTop) vs
    GenTuple -> GenTuple.gen

main :: HasCallStack => IO ()
main = do
  as <- getArgs
  let (what, files) = args as
  (fs :: [(SpanPos, Defs)]) <- mapM file files
  doit what fs
