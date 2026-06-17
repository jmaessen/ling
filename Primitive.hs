{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Primitive(env0) where
import AST(Arity, Constant(..), Var, showPp, showsPp)
import Value

import Data.ByteString(ByteString)
import Data.ByteString.UTF8(fromString, toString)
import Data.Map as M hiding (foldl)
import Debug.Trace(trace)
import GHC.Stack(HasCallStack)

-- Definitions of primitives
mkPrim :: Applicative m => (Var, Arity, [Val m] -> Val m) -> (Var, Val m)
mkPrim (v, n, f) = (v, VDesc (Desc v n Fold (CloFun $ pure . f)))

vBool :: Bool -> Val m
vBool True = VCon0 "True"
vBool False = VCon0 "False"

i2 :: HasCallStack => (a -> Val m) -> (Integer -> Integer -> a) -> [Val m] -> Val m
i2 v op [VConst (EInt a), VConst (EInt b)] = v (a `op` b)
i2 _ _ vs = error ("Bad args "++showsPp vs)

valToList :: HasCallStack => Val m -> [Val m]
valToList v =
  case toListVal v of
    Just vs -> vs
    _ -> error ("valToList: not a list "++showPp v)

valToString :: HasCallStack => Val m -> ByteString
valToString (VConst (EString s)) = s
valToString v = error ("valToString: not a string "++showPp v)

strConcat :: HasCallStack => [Val m] -> Val m
strConcat [v] = VConst (EString (mconcat (valToString <$> valToList v)))
strConcat vs = error ("strConcat: wrong number of args "++showPp vs)

valToInt :: HasCallStack => Val m -> Integer
valToInt (VConst (EInt i)) = i
valToInt v = error ("valToInt: not an int "++showPp v)

getPrim :: (HasCallStack, Applicative m) => [Val m] -> Val m
getPrim [n, v] =
  case M.lookup (valToString v) env0 of
    Just r@(VDesc (Desc _ n' _ _))
      | fromInteger (valToInt n) == n' -> r
      | otherwise ->
        error ("Arity mismatch on prim "++showPp v++" registered as "++show n'++" asked for "++showPp n)
    _ -> error ("Bad prim "++showPp v)
getPrim as = error ("Bad args to prim "++showPp as)

env0 :: Applicative m => Map Var (Val m)
env0 = foldl (\env p -> uncurry M.insert (mkPrim p) env) mempty [
  ("prim", 2, getPrim),
  ("intAdd", 2, i2 (VConst . EInt) (+)),
  ("intSub", 2, i2 (VConst . EInt) (-)),
  ("intEq", 2, i2 vBool (==)),
  ("intLE", 2, i2 vBool (<=)),
  ("strAppend", 2, \case
      [VConst (EString a), VConst (EString b)] -> VConst (EString (a <> b))
      vs -> error ("strAppend "++showsPp vs)
  ),
  ("putStr", 1, \case
      [v] -> trace (toString (valToString v)) (VCon0 "()") -- total hack, but "safe"
      vs -> error ("putStr "++showsPp vs)
  ),
  ("strConcat", 1, strConcat),
  ("intToStr", 1, \case
      [v] -> VConst $ EString $ fromString $ show $ valToInt v
      vs -> error ("intToStr "++showsPp vs)
  )
  ]
