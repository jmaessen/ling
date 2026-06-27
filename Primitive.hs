{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Primitive(env0) where
import AST(Arity, Constant(..), Var, showPp, showsPp)
import Value

import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
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

env0 :: Applicative m => Map Var (Val m)
env0 = foldl (\env p -> uncurry M.insert (mkPrim p) env) mempty [
  ("intAdd", 2, i2 (VConst . EInt) (+)),
  ("intSub", 2, i2 (VConst . EInt) (-)),
  ("intMul", 2, i2 (VConst . EInt) (*)),
  ("intDiv", 2, i2 (VConst . EInt) quot),
  ("intMod", 2, i2 (VConst . EInt) rem),
  ("intEq", 2, i2 vBool (==)),
  ("intNE", 2, i2 vBool (/=)),
  ("intLt", 2, i2 vBool (<)),
  ("intLE", 2, i2 vBool (<=)),
  ("intGt", 2, i2 vBool (>)),
  ("intGE", 2, i2 vBool (>=)),
  ("strAppend", 2, \case
      [VConst (EString a), VConst (EString b)] -> VConst (EString (a <> b))
      vs -> error ("strAppend "++showsPp vs)
  ),
  ("strAppendByte", 2, \case
      [VConst (EString a), VConst (EChar b)] -> VConst (EString (a <> b))),
  ("strLength", 1, \case [VConst (EString a)] ->
                           VConst (EInt (fromIntegral (BS.length a)))),
  ("intToStr", 1, \case
      [v] -> VConst $ EString $ fromString $ show $ valToInt v
      vs -> error ("intToStr "++showsPp vs)
  ),
  ("byteAt", 2, \case [VConst (EString a), VConst (EInt b)] ->
                        VConst (EInt (fromIntegral (a `BS.index` (fromIntegral b))))),
  ("strEq", 2, \case [VConst (EString a), VConst (EString b)] -> vBool (a == b)),
  ("substr", 3, \case [VConst (EString a), VConst (EInt start), VConst (EInt len)] ->
                        VConst (EString (BS.take (fromInteger len) $ BS.drop (fromInteger start) a))),
  ("strConcat", 1, strConcat),
  ("putStr", 1, \case
      [v] -> trace (toString (valToString v)) (VCon0 "()") -- total hack, but "safe"
      vs -> error ("putStr "++showsPp vs)
  )
  ]
