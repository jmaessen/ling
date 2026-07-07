{-# LANGUAGE LambdaCase, OverloadedStrings, ImpredicativeTypes #-}
module Primitive(env0) where
import AST(Exp(..), OpOrIdent(Ident), ConOrVar(Con),
           Arity, Constant(..), Var, showPp, showsPp, noSpan)
import Value

import Data.ByteString(ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.UTF8(fromString, toString)
import Data.Map as M hiding (foldl)
import Debug.Trace(trace)
import GHC.Stack(HasCallStack)

-- Definitions of primitives
type PrimOp m = [Val m] -> Val m
type Prim m = (PrimOp m, Exp)

mkPrim :: Applicative m =>
          (Var, Arity, Prim m) -> (Var, (Val m, Exp))
mkPrim (v, n, (f, ty)) =
  (v, (VDesc (Desc v n Fold (CloFun $ pure . f)), ty))

vBool :: Bool -> Val m
vBool True = VCon0 "True"
vBool False = VCon0 "False"

vInt :: Integer -> Val m
vInt = VConst . EInt

tInt :: Exp
tInt = Id noSpan Ident Con "Int"

tBool :: Exp
tBool = Id noSpan Ident Con "Bool"

tChar :: Exp
tChar = Id noSpan Ident Con "Char"

tString :: Exp
tString = Id noSpan Ident Con "String"

tf :: Exp -> Exp -> Exp
tf = Arrow noSpan

tf2 :: Exp -> Exp -> Exp -> Exp
tf2 a b c = tf a (tf b c)

i2 :: Exp -> (a -> Val m) -> (Integer -> Integer -> a) -> Prim m
i2 retTy v op = (f, ty) where
  f [VConst (EInt a), VConst (EInt b)] = v (a `op` b)
  f vs = error ("Bad args "++showsPp vs)
  ty = tf2 tInt tInt retTy

valToList :: HasCallStack => Val m -> [Val m]
valToList v =
  case toListVal v of
    Just vs -> vs
    _ -> error ("valToList: not a list "++showPp v)

valToString :: HasCallStack => Val m -> ByteString
valToString (VConst (EString s)) = s
valToString v = error ("valToString: not a string "++showPp v)

valToInt :: HasCallStack => Val m -> Integer
valToInt (VConst (EInt i)) = i
valToInt v = error ("valToInt: not an int "++showPp v)

strAppend :: PrimOp m
strAppend [VConst (EString a), VConst (EString b)] = VConst (EString (a <> b))
strAppend v = error ("strAppend: Non-string arg "++showPp v)

strAppendByte :: PrimOp m
strAppendByte [VConst (EString a), VConst (EChar b)] = VConst (EString (a <> b))
strAppendByte v = error ("strAppendByte: Bad arg "++showPp v)

strLength :: PrimOp m
strLength [VConst (EString a)] = vInt (fromIntegral (BS.length a))
strLength v = error ("strLength: not string "++showPp v)

intToStr :: PrimOp m
intToStr [v] = VConst $ EString $ fromString $ show $ valToInt v
intToStr vs  = error ("intToStr "++showPp vs)

byteAt :: PrimOp m
byteAt [VConst (EString a), VConst (EInt b)] =
  vInt (fromIntegral (a `BS.index` (fromIntegral b)))
byteAt vs = error ("byteAt: bad arg "++showPp vs)

strEq :: PrimOp m
strEq [VConst (EString a), VConst (EString b)] = vBool (a == b)
strEq vs = error ("strEq: non-string "++showPp vs)

substr :: PrimOp m
substr [VConst (EString a), VConst (EInt start), VConst (EInt len)] =
  VConst (EString (BS.take (fromInteger len) $ BS.drop (fromInteger start) a))
substr vs = error ("substr: bad arg "++showPp vs)

strConcat :: PrimOp m
strConcat [v] = VConst (EString (mconcat (valToString <$> valToList v)))
strConcat vs  = error ("strConcat: wrong number of args "++showPp vs)

pputStr :: PrimOp m
pputStr [v] = trace (toString (valToString v)) (VCon0 "()") -- total hack, but "safe"
pputStr vs  = error ("putStr "++showsPp vs)

env0 :: Applicative m => Map Var (Val m, Exp)
env0 = foldl (\env p -> uncurry M.insert (mkPrim p) env) mempty [
  ("intAdd", 2, i2 tInt vInt (+)),
  ("intSub", 2, i2 tInt vInt (-)),
  ("intMul", 2, i2 tInt vInt (*)),
  ("intDiv", 2, i2 tInt vInt quot),
  ("intMod", 2, i2 tInt vInt rem),
  ("intEq", 2, i2 tBool vBool (==)),
  ("intNE", 2, i2 tBool vBool (/=)),
  ("intLt", 2, i2 tBool vBool (<)),
  ("intLE", 2, i2 tBool vBool (<=)),
  ("intGt", 2, i2 tBool vBool (>)),
  ("intGE", 2, i2 tBool vBool (>=)),
  ("strAppend", 2, (strAppend, tf2 tString tString tString)),
  ("strAppendByte", 2, (strAppendByte, tf2 tString tChar tString)),
  ("strLength", 1, (strLength, tf tString tInt)),
  ("intToStr", 1, (intToStr, tf tInt tString)),
  ("byteAt", 2, (byteAt, tf2 tString tInt tInt)),
  ("strEq", 2, (strEq, tf2 tString tString tBool)),
  ("substr", 3, (substr, tf tString (tf2 tInt tInt tString))),
  ("strConcat", 1, (strConcat, tf (List noSpan [tString]) tString)),
  ("putStr", 1, (pputStr, tf tString (Tuple noSpan [])))
  ]
