{-# LANGUAGE PatternSynonyms, OverloadedStrings, TypeFamilies #-}
module Value(
  Val(..), pattern VCon0, pattern VCon,
  Desc(..), CloFun(..), Foldability(..),
  FieldName, ConName,
  MonadEval(..),
  toListVal,
  SimEnv(..), Knw(..), sameEnv,
  Mode(..), meet) where
import AST

import Data.ByteString
import Data.ByteString.UTF8(toString)
import Data.Map
import Text.PrettyPrint as PP hiding ((<>), Mode)

-- Simple type aliases
type FieldName = ByteString
type ConName = ByteString

class (Monad m, Eq (ClosureState m), Show (ClosureState m)) => MonadEval m where
  type ClosureState m
  withClo :: ClosureState m -> m a -> m a

-- Closures, Descriptors, and Values
newtype CloFun m = CloFun ([Val m] -> m (Val m))

instance Eq (CloFun m) where
  _ == _ = True -- Rely on parent to disambiguate.

instance Show (CloFun m) where
  show _ = "<clofun>"

data Foldability = Fold | NoFold deriving (Eq, Show)

data Desc m = Desc !Var !Arity !Foldability (CloFun m)
  deriving (Eq, Show)

data Val m
  = VConst !Constant
  | VDesc !(Desc m)
  | VPAp !(Desc m) !(ClosureState m) ![Val m] -- Also closures
  | VObj !(Desc m) ![Val m]
  | VStruct !(Map FieldName (Val m))

deriving instance MonadEval m => Eq (Val m)
deriving instance MonadEval m => Show (Val m)

pattern VCon0 :: ConName -> Val m
pattern VCon0 c <- VDesc (Desc c 0 Fold _) where
  VCon0 c =
    VDesc (Desc c 0 Fold (CloFun (\_ -> error ("Applying nullary "++ toString c))))

pattern VCon :: ConName -> Arity -> [Val m] -> Val m
pattern VCon c n vs <- VObj (Desc c n Fold _) vs where
  VCon c n vs =
    VObj (Desc c n Fold (CloFun (\_ -> error ("Applying already-built "++toString c)))) vs

{-# COMPLETE VConst, VDesc, VPAp, VCon, VStruct #-}

toListVal :: Val m -> Maybe [Val m]
toListVal (VCon0 "[]") = Just []
toListVal (VCon "::" 2 [a,as]) = (a:) <$> toListVal as
toListVal _ = Nothing

instance PP (Val m) where
  pp (VConst c) = pp (Const noSpan c)
  pp (VCon0 c) = PP.text (toString c)
  pp (VDesc (Desc v n Fold _)) =
    "<p" <+> PP.text (toString v) <+> (PP.int n <> ">")
  pp (VDesc (Desc v n _ _)) =
    "<d" <+> PP.text (toString v) <+> (PP.int n <> ">")
  pp (VPAp (Desc v n _ _) _ []) =
    "<c" <+> PP.text (toString v) <+> (PP.int n <> ">")
  pp (VPAp (Desc v _ _ _) _ vs) = PP.parens (PP.text (toString v) <+> PP.sep (pp <$> vs))
  pp c@(VCon "::" 2 [_,_])
    | Just cs <- toListVal c =
      PP.brackets (PP.fsep $ PP.punctuate "," (pp <$> cs))
  pp (VCon "()" _ vs) =
    PP.parens (PP.hsep $ PP.punctuate "," (pp <$> vs))
  pp (VCon c _ vs) = PP.parens (PP.text (toString c) <+> PP.sep (pp <$> vs))
  pp (VStruct vs) =
    PP.vcat [PP.lbrace, "", PP.nest 2 (PP.vcat $ fmap ppField (toList vs)), PP.rbrace]
    where ppField (f, v) = PP.text (toString f) <+> "=" <+> pp v

-- Known-ness (abstract domain of value information)
data SimEnv = SameEnv | DiffEnv deriving (Eq, Show)

data Knw m
  = Unknown
  | KnownValue (Val m)
  | KnownDesc SimEnv (Desc m)
  | Bottom
  deriving (Eq, Show)

sameEnv :: Knw m -> Knw m
sameEnv (KnownDesc _ d) = KnownDesc SameEnv d
sameEnv kn = kn

-- The information-theoretic join on Knw m
instance MonadEval m => Semigroup (Knw m) where
  Bottom <> b = b
  a <> Bottom = a
  a <> b
    | a == b = a
  KnownValue (VObj a _) <> KnownValue (VObj b _)
    | a == b = KnownDesc DiffEnv a
  KnownValue (VPAp a _ _) <> KnownValue (VPAp b _ _)
    | a == b = KnownDesc DiffEnv a
  _ <> _ = Unknown

instance MonadEval m => Monoid (Knw m) where
  mempty = Bottom

instance PP (Knw m) where
  pp Unknown = "Unknown"
  pp (KnownValue v) = pp v
  pp (KnownDesc SameEnv (Desc v n _ _)) =
    "<k same env " <+> PP.text (toString v) <+> (PP.int n <> ">")
  pp (KnownDesc _ (Desc v n _ _)) =
    "<k" <+> PP.text (toString v) <+> (PP.int n <> ">")
  pp Bottom = "Bottom (Unreachable)"

-- Match Mode (static information about a match).
data Mode = AlwaysSucceeds | MayFail | AlwaysFails deriving (Eq, Show)

-- The join semigroup (disjoint conditions)
instance Semigroup Mode where
  AlwaysSucceeds <> _ = AlwaysSucceeds
  AlwaysFails <> o = o
  MayFail <> AlwaysSucceeds = AlwaysSucceeds
  MayFail <> _ = MayFail

instance Monoid Mode where
  mempty = AlwaysFails

-- The meet semigroup (same condition)
meet :: Mode -> Mode -> Mode
meet AlwaysFails _ = AlwaysFails
meet AlwaysSucceeds o = o
meet MayFail AlwaysFails = AlwaysFails
meet MayFail _ = MayFail
