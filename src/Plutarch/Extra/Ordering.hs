{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutarch.Extra.Ordering (
    POrdering (..),
    PCompareable (..),
) where

import Plutarch.Extra.IsData (
    DerivePConstantViaEnum (..),
    PlutusTypeEnumData,
 )
import Plutarch.Lift (
    PConstantDecl,
    PUnsafeLiftDecl (PLifted),
 )

data POrdering (s :: S)
    = PLT
    | PEQ
    | PGT
    deriving stock
        ( Generic
        , Enum
        , Bounded
        )
    deriving anyclass
        ( PlutusType
        , PEq
        )

instance DerivePlutusType POrdering where
    type DPTStrat _ = PlutusTypeEnumData

instance PUnsafeLiftDecl POrdering where
    type PLifted _ = Ordering

deriving via
    (DerivePConstantViaEnum Ordering POrdering)
    instance
        (PConstantDecl Ordering)

class (POrd a) => PCompareable a where
    pcompare :: forall s. Term s (a :--> a :--> POrdering)
    pcompare = phoistAcyclic $
        plam $ \l r ->
            pif (l #== r) (pcon PEQ) $
                pif (l #< r) (pcon PLT) $
                    pcon PGT

instance (POrd a) => PCompareable a
