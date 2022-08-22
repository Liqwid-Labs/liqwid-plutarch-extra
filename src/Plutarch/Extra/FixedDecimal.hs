{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{- |
 Module: Plutarch.Extra.FixedDecimal
 Copyright: (C) Liqwid Labs 2022
 License: Apache 2.0
 Maintainer: Koz Ross <koz@mlabs.city>
 Portability: GHC only
 Stability: Experimental
-}
module Plutarch.Extra.FixedDecimal (
    -- * Type
    PFixedDecimal (..),

    -- * Type classes
    DivideSemigroup (..),
    DivideMonoid (..),

    -- * Functions

    -- ** Conversion
    decimalToAdaValue,
    fromPInteger,
    toPInteger,
) where

import Control.Composition (on, (.*))
import Data.Bifunctor (first)
import Data.Proxy (Proxy (Proxy))
import GHC.TypeLits (KnownNat, Nat, natVal)
import Plutarch.Api.V1 (PValue)
import Plutarch.Api.V2 (AmountGuarantees, KeyGuarantees)
import Plutarch.Extra.Function (pflip)
import Plutarch.Extra.Value (psingletonValue)
import Plutarch.Num (PNum (pfromInteger, (#*)))
import qualified Plutarch.Numeric.Additive as A (
    AdditiveMonoid (zero),
    AdditiveSemigroup ((+)),
 )
import Plutarch.TryFrom (PTryFrom (PTryFromExcess, ptryFrom'))
import Plutarch.Unsafe (punsafeCoerce)

{- | Fixed-width decimal, with the decimal point indicated in its type. One
 possible use is currency at a fixed precision: for example, an Ada value
 stored as Lovelace.

 @since 1.0.0
-}
newtype PFixedDecimal (unit :: Nat) (s :: S)
    = PFixedDecimal (Term s PInteger)
    deriving stock
        ( -- | @since 1.0.0
          Generic
        )
    deriving anyclass
        ( -- | @since 1.0.0
          PlutusType
        , -- | @since 1.0.0
          PIsData
        , -- | @since 1.4.0
          PEq
        , -- | @since 1.4.0
          PPartialOrd
        , -- | @since 1.0.0
          POrd
        , -- | @since 1.0.0
          PShow
        )

-- | @since 1.4.0
instance DerivePlutusType (PFixedDecimal a) where
    type DPTStrat _ = PlutusTypeNewtype

-- | @since 1.4.0
instance KnownNat u => PNum (PFixedDecimal u) where
    (#*) =
        (pcon . PFixedDecimal)
            .* (pflip # pdiv # pconstant (natVal (Proxy @u)) #)
            .* (#*) `on` punsafeCoerce
    pfromInteger = pcon . PFixedDecimal . (* pconstant (natVal (Proxy @u))) . pconstant

-- | @since 1.0.0
instance PTryFrom PData (PAsData (PFixedDecimal unit)) where
    type PTryFromExcess PData (PAsData (PFixedDecimal unit)) = PTryFromExcess PData (PAsData PInteger)
    ptryFrom' d k = ptryFrom' @_ @(PAsData PInteger) d $ k . first punsafeCoerce

-- | @since 1.4.0
class DivideSemigroup a where
    divide :: a -> a -> a

-- | @since 1.4.0
class DivideSemigroup a => DivideMonoid a where
    one :: a

-- | @since 1.0.0
instance (KnownNat u) => DivideSemigroup (Term s (PFixedDecimal u)) where
    divide (pto -> x) (pto -> y) =
        pcon . PFixedDecimal $ pdiv # (x * pconstant (natVal (Proxy @u))) # y

-- | @since 1.0.0
instance (KnownNat u) => DivideMonoid (Term s (PFixedDecimal u)) where
    one = 1

-- | @since 1.0.0
instance (KnownNat u) => A.AdditiveSemigroup (Term s (PFixedDecimal u)) where
    (+) = (+)

-- | @since 1.0.0
instance (KnownNat u) => A.AdditiveMonoid (Term s (PFixedDecimal u)) where
    zero = pcon . PFixedDecimal $ pconstant 0

{- | Convert a decimal into an Ada value. This will construct the value as an
 integral amount of Lovelace.

 @since 1.0.0
-}
decimalToAdaValue ::
    forall (s :: S) (keys :: KeyGuarantees) (amounts :: AmountGuarantees) (unit :: Nat).
    KnownNat unit =>
    Term s (PFixedDecimal unit :--> PValue keys amounts)
decimalToAdaValue =
    phoistAcyclic $
        plam $ \(pto -> dec) ->
            let adaValue = (pdiv # dec # pconstant (natVal (Proxy @unit))) * pconstant 1000000
             in psingletonValue # pconstant "" # pconstant "" #$ adaValue

{- | Convert a 'PInteger' to a 'PFixedDecimal'.

 @since 1.0.0
-}
fromPInteger ::
    forall (unit :: Nat) (s :: S).
    KnownNat unit =>
    Term s (PInteger :--> PFixedDecimal unit)
fromPInteger =
    phoistAcyclic $ plam $ \z -> pcon . PFixedDecimal $ pconstant (natVal (Proxy @unit)) * z

{- | Convert a 'PFixedDecimal' to a 'PInteger' by truncation; any fractional
 amounts will be dropped.

 @since 1.0.0
-}
toPInteger ::
    forall (unit :: Nat) (s :: S).
    KnownNat unit =>
    Term s (PFixedDecimal unit :--> PInteger)
toPInteger =
    phoistAcyclic $ plam $ \d -> pdiv # pto d # pconstant (natVal (Proxy @unit))
