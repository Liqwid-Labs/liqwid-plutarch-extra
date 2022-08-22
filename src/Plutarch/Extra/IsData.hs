{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- |
 Module: Plutarch.Extra.IsData
 Copyright: (C) Liqwid Labs 2022
 License: Apache 2.0
 Maintainer: Koz Ross <koz@mlabs.city>
 Portability: GHC only
 Stability: Experimental
-}
module Plutarch.Extra.IsData (
    -- * PlutusTx ToData/FromData derive-wrappers
    ProductIsData (..),
    EnumIsData (..),

    -- * Plutarch PIsData/PlutusType derive-wrappers
    DerivePConstantViaDataList (..),
    DerivePConstantViaEnum (..),

    -- * Plutarch deriving strategy
    PlutusTypeEnumData,

    -- * Functions for PEnumData types
    pmatchEnum,
    pmatchEnumFromData,
) where

--------------------------------------------------------------------------------

import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (Proxy))
import Generics.SOP (
    All,
    IsProductType,
    hcmap,
    hcollapse,
    hctraverse,
    mapIK,
    mapKI,
    productTypeFrom,
    productTypeTo,
    unI,
 )
import qualified Generics.SOP as SOP
import Plutarch.Builtin (pasInt)
import Plutarch.Extra.TermCont (pletC)
import Plutarch.Internal.Generic (PGeneric)
import Plutarch.Internal.PlutusType (
    DerivePlutusType (DPTStrat),
    PlutusTypeStrat (DerivedPInner, PlutusTypeStratConstraint, derivedPCon, derivedPMatch),
 )
import Plutarch.Lift (PConstantDecl (PConstantRepr, PConstanted, pconstantFromRepr, pconstantToRepr))
import Plutarch.Prelude (
    PData,
    PEq ((#==)),
    PInteger,
    PLift,
    S,
    Term,
    Type,
    pif,
    unTermCont,
    (#),
 )
import PlutusLedgerApi.V1 (
    BuiltinData (BuiltinData),
    UnsafeFromData (unsafeFromBuiltinData),
 )
import PlutusTx (
    Data (List),
    FromData (fromBuiltinData),
    ToData (toBuiltinData),
    fromData,
    toData,
 )
import Prelude (
    Bounded,
    Enum,
    Integer,
    Maybe (Just, Nothing),
    enumFrom,
    error,
    fmap,
    foldr,
    fromEnum,
    fromInteger,
    maxBound,
    minBound,
    pure,
    toEnum,
    toInteger,
    ($),
    (.),
    (<$>),
 )

--------------------------------------------------------------------------------
-- ProductIsData

{- |
  Wrapper for deriving 'ToData', 'FromData' using the 'List' constructor of
  'Data' to represent a product type.

  Uses 'gProductToBuiltinData', 'gproductFromBuiltinData'.

  @since 1.1.0
-}
newtype ProductIsData (a :: Type) = ProductIsData {unProductIsData :: a}

{- | Variant of 'PConstantViaData' using the 'List' representation from
 'ProductIsData'.

 @since 1.1.0
-}
newtype DerivePConstantViaDataList (h :: Type) (p :: S -> Type) = DerivePConstantViaDataList h

{- |
  Generically convert a product-Type to 'BuiltinData' with the 'List' representation.

  @since 1.1.0
-}
gProductToBuiltinData ::
    forall (a :: Type) (repr :: [Type]).
    (IsProductType a repr, All ToData repr) =>
    a ->
    BuiltinData
gProductToBuiltinData x =
    BuiltinData $ List $ hcollapse $ hcmap (Proxy @ToData) (mapIK toData) $ productTypeFrom x

{- |
  Generically convert a product type from a 'BuiltinData' 'List' representation.

  @since 1.1.0
-}
gProductFromBuiltinData ::
    forall (a :: Type) (repr :: [Type]).
    (IsProductType a repr, All FromData repr) =>
    BuiltinData ->
    Maybe a
gProductFromBuiltinData (BuiltinData (List xs)) = do
    prod <- SOP.fromList @repr xs
    productTypeTo <$> hctraverse (Proxy @FromData) (unI . mapKI fromData) prod
gProductFromBuiltinData _ = Nothing

{- |
  Unsafe version of 'gProductFromBuiltinData'.

  @since 1.1.0
-}
gProductFromBuiltinDataUnsafe ::
    forall (a :: Type) (repr :: [Type]).
    (IsProductType a repr, All UnsafeFromData repr) =>
    BuiltinData ->
    a
gProductFromBuiltinDataUnsafe (BuiltinData (List xs)) =
    let prod = fromJust $ SOP.fromList @repr xs
     in productTypeTo $
            runIdentity $
                hctraverse
                    (Proxy @UnsafeFromData)
                    (unI . mapKI (Identity . unsafeFromBuiltinData . BuiltinData))
                    prod
gProductFromBuiltinDataUnsafe _ = error "invalid representation"

-- | @since 1.1.0
instance
    forall (h :: Type) (p :: S -> Type).
    (PlutusTx.FromData h, PlutusTx.ToData h, PLift p) =>
    PConstantDecl (DerivePConstantViaDataList h p)
    where
    type PConstantRepr (DerivePConstantViaDataList h p) = [PlutusTx.Data]
    type PConstanted (DerivePConstantViaDataList h p) = p
    pconstantToRepr (DerivePConstantViaDataList x) = case PlutusTx.toData x of
        (PlutusTx.List xs) -> xs
        _ -> error "ToData repr is not a List!"
    pconstantFromRepr = coerce (PlutusTx.fromData @h . PlutusTx.List)

-- | @since 1.1.0
instance
    forall (a :: Type) (repr :: [Type]).
    (IsProductType a repr, All ToData repr) =>
    ToData (ProductIsData a)
    where
    toBuiltinData = coerce (gProductToBuiltinData @a)

-- | @since 1.1.0
instance
    forall (a :: Type) (repr :: [Type]).
    (IsProductType a repr, All UnsafeFromData repr) =>
    UnsafeFromData (ProductIsData a)
    where
    unsafeFromBuiltinData = coerce (gProductFromBuiltinDataUnsafe @a)

-- | @since 1.1.0
instance
    forall (a :: Type) (repr :: [Type]).
    (IsProductType a repr, All FromData repr) =>
    FromData (ProductIsData a)
    where
    fromBuiltinData = coerce (gProductFromBuiltinData @a)

--------------------------------------------------------------------------------
-- PEnumData

{- |
  Wrapper for deriving 'ToData', 'FromData' using an integral representation via 'Enum'.

  @since 1.1.0
-}
newtype EnumIsData (a :: Type) = EnumIsData a

-- | @since 1.1.0
instance forall (a :: Type). (Enum a) => ToData (EnumIsData a) where
    toBuiltinData = coerce $ toBuiltinData . toInteger . fromEnum @a

-- | @since 1.1.0
instance forall (a :: Type). (Enum a) => FromData (EnumIsData a) where
    fromBuiltinData = coerce $ fmap (toEnum @a . fromInteger) . fromBuiltinData @Integer

-- | @since 1.1.0
instance forall (a :: Type). (Enum a) => UnsafeFromData (EnumIsData a) where
    unsafeFromBuiltinData = coerce . toEnum @a . fromInteger . unsafeFromBuiltinData @Integer

data PlutusTypeEnumData

class
    ( PGeneric p
    , forall s. Enum (p s)
    , forall s. Bounded (p s)
    ) =>
    IsPlutusTypeEnumData (p :: S -> Type)
instance
    ( PGeneric p
    , forall s. Enum (p s)
    , forall s. Bounded (p s)
    ) =>
    IsPlutusTypeEnumData p

instance PlutusTypeStrat PlutusTypeEnumData where
    type PlutusTypeStratConstraint PlutusTypeEnumData = IsPlutusTypeEnumData
    type DerivedPInner PlutusTypeEnumData a = PInteger
    derivedPCon = fromInteger . toInteger . fromEnum
    derivedPMatch = pmatchEnum

{- |
  Wrapper for deriving `PConstantDecl` using an integral representation via 'Enum'.

  @since 1.1.0
-}
newtype DerivePConstantViaEnum (h :: Type) (p :: S -> Type)
    = DerivePConstantEnum h

-- | @since 1.1.0
instance
    forall (p :: S -> Type) (h :: Type).
    ( PLift p
    , Enum h
    , DerivePlutusType p
    , DPTStrat p ~ PlutusTypeEnumData
    ) =>
    PConstantDecl (DerivePConstantViaEnum h p)
    where
    type PConstantRepr (DerivePConstantViaEnum h p) = Integer
    type PConstanted (DerivePConstantViaEnum h p) = p

    pconstantToRepr = toInteger . fromEnum @h . coerce
    pconstantFromRepr = Just . coerce . toEnum @h . fromInteger

-- Enumerate all cases. This relies on 'enumFrom' not being partial or having
-- \'gaps\'; we cannot guarantee this in general.
safeCases :: forall (a :: Type). (Bounded a, Enum a) => [a]
safeCases = enumFrom minBound

{- |
  Pattern match over the integral representation of a 'Bounded' and 'Enum' instance.

  @since 1.1.0
-}
pmatchEnum ::
    forall (a :: Type) (b :: S -> Type) (s :: S).
    (Bounded a, Enum a) =>
    Term s PInteger ->
    (a -> Term s b) ->
    Term s b
pmatchEnum x f = unTermCont $ do
    x' <- pletC x
    let branch :: a -> Term s b -> Term s b
        branch n =
            pif
                (x' #== (fromInteger . toInteger . fromEnum $ n))
                (f n)

    pure $ foldr branch (f maxBound) safeCases

{- | Pattern match on 'PData' by treating it as an instance of 'Bounded' and
 'Enum'.

 @since 1.1.0
-}
pmatchEnumFromData ::
    forall (a :: Type) (b :: S -> Type) (s :: S).
    (Bounded a, Enum a) =>
    Term s PData ->
    (Maybe a -> Term s b) ->
    Term s b
pmatchEnumFromData d f = unTermCont $ do
    x <- pletC $ pasInt # d

    let branch :: a -> Term s b -> Term s b
        branch n =
            pif
                (x #== (fromInteger . toInteger . fromEnum $ n))
                (f $ Just n)

    pure $ foldr branch (f Nothing) safeCases
