{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Extra.Lift (
  -- * Derivation helpers for ToData, FromData and UnsafeFromData
  RecordIsData (..),
) where

import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Proxy (Proxy (Proxy))
import Generics.SOP (
  All,
  I,
  NP,
  NS (Z),
  SOP (SOP),
  hcmap,
  hcollapse,
  hctraverse,
  mapIK,
  mapKI,
  unI,
  unSOP,
  unZ,
 )
import qualified Generics.SOP as SOP
import Generics.SOP.GGP (GCode, GFrom, GTo, gfrom, gto)
import PlutusTx (
  Data (List),
  FromData (fromBuiltinData),
  ToData (toBuiltinData),
  UnsafeFromData (unsafeFromBuiltinData),
  fromData,
  toData,
 )
import PlutusTx.Builtins.Internal (BuiltinData (BuiltinData))

{- | Wrapper for deriving 'ToData', 'FromData' and 'UnsafeFromData'
 consistently, using the 'List' constructor of 'Data' as the underlying
 representation. Intended for record types, hence the name.

 For safety, we recommend using 'Plutarch.Extra.PlutusType.PlutusTypeRecord'
 as the deriving strategy for 'PlutusType' for the Plutarch equivalent of any
 type using 'RecordIsData'; this ensures consistency, including in field
 ordering.

 For this to work, the type @a@ must:

 - Implement 'Generic'; and
 - Have fields with themselves have instances of 'ToData', 'FromData' and
 'UnsafeFromData', depending on what you're deriving.

 If you get weird error messages, check that you meet these criteria. Also,
 let us know, so we can have more helpful error messages!

 @since 3.10.0
-}
newtype RecordIsData (a :: Type) = RecordIsData a

-- | @since 3.10.0
instance
  (Generic a, GCode a ~ '[repr], All ToData repr, GFrom a) =>
  ToData (RecordIsData a)
  where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (RecordIsData x) =
    BuiltinData
      . List
      . hcollapse
      . hcmap (Proxy @ToData) (mapIK toData)
      . toProduct
      $ x

-- | @since 3.10.0
instance
  (Generic a, GCode a ~ '[repr], All UnsafeFromData repr, GTo a) =>
  UnsafeFromData (RecordIsData a)
  where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData = \case
    BuiltinData (List xs) -> case SOP.fromList xs of
      Nothing ->
        error $
          "unsafeFromBuiltinData: "
            <> "wrong number of items for a derived RecordIsData"
      Just prod ->
        RecordIsData
          . fromProduct
          . runIdentity
          . hctraverse (Proxy @UnsafeFromData) (unI . mapKI (Identity . unsafeFromBuiltinData . BuiltinData))
          $ prod
    _ ->
      error $
        "unsafeFromBuiltinData: "
          <> "Derived RecordIsData expects a list, but got something else."

-- | @since 3.10.0
instance
  (Generic a, GCode a ~ '[repr], All FromData repr, GTo a) =>
  FromData (RecordIsData a)
  where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData = \case
    BuiltinData (List xs) ->
      RecordIsData <$> do
        prod <- SOP.fromList xs
        fromProduct <$> hctraverse (Proxy @FromData) (unI . mapKI fromData) prod
    _ -> Nothing

-- Helpers

toProduct ::
  forall (repr :: [Type]) (a :: Type).
  (Generic a, GCode a ~ '[repr], GFrom a) =>
  a ->
  NP I repr
toProduct = unZ . unSOP . gfrom

fromProduct ::
  forall (repr :: [Type]) (a :: Type).
  (Generic a, GCode a ~ '[repr], GTo a) =>
  NP I repr ->
  a
fromProduct = gto . SOP . Z
