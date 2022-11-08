module Plutarch.Extra.ExtendedAssetClass (
  -- * Types

  -- ** Haskell
  ExtendedAssetClass (..),

  -- ** Plutarch
  PExtendedAssetClass (..),

  -- * Functions

  -- ** Plutarch
  pextendedAssetClassValueOf,
  peqClasses,
) where

import Data.Aeson (
  FromJSON (parseJSON),
  ToJSON (toEncoding, toJSON),
  object,
  pairs,
  withObject,
  (.:),
 )
import Data.Aeson.Encoding (pair)
import Data.Text (Text, unpack)
import Optics.AffineTraversal (An_AffineTraversal, atraversal)
import Optics.Getter (A_Getter, to, view)
import Optics.Label (LabelOptic (labelOptic))
import Optics.Setter (set)
import Plutarch.Api.V1 (
  AmountGuarantees,
  KeyGuarantees,
  PCurrencySymbol,
  PValue,
 )
import Plutarch.DataRepr (DerivePConstantViaData (DerivePConstantViaData))
import Plutarch.Extra.AssetClass (
  AssetClass (AssetClass),
  PAssetClassData,
  ptoScottEncoding,
 )
import Plutarch.Extra.Value (passetClassValueOf, psymbolValueOf)
import Plutarch.Lift (
  PConstantDecl,
  PUnsafeLiftDecl (PLifted),
 )
import PlutusLedgerApi.V2 (
  CurrencySymbol,
  Data (Constr),
  FromData (fromBuiltinData),
  ToData (toBuiltinData),
  TokenName,
  UnsafeFromData (unsafeFromBuiltinData),
  builtinDataToData,
  dataToBuiltinData,
  fromData,
  toData,
 )

{- | An 'AssetClass' whose 'TokenName' may or may not be relevant.

 @since 3.14.2
-}
data ExtendedAssetClass
  = -- | 'TokenName' is irrelevant
    AnyToken CurrencySymbol
  | -- | 'TokenName' is relevant
    FixedToken AssetClass
  deriving stock
    ( -- | @since 3.14.2
      Generic
    , -- | @since 3.14.2
      Show
    , -- | @since 3.14.2
      Eq
    , -- | @since 3.14.2
      Ord
    )

-- | @since 3.14.2
instance FromData ExtendedAssetClass where
  fromBuiltinData dat = case builtinDataToData dat of
    Constr 0 [dat'] -> AnyToken <$> fromData dat'
    Constr 1 [dat'] -> FixedToken <$> fromData dat'
    _ -> Nothing

-- | @since 3.14.2
instance UnsafeFromData ExtendedAssetClass where
  unsafeFromBuiltinData dat = case fromBuiltinData dat of
    Just eac -> eac
    Nothing -> error "unsafeFromBuiltinData: Could not make an ExtendedAssetClass"

-- | @since 3.14.2
instance ToData ExtendedAssetClass where
  toBuiltinData =
    dataToBuiltinData . \case
      AnyToken x -> Constr 0 [toData x]
      FixedToken x -> Constr 1 [toData x]

-- | @since 3.14.2
deriving via
  (DerivePConstantViaData ExtendedAssetClass PExtendedAssetClass)
  instance
    PConstantDecl ExtendedAssetClass

-- | @since 3.14.2
instance ToJSON ExtendedAssetClass where
  {-# INLINEABLE toJSON #-}
  toJSON = \case
    AnyToken x ->
      object
        [ ("tag", toJSON @Text "anyToken")
        , ("symbol", toJSON x)
        ]
    FixedToken x ->
      object
        [ ("tag", toJSON @Text "fixedToken")
        , ("symbol", toJSON . view #symbol $ x)
        , ("name", toJSON . view #name $ x)
        ]
  {-# INLINEABLE toEncoding #-}
  toEncoding = \case
    AnyToken x ->
      pairs $
        pair "tag" (toEncoding @Text "anyToken")
          <> pair "symbol" (toEncoding x)
    FixedToken x ->
      pairs $
        pair "tag" (toEncoding @Text "fixedToken")
          <> pair "symbol" (toEncoding . view #symbol $ x)
          <> pair "name" (toEncoding . view #name $ x)

-- | @since 3.14.2
instance FromJSON ExtendedAssetClass where
  {-# INLINEABLE parseJSON #-}
  parseJSON = withObject "ExtendedAssetClass" $ \obj -> do
    tag :: Text <- obj .: "tag"
    cs <- obj .: "symbol"
    case tag of
      "anyToken" -> do
        pure . AnyToken $ cs
      "fixedToken" -> do
        tn <- obj .: "name"
        pure . FixedToken . AssetClass cs $ tn
      _ -> fail $ "Not a valid tag: " <> unpack tag

{- | We can always retrieve a 'CurrencySymbol', but depending on what we have,
 we may be unable to change it.

 @since 3.14.2
-}
instance
  (k ~ A_Getter, a ~ CurrencySymbol, b ~ CurrencySymbol) =>
  LabelOptic "symbol" k ExtendedAssetClass ExtendedAssetClass a b
  where
  labelOptic = to $ \case
    AnyToken x -> x
    FixedToken x -> view #symbol x

{- | We may not necessarily have a 'TokenName' that matters; if we do, then
 changing it is fine.

 @since 3.14.2
-}
instance
  (k ~ An_AffineTraversal, a ~ TokenName, b ~ TokenName) =>
  LabelOptic "name" k ExtendedAssetClass ExtendedAssetClass a b
  where
  labelOptic = atraversal out $ \eac tn -> case eac of
    AnyToken _ -> eac
    FixedToken x -> FixedToken . set #name tn $ x
    where
      out :: ExtendedAssetClass -> Either ExtendedAssetClass TokenName
      out = \case
        eac@(AnyToken _) -> Left eac
        FixedToken x -> Right . view #name $ x

{- | We can always \'pull out\' an 'AssetClass', by essentially \'forgetting\'
 the significance of our \'TokenName\'. In cases where it's not significant,
 we stub it with the empty name.

 @since 3.14.2
-}
instance
  (k ~ A_Getter, a ~ AssetClass, b ~ AssetClass) =>
  LabelOptic "assetClass" k ExtendedAssetClass ExtendedAssetClass a b
  where
  labelOptic = to $ \case
    AnyToken x -> AssetClass x ""
    FixedToken x -> x

{- | Plutarch equivalent to 'ExtendedAssetClass'.

 @since 3.14.2
-}
data PExtendedAssetClass (s :: S)
  = PAnyToken (Term s (PDataRecord '["_0" ':= PCurrencySymbol]))
  | PFixedToken (Term s (PDataRecord '["_0" ':= PAssetClassData]))
  deriving stock
    ( -- | @since 3.14.2
      Generic
    )
  deriving anyclass
    ( -- | @since 3.14.2
      PEq
    , -- | @since 3.14.2
      PlutusType
    , -- | @since 3.14.2
      PShow
    , -- | @since 3.14.2
      PIsData
    )

-- | @since 3.14.2
instance DerivePlutusType PExtendedAssetClass where
  type DPTStrat _ = PlutusTypeData

-- | @since 3.14.2
instance PUnsafeLiftDecl PExtendedAssetClass where
  type PLifted PExtendedAssetClass = ExtendedAssetClass

{- | As 'passetClassValueOf', but for 'PExtendedAssetClass'.

 @since 3.14.2
-}
pextendedAssetClassValueOf ::
  forall (keys :: KeyGuarantees) (amounts :: AmountGuarantees) (s :: S).
  Term s (PExtendedAssetClass :--> PValue keys amounts :--> PInteger)
pextendedAssetClassValueOf = phoistAcyclic $ plam $ \eac value ->
  pmatch eac $ \case
    PAnyToken t -> psymbolValueOf # pfromData (pfield @"_0" # t) # value
    PFixedToken t ->
      let t' = ptoScottEncoding #$ pfield @"_0" # t
       in passetClassValueOf # t' # value

{- | Compare a 'PExtendedAssetClass' to a 'PAssetClass'.

 @since 3.14.2
-}
peqClasses ::
  forall (s :: S).
  Term s (PExtendedAssetClass :--> PAssetClassData :--> PBool)
peqClasses = phoistAcyclic $ plam $ \eac acd ->
  pmatch eac $ \case
    PAnyToken t ->
      pfromData (pfield @"_0" # t) #== pfromData (pfield @"symbol" # acd)
    PFixedToken t -> pfromData (pfield @"_0" # t) #== acd