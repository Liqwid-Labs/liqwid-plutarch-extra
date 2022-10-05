{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Extra.PlutusType (
  -- * Derivation strategies
  PlutusTypeRecord,

  -- * Derivation helpers for PUnsafeLiftDecl and PConstantDecl
  LiftingPDataRecord (..),
) where

import Data.Kind (Constraint)
import Data.Proxy (Proxy (Proxy))
import Fcf (Eval, Exp, Map)
import GHC.TypeLits (
  ErrorMessage (ShowType, Text, (:$$:), (:<>:)),
  TypeError,
 )
import Generics.SOP (
  All,
  I,
  NP (Nil, (:*)),
  NS (S, Z),
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
import Generics.SOP.Constraint (Head, SameShapeAs)
import Generics.SOP.GGP (GCode, GFrom, GTo, gfrom, gto)
import Plutarch.DataRepr (PFields)
import Plutarch.Internal.Generic (PCode, PGeneric, gpfrom, gpto)
import Plutarch.Internal.PlutusType (
  PlutusTypeStrat (
    DerivedPInner,
    PlutusTypeStratConstraint,
    derivedPCon,
    derivedPMatch
  ),
 )
import Plutarch.Lift (
  PConstantDecl (
    PConstantRepr,
    PConstanted,
    pconstantFromRepr,
    pconstantToRepr
  ),
  PUnsafeLiftDecl (PLifted),
 )
import PlutusTx (Data, FromData, ToData, fromData, toData)

{- | A 'PlutusType' derivation strategy designed for use with wrappers around
 'PDataRecord'. Similar in intent to 'PlutusTypeData', but has additional
 checks to ensure we're actually wrapping a 'PDataRecord', as well as having a
 Haskell equivalent.

 = Using this strategy

 For this strategy to work, you must ensure that the following hold:

 - The type being derived over must have a Haskell equivalent, \'bridged\' by
 means of 'PUnsafeLiftDecl'.
 - Both the Haskell and Plutarch type must implement 'Generic'.
 - The Haskell and Plutarch types must have the same number of fields.
 - The Haskell and Plutarch types must have equivalent types in each position.

 If you get weird errors, check that all the above hold. Also, please report
 it to us, so we can get better error messages!

 @since 3.10.0
-}
data PlutusTypeRecord

-- | @since 3.10.0
instance PlutusTypeStrat PlutusTypeRecord where
  type PlutusTypeStratConstraint PlutusTypeRecord = IsPlutusTypeRecord
  type DerivedPInner PlutusTypeRecord a = PDataRecord (PFields (Head (Head (PCode a))))
  derivedPCon x = case gpfrom x of
    SOP (Z (x' :* Nil)) -> x'
    -- This is an impossible case.
    SOP (S x') -> case x' of {}
  derivedPMatch rec f = f . gpto . SOP . Z $ rec :* Nil

{- | Derivation helper for deriving 'PConstantDecl' for the Haskell equivalent
 of a Plutus record.

 Using this via-derivation ensures that we have a faithful representation
 between the chosen Plutarch equivalent and ourselves, using similar
 techniques to 'PlutusTypeRecord'.

 To ensure this works, the following must hold:

 - @a@ and @p@ must be equivalents in their respective \'worlds\', \'bridged\'
 by means of 'PUnsafeLiftDecl'.
 - @a@ and @p@ must both be instances of 'Generic'.
 - @a@ and @p@ (or whatever @p@ is wrapping) must have the same number of
 fields.
 - @a@ and @p@ (or whatever @p@ is wrapping) must have equivalent types in
 each position.

 If you get weird errors, check that all the above hold. Also, please report
 it to us, so we can get better error messages!

 @since 3.10.0
-}
newtype LiftingPDataRecord (p :: S -> Type) (a :: Type)
  = LiftingPDataRecord a

-- | @since 3.10.0
instance
  ( IsPlutusTypeRecord p
  , Generic a
  , GCode a ~ '[repr]
  , All ToData repr
  , All FromData repr
  , GFrom a
  , GTo a
  ) =>
  PConstantDecl (LiftingPDataRecord p a)
  where
  type PConstantRepr (LiftingPDataRecord p a) = [Data]
  type PConstanted (LiftingPDataRecord p a) = p
  pconstantToRepr (LiftingPDataRecord x) =
    hcollapse . hcmap (Proxy @ToData) (mapIK toData) . toProduct $ x
  pconstantFromRepr dat =
    LiftingPDataRecord <$> do
      prod <- SOP.fromList dat
      fromProduct <$> hctraverse (Proxy @FromData) (unI . mapKI fromData) prod

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

-- First-class families-style helpers

-- Converts a type to its Plutarch equivalent

data ToPlutarch :: Type -> Exp (S -> Type)

type instance Eval (ToPlutarch a) = PConstanted a

-- 'Pulls off' the type of a PLabeledType

data Unlabel :: PLabeledType -> Exp (S -> Type)

type instance Eval (Unlabel (_ ':= p)) = p

-- A 'constraint summarizer', to help write a complex constraint.
--
-- We do this using a combination of type class and instance because
-- PlutusTypeStratConstraint wants something of kind S -> Type -> Constraint,
-- which we can't provide using a synonym if we want to 'name' the argument.

class
  ( -- The Plutarch type needs to be an instance of Generic
    PGeneric p
  , -- We need a Haskell equivalent
    PUnsafeLiftDecl p
  , -- We need to be a newtype around PDataRecord, or a single-constructor data
    -- declaration whose only field is a PDataRecord
    PCode p ~ '[ '[PDataRecord (PFields (Head (Head (PCode p))))]]
  , -- Our Haskell and Plutarch types must have identical field counts
    SameShapeAs
      (Eval (Map ToPlutarch (Head (GCode (PLifted p)))))
      (Eval (Map Unlabel (PFields (Head (Head (PCode p))))))
  , -- Our Haskell and Plutarch types must have the same field types in the same
    -- positions
    MatchTypes
      (UD (Eval (Map ToPlutarch (Head (GCode (PLifted p))))))
      (Eval (Map Unlabel (PFields (Head (Head (PCode p))))))
  ) =>
  IsPlutusTypeRecord p

-- Same as above, but with some rigid type variables to better convey intent. We
-- can't do this in superclass constraints for some bizarre reason.
instance
  ( pfields ~ PFields (Head (Head (PCode p)))
  , fieldTypes ~ Eval (Map ToPlutarch (Head (GCode (PLifted p))))
  , pfieldTypes ~ Eval (Map Unlabel pfields)
  , PGeneric p
  , PUnsafeLiftDecl p
  , PCode p ~ '[ '[PDataRecord pfields]]
  , SameShapeAs fieldTypes pfieldTypes
  , MatchTypes (UD fieldTypes) pfieldTypes
  ) =>
  IsPlutusTypeRecord p

-- Ensures we have the same structure, with good error messages when we don't.

type MatchTypes (n :: [S -> Type]) (m :: [S -> Type]) =
  (MatchTypesError n m (MatchTypes' n m))

type family MatchTypes' (n :: [S -> Type]) (m :: [S -> Type]) :: Bool where
  MatchTypes' '[] '[] = 'True
  MatchTypes' (x ': xs) (x ': ys) = MatchTypes' xs ys
  MatchTypes' (x ': xs) (y ': ys) = 'False
  MatchTypes' '[] ys = 'False
  MatchTypes' xs '[] = 'False

type family MatchTypesError (n :: [S -> Type]) (m :: [S -> Type]) (a :: Bool) :: Constraint where
  MatchTypesError _ _ 'True = ()
  MatchTypesError n m 'False =
    ( 'True ~ 'False
    , TypeError
        ( 'Text "Error when deriving 'PlutusTypeDataList':"
            ':$$: 'Text "\tMismatch between constituent Haskell and Plutarch types"
            ':$$: 'Text "Constituent Haskell Types: "
            ':$$: 'Text "\t"
            ':<>: 'ShowType n
            ':$$: 'Text "Constituent Plutarch Types: "
            ':$$: 'Text "\t"
            ':<>: 'ShowType m
        )
    )

-- 'Maps over' the 'stuff in' function below.

type family UD (p :: [S -> Type]) :: [S -> Type] where
  UD (x ': xs) = UD' x ': UD xs
  UD '[] = '[]

-- Recursively 'stuffs in' PAsData everywhere it can.

type family UD' (p :: S -> Type) :: S -> Type where
  UD' (p x1 x2 x3 x4 x5) = p (UD' x1) (UD' x2) (UD' x3) (UD' x4) (UD' x5)
  UD' (p x1 x2 x3 x4) = p (UD' x1) (UD' x2) (UD' x3) (UD' x4)
  UD' (p x1 x2 x3) = p (UD' x1) (UD' x2) (UD' x3)
  UD' (p x1 x2) = p (UD' x1) (UD' x2)
  UD' (p x1) = p (PAsData (UD' x1))
  UD' p = p
