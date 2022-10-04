{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

module Plutarch.Extra.PlutusType (
  PlutusTypeDataList
  ) where

import Plutarch.DataRepr (PFields)
import Generics.SOP.GGP (GCode)
import GHC.TypeLits (
  TypeError, 
  ErrorMessage (Text, (:$$:), (:<>:), ShowType)
  )
import Data.Kind (Constraint)
import Plutarch.Lift (PUnsafeLiftDecl (PLifted), PConstanted)
import Generics.SOP (SOP (SOP), NS (Z, S),
  NP (Nil, (:*)))
import Generics.SOP.Constraint (Head, SameShapeAs)
import Plutarch.Internal.PlutusType (
  PlutusTypeStrat (PlutusTypeStratConstraint,
                   DerivedPInner,
                   derivedPCon,
                   derivedPMatch)
  )
import Plutarch.Internal.Generic (PGeneric, PCode, gpto, gpfrom)

-- | @since 3.10.0
data PlutusTypeDataList

-- | @since 3.10.0
instance PlutusTypeStrat PlutusTypeDataList where
  type PlutusTypeStratConstraint PlutusTypeDataList = IsPlutusTypeDataList
  type DerivedPInner PlutusTypeDataList a = GetPRecord a
  derivedPCon x = case gpfrom x of 
    SOP (Z (x' :* Nil)) -> x'
    SOP (S x') -> case x' of {} -- impossible
  derivedPMatch rec f = f . gpto . SOP . Z $ rec :* Nil

-- Helpers

class (
  PGeneric p,
  PCode p ~ '[ '[ PDataRecord (PFields (Head (Head (PCode p)))) ] ]
  ) => IsPlutusTypeDataList p

instance (
  PGeneric p,
  PUnsafeLiftDecl p,
  PCode p ~ '[ '[ PDataRecord (PFields (Head (Head (PCode p)))) ] ],
  SameShapeAs (GetRecordTypes (GCode (PLifted p))) (PUnlabel (GetPRecord' (PCode p))),
  MatchTypes (UD (GetRecordTypes (GCode (PLifted p)))) (PUnlabel (GetPRecord' (PCode p)))
  ) => IsPlutusTypeDataList p

type family GetPRecord' (a :: [[S -> Type]]) :: [PLabeledType] where
  GetPRecord' '[ '[PDataRecord a]] = a

type family GetPRecord (a :: S -> Type) :: S -> Type where
  GetPRecord a = PDataRecord (GetPRecord' (PCode a))

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

type MatchTypes (n :: [S -> Type]) (m :: [S -> Type]) =
  (MatchTypesError n m (MatchTypes' n m))

type family UD' (p :: S -> Type) :: S -> Type where
  UD' (p x1 x2 x3 x4 x5) = p (UD' x1) (UD' x2) (UD' x3) (UD' x4) (UD' x5)
  UD' (p x1 x2 x3 x4) = p (UD' x1) (UD' x2) (UD' x3) (UD' x4)
  UD' (p x1 x2 x3) = p (UD' x1) (UD' x2) (UD' x3)
  UD' (p x1 x2) = p (UD' x1) (UD' x2)
  UD' (p x1) = p (PAsData (UD' x1))
  UD' p = p

type family UD (p :: [S -> Type]) :: [S -> Type] where
  UD (x ': xs) = UD' x ': UD xs
  UD '[] = '[]

type family GetRecordTypes (n :: [[Type]]) :: [S -> Type] where
  GetRecordTypes '[x ': xs] = PConstanted x ': GetRecordTypes '[xs]
  GetRecordTypes '[ '[]] = '[]

type family PUnlabel (n :: [PLabeledType]) :: [S -> Type] where
  PUnlabel ((_ ':= p) ': xs) = p ': PUnlabel xs
  PUnlabel '[] = '[]
