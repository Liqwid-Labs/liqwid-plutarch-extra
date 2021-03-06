{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Plutarch.Extra.Field (pletAll, pletAllC) where

import GHC.TypeLits (Symbol)
import Plutarch.DataRepr.Internal.Field (
    BindFields,
    Bindings,
    BoundTerms,
    HRec,
    HRecOf,
    PDataFields (PFields),
    pletFields,
 )
import Plutarch.Prelude (PLabeledType (..), Term, TermCont, tcont)

type family BindAll (ps :: [PLabeledType]) :: [Symbol] where
    BindAll '[] = '[]
    BindAll ((name ':= _) ': xs) = name : BindAll xs

{- | Same as `pletFields` but instead of specifiying fields, it will take all fields.

 @since 1.2.1
-}
pletAll ::
    forall a s b ps bs.
    ( PDataFields a
    , ps ~ PFields a
    , bs ~ Bindings ps (BindAll ps)
    , BindFields ps bs
    ) =>
    Term s a ->
    (HRecOf a (BindAll ps) s -> Term s b) ->
    Term s b
pletAll = pletFields @(BindAll ps)

{- | TermCont version of `pletAll`

 @since 1.2.1
-}
pletAllC ::
    forall a s b ps bs.
    ( PDataFields a
    , ps ~ PFields a
    , bs ~ Bindings ps (BindAll ps)
    , BindFields ps bs
    ) =>
    Term s a ->
    TermCont @b s (HRec (BoundTerms ps bs s))
pletAllC = tcont . pletFields @(BindAll ps)
