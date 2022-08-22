-- Needed to ensure mapBoring is used properly
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{- |
 Module: Plutarch.Extra.Boring
 Copyright: (C) Liqwid Labs 2022
 License: Apache 2.0
 Maintainer: Koz Ross <koz@mlabs.city>
 Portability: GHC only
 Stability: Experimental

 Defines a Plutarch notion of a type which provides no information from its
 values. Inspired by [Conor McBride](https://stackoverflow.com/a/33115522/2629787).
-}
module Plutarch.Extra.Boring (
    -- * Type class
    PBoring (..),

    -- * Functions
    mapBoring,
) where

{- | Represents singleton values. They are \'boring\' as having a value of that
 type tells you absolutely nothing, as they're all the same.

 = Laws

 * /Singleton/: @x = boring@

 @since 1.2.0
-}
class PBoring (a :: S -> Type) where
    pboring :: Term s a

-- | @since 1.2.0
instance PBoring PUnit where
    pboring = pcon PUnit

{- | As every 'PBoring' instance is a singleton, we can always convert one
 boring value into another.

 @since 1.2.0
-}
mapBoring ::
    forall (a :: S -> Type) (b :: S -> Type) (s :: S).
    (PBoring a, PBoring b) =>
    Term s (a :--> b)
mapBoring = phoistAcyclic $ plam $ const pboring
