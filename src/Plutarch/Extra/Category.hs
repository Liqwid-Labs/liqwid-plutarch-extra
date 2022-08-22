{- |
 Module: Plutarch.Extra.Category
 Copyright: (C) Liqwid Labs 2022
 License: Apache 2.0
 Maintainer: Koz Ross <koz@mlabs.city>
 Portability: GHC only
 Stability: Experimental
-}
module Plutarch.Extra.Category (
    -- * Type classes
    PSemigroupoid (..),
    PCategory (..),

    -- * Helper functions
    pconst,
    (#<<<),
) where

import Plutarch.Extra.Profunctor (PProfunctor (PCoSubcategory, PContraSubcategory, prmap))

{- | Gives a 'PProfunctor' the ability to compose.

 = Laws

 * /Associativity:/ @(f '#>>>' g) '#>>>' h@ @=@ @f '#>>>' (g '#>>>' h)@

 @since 1.0.0
-}
class (PProfunctor p) => PSemigroupoid (p :: (S -> Type) -> (S -> Type) -> S -> Type) where
    (#>>>) ::
        forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type) (s :: S).
        ( PContraSubcategory p a
        , PContraSubcategory p b
        , PCoSubcategory p b
        , PCoSubcategory p c
        ) =>
        Term s (p a b) ->
        Term s (p b c) ->
        Term s (p a c)

-- | @since 1.0.0
instance PSemigroupoid (:-->) where
    (#>>>) ::
        forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type) (s :: S).
        Term s (a :--> b) ->
        Term s (b :--> c) ->
        Term s (a :--> c)
    t #>>> t' = go # t # t'
      where
        go ::
            forall (s' :: S).
            Term s' ((a :--> b) :--> (b :--> c) :--> (a :--> c))
        go = phoistAcyclic $
            plam $ \ab ->
                plam $ \bc ->
                    plam $ \x -> bc # (ab # x)

{- | Extends a 'PSemigroupoid' with a compositional identity.

 = Laws

 * /Identity:/ @'pidentity' '#>>>' f@ @=@ @f '#>>>' 'pidentity'@ @=@ @f@

 @since 1.0.0
-}
class (PSemigroupoid p) => PCategory (p :: (S -> Type) -> (S -> Type) -> S -> Type) where
    pidentity ::
        forall (a :: S -> Type) (s :: S).
        ( PContraSubcategory p a
        , PCoSubcategory p a
        ) =>
        Term s (p a a)

-- | @since 1.0.0
instance PCategory (:-->) where
    pidentity = phoistAcyclic $ plam id

{- | Given a \'result\', constructs an arrow sending absolutely anything to that
 \'result\'. Similar to Haskell's 'const', but over an arbitrary 'PCategory'.

 @since 1.0.0
-}
pconst ::
    forall
        (p :: (S -> Type) -> (S -> Type) -> S -> Type)
        (a :: S -> Type)
        (b :: S -> Type)
        (s :: S).
    ( PContraSubcategory p b
    , PCategory p
    , PCoSubcategory p b
    , PCoSubcategory p a
    ) =>
    Term s (a :--> p b a)
pconst = phoistAcyclic $ plam $ \x -> prmap # (go # x) # pidentity
  where
    go :: forall (s' :: S). Term s' (a :--> b :--> a)
    go = phoistAcyclic $ plam const

{- | Composition from right to left. Similar to Haskell's composition operator,
 but over an arbitrary 'PSemigroupoid'.

 @since 1.0.0
-}
(#<<<) ::
    forall
        (p :: (S -> Type) -> (S -> Type) -> S -> Type)
        (a :: S -> Type)
        (b :: S -> Type)
        (c :: S -> Type)
        (s :: S).
    ( PSemigroupoid p
    , PContraSubcategory p a
    , PContraSubcategory p b
    , PCoSubcategory p b
    , PCoSubcategory p c
    ) =>
    Term s (p b c) ->
    Term s (p a b) ->
    Term s (p a c)
t #<<< t' = t' #>>> t

infixr 1 #<<<
