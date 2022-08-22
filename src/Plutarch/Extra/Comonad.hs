module Plutarch.Extra.Comonad (
    -- * Type classes
    PExtend (..),
    PComonad (..),
) where

import Plutarch.Extra.Functor (PFunctor (PSubcategory))
import Plutarch.Extra.TermCont (pletC, pmatchC)
import Plutarch.List (puncons)

{- | Gives a 'PFunctor' the ability to be \'extended\'.

 = Laws

 * /Composition:/ @('pextend' '#' f) '#>>>' ('pextend' '#' g)@ @=@ @'pextend'
 (('pextend' '#' f) '#>>>' g)@

 @since 1.0.0
-}
class (PFunctor w) => PExtend (w :: (S -> Type) -> S -> Type) where
    pextend ::
        forall (a :: S -> Type) (b :: S -> Type) (s :: S).
        (PSubcategory w a, PSubcategory w b) =>
        Term s ((w a :--> b) :--> w a :--> w b)

{- | Applies the given function over every proper suffix of a 'PList', from
 longest to shortest, and returns their results in a 'PList'.

 @since 1.0.0
-}
instance PExtend PList where
    pextend ::
        forall (a :: S -> Type) (b :: S -> Type) (s :: S).
        Term s ((PList a :--> b) :--> PList a :--> PList b)
    pextend = phoistAcyclic $
        plam $ \f xs -> unTermCont $ do
            t <- pmatchC (puncons # xs)
            case t of
                PNothing -> pure pnil
                PJust t' -> do
                    PPair _ ttail <- pmatchC t'
                    pure $ go # f # ttail
      where
        go ::
            forall (s' :: S).
            Term s' ((PList a :--> b) :--> PList a :--> PList b)
        go = phoistAcyclic $
            plam $ \f xs -> unTermCont $ do
                res <- pletC (f # xs)
                t <- pmatchC (puncons # xs)
                case t of
                    PNothing -> pure $ pcons # res # pnil
                    PJust t' -> do
                        PPair _ ttail <- pmatchC t'
                        pure $ pcons # res # (go # f # ttail)

-- | @since 1.0.0
instance PExtend (PPair a) where
    pextend = phoistAcyclic $
        plam $ \f p -> unTermCont $ do
            PPair x _ <- pmatchC p
            pure . pcon . PPair x $ f # p

{- | Makes a 'PExtend' into a comonad on a subcategory of 'Plut'.

 = Laws

 * /Extend-extract:/ @'pextend' '#' 'pextract'@ @=@ @'pidentity'@
 * /Extract-extend:/ @('pextend' '#' f) '#>>>' 'pextract'@ @=@ @f@

 @since 1.0.0
-}
class (PExtend w) => PComonad (w :: (S -> Type) -> S -> Type) where
    pextract ::
        forall (a :: S -> Type) (s :: S).
        (PSubcategory w a) =>
        Term s (w a :--> a)

-- | @since 1.0.0
instance PComonad (PPair a) where
    pextract = phoistAcyclic $
        plam $ \p -> unTermCont $ do
            PPair _ t <- pmatchC p
            pure t
