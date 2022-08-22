{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
 Module: Plutarch.Extra.Applicative
 Copyright: (C) Liqwid Labs 2022
 License: Apache 2.0
 Maintainer: Koz Ross <koz@mlabs.city>
 Portability: GHC only
 Stability: Experimental
-}
module Plutarch.Extra.Applicative (
    -- * Type classes
    PApply (..),
    PApplicative (..),

    -- * Functions
    (#<*>),
    (#*>),
    (#<*),
    preplicateA,
    preplicateA_,
    pwhen,
    punless,
) where

import Plutarch.Api.V1.Maybe (PMaybeData (PDJust, PDNothing))
import Plutarch.Extra.Boring (PBoring (pboring))
import Plutarch.Extra.Function (papply, pconst)
import Plutarch.Extra.Functor (PFunctor (PSubcategory))
import Plutarch.Extra.TermCont (pletC, pmatchC)
import Plutarch.List (puncons)

{- | 'PFunctor' with the ability to lift a multi-argument function. Similar to
 'Applicative' from Haskell, but without 'pure'. Much like 'PFunctor', we
 allow constraining the parametricity of a 'PApply'.

 = Laws

 Formally, @f@ must be a strong, lax semimonoidal endofunctor on a subcategory
 of @Plut@, as described by @f@'s 'PSubcategory' constraint. This means that
 the following must hold:

 * /Pure post-processing:/ @'pfmap' '#' f '#' ('pliftA2' '#' g '#' x '#' y)@
 @=@ @'pliftF2' '#' ('plam' '$' \z -> (g '#' z) '#>>>' f) '#' x '#' y@
 * /Pure pre-processing:/ @'pliftF2' '#' f '#' ('pfmap' '#' g '#' x) '#'
 ('pfmap' '#' h '#' y)@ @=@ @'pliftF2' '#' ('plam' '$' \z1 z2 -> f '#' (g '#'
 z1) '#' (h '#' z2)) '#' x '#' y@

 If @'PSubcategory' f ~ 'Plut'@, we must also have:

 * /Associativity:/ @'pliftF2' '#' f '#' x '#' ('pliftF2' '#' g '#' y '#' z)@
 @=@ @'pliftF2' '#' 'papply' '#' ('pliftF2' '#' ('plam' '$' \z1 z2 -> (g '#'
 z2) '#>>>' (f '#' z1)) '#' x '#' y) '#' z@

 = Note

 If @'PSubcategory' f@ is /not/ 'Plut', this only gives us the ability to lift
 functions whose arity is /exactly/ two. This is in contrast with Haskell,
 where being able to lift any arity above 1 gives the ability to lift any
 arity whatsoever. Since @Plut@ is cartesian closed, we retain the \'arbitrary
 arity lift\' if @'PSubcategory' f ~ 'Plut'@.

 @since 1.0.0
-}
class (PFunctor f) => PApply (f :: (S -> Type) -> S -> Type) where
    pliftA2 ::
        forall (a :: S -> Type) (b :: S -> Type) (c :: S -> Type) (s :: S).
        (PSubcategory f a, PSubcategory f b, PSubcategory f c) =>
        Term s ((a :--> b :--> c) :--> f a :--> f b :--> f c)

-- | @since 1.0.0
instance PApply PMaybe where
    pliftA2 = phoistAcyclic $
        plam $ \f xs ys -> unTermCont $ do
            xs' <- pmatchC xs
            ys' <- pmatchC ys
            pure . pcon $ case (xs', ys') of
                (PJust x, PJust y) -> PJust $ f # x # y
                _ -> PNothing

-- | @since 1.0.0
instance PApply PMaybeData where
    pliftA2 = phoistAcyclic $
        plam $ \f xs ys -> unTermCont $ do
            xs' <- pmatchC xs
            ys' <- pmatchC ys
            case (xs', ys') of
                (PDJust x, PDJust y) -> do
                    x' <- pletC (pfromData $ pfield @"_0" # x)
                    y' <- pletC (pfromData $ pfield @"_0" # y)
                    pure . pcon . PDJust $ pdcons # pdata (f # x' # y') # pdnil
                _ -> pure . pcon . PDNothing $ pdnil

{- | Describes \'nondeterminism semantics\', similar to the Haskell instance of
 'Applicative' for lists. This is because, while it is possible to define
 \'zippy semantics\' for 'PApply', extending it to 'PApplicative' is
 impossible, as it would require an infinite or lazy on-chain structure for
 'ppure' to make sense.

 @since 1.0.0
-}
instance PApply PList where
    pliftA2 = phoistAcyclic $
        pfix
            #$ plam
            $ \self f xs ys -> unTermCont $ do
                t <- pmatchC (puncons # ys)
                case t of
                    PNothing -> pure pnil
                    PJust t' -> do
                        PPair thead ttail <- pmatchC t'
                        res <- pletC (pmap # plam (\x -> f # x # thead) # xs)
                        pure $ pconcat # res # (self # f # xs # ttail)

{- | Describes \'nondeterminism semantics\', for similar reasons to the 'PList'
 instance.

 @since 1.0.0
-}
instance PApply PBuiltinList where
    pliftA2 = phoistAcyclic $
        pfix
            #$ plam
            $ \self f xs ys -> unTermCont $ do
                t <- pmatchC (puncons # ys)
                case t of
                    PNothing -> pure pnil
                    PJust t' -> do
                        PPair thead ttail <- pmatchC t'
                        res <- pletC (pmap # plam (\x -> f # x # thead) # xs)
                        pure $ pconcat # res # (self # f # xs # ttail)

-- | @since 1.0.0
instance (forall (s :: S). Semigroup (Term s a)) => PApply (PPair a) where
    pliftA2 = phoistAcyclic $
        plam $ \f xs ys -> unTermCont $ do
            PPair x1 x2 <- pmatchC xs
            PPair y1 y2 <- pmatchC ys
            pure . pcon . PPair (x1 <> y1) $ f # x2 # y2

{- | Forwards the /first/ 'PLeft', similar to the 'Applicative' instance for
 - 'Either'.

 @since 1.0.0
-}
instance PApply (PEither e) where
    pliftA2 = phoistAcyclic $
        plam $ \f xs ys -> unTermCont $ do
            xs' <- pmatchC xs
            ys' <- pmatchC ys
            pure . pcon $ case (xs', ys') of
                (PLeft e, _) -> PLeft e
                (_, PLeft e) -> PLeft e
                (PRight x, PRight y) -> PRight $ f # x # y

{- | Extends a 'PApply' with the ability to lift arbitrary values.

 = Laws

 Formally, @f@ must be a lax monoidal endofunctor on a subcategory of @Plut@,
 as described by @f@'s 'PSubcategory' constraint. This means that the
 following must hold:

 * /Homomorphism:/ @'pliftF2' '#' f '#' ('ppure' '#' x) '#' ('ppure' '#' y)@
 @=@ @'ppure' '#' (f '#' x '#' y)@
 * /Interchange:/ @'pliftF2' '#' f '#' ('ppure' '#' x) '#' y@ @=@ @'pliftF2'
 '#' ('pflip' '#' f) '#' y '#' ('ppure' x)@

 If @'PSubcategory' f ~ 'Plut'@, we must also have:

 * /Identity:/ @'pliftF2' '#' 'papply' '#' ('ppure' '#' f) '#' x@ @=@ @'pfmap'
 '#' f '#' x@

 @since 1.0.0
-}
class (PApply f) => PApplicative (f :: (S -> Type) -> S -> Type) where
    ppure ::
        forall (a :: S -> Type) (s :: S).
        (PSubcategory f a) =>
        Term s (a :--> f a)

-- | @since 1.0.0
instance PApplicative PMaybe where
    ppure = phoistAcyclic $ plam $ pcon . PJust

-- | @since 1.0.0
instance PApplicative PMaybeData where
    ppure = phoistAcyclic $ plam $ \x -> pcon . PDJust $ pdcons # pdata x # pdnil

-- | @since 1.0.0
instance PApplicative PList where
    ppure = phoistAcyclic $ plam $ \x -> pcons # x # pnil

-- | @since 1.0.0
instance PApplicative PBuiltinList where
    ppure = phoistAcyclic $ plam $ \x -> pcons # x # pnil

-- | @since 1.0.0
instance (forall (s :: S). Monoid (Term s a)) => PApplicative (PPair a) where
    ppure = phoistAcyclic $ plam $ pcon . PPair mempty

-- | @since 1.0.0
instance PApplicative (PEither e) where
    ppure = phoistAcyclic $ plam $ pcon . PRight

{- | Plutarch equivalent to '<*>'. This is not a type class method of 'PApply',
 as in general, we cannot assume a subcategory of @Plut@ will be cartesian
 closed (that is, contain functions).

 @since 1.0.0
-}
(#<*>) ::
    forall (f :: (S -> Type) -> S -> Type) (a :: S -> Type) (b :: S -> Type) (s :: S).
    (PSubcategory f (a :--> b), PSubcategory f a, PSubcategory f b, PApply f) =>
    Term s (f (a :--> b)) ->
    Term s (f a) ->
    Term s (f b)
fs #<*> xs = pliftA2 # papply # fs # xs

infixl 4 #<*>

{- | Plutarch equivalent to '*>'. This could become a method of 'PApply' in the
 future, but as we don't see many more efficient implementations of this
 operator possible, we don't currently include it.

 @since 1.0.0
-}
(#*>) ::
    forall (f :: (S -> Type) -> S -> Type) (a :: S -> Type) (b :: S -> Type) (s :: S).
    (PSubcategory f a, PSubcategory f b, PApply f) =>
    Term s (f a) ->
    Term s (f b) ->
    Term s (f b)
t #*> t' = pliftA2 # plam (\_ x -> x) # t # t'

infixl 4 #*>

{- | Plutarch equivalent to '<*'. This could become a method of 'PApply' in the
 future, but as we don't see many more efficient implementations of this
 operator possible, we don't currently include it.

 @since 1.0.0
-}
(#<*) ::
    forall (f :: (S -> Type) -> S -> Type) (a :: S -> Type) (b :: S -> Type) (s :: S).
    (PSubcategory f a, PSubcategory f b, PApply f) =>
    Term s (f a) ->
    Term s (f b) ->
    Term s (f a)
t #<* t' = pliftA2 # pconst # t # t'

infixl 4 #<*

{- | 'preplicateA' @n@ @comp@ repeats @comp@ @n@ times (0 if @n@ is negative),
 collects the results into a 'PListLike', and returns a single computation
 producing them all.

 = Notes

 The type of the 'PListLike' is left flexible: you can set it using
 @TypeApplications@. We put that type parameter first to make this easier.

 @since 1.2.0
-}
preplicateA ::
    forall
        (ell :: (S -> Type) -> S -> Type)
        (f :: (S -> Type) -> S -> Type)
        (a :: S -> Type)
        (s :: S).
    ( PApplicative f
    , PListLike ell
    , PElemConstraint ell a
    , PSubcategory f (ell a)
    , PSubcategory f a
    ) =>
    Term s (PInteger :--> f a :--> f (ell a))
preplicateA = phoistAcyclic $
    pfix #$ plam $ \self count comp ->
        pif (0 #<= count) (ppure # pnil) (pliftA2 # pcons # comp # (self # (count - 1) # comp))

{- | As 'preplicateA', but ignores the results.

 @since 1.2.0
-}
preplicateA_ ::
    forall
        (f :: (S -> Type) -> S -> Type)
        (b :: S -> Type)
        (s :: S).
    (PApplicative f, PBoring b, PSubcategory f b) =>
    Term s (PInteger :--> f b :--> f b)
preplicateA_ = phoistAcyclic $
    pfix #$ plam $ \self count comp ->
        pif (0 #<= count) (ppure # pboring) (comp #*> (self # (count - 1) # comp))

{- | 'pwhen' @b@ @comp@ executes @comp@ if @b@ is 'PTrue', and does nothing
 otherwise.

 @since 1.2.0
-}
pwhen ::
    forall
        (f :: (S -> Type) -> S -> Type)
        (b :: S -> Type)
        (s :: S).
    (PApplicative f, PBoring b, PSubcategory f b) =>
    Term s (PBool :--> f b :--> f b)
pwhen = phoistAcyclic $ plam $ \b comp -> pif b comp (ppure # pboring)

{- | 'punless' @b@ @comp@ executes @comp@ if @b@ is 'PFalse', and does nothing
 otherwise.

 @since 1.2.0
-}
punless ::
    forall
        (f :: (S -> Type) -> S -> Type)
        (b :: S -> Type)
        (s :: S).
    (PApplicative f, PBoring b, PSubcategory f b) =>
    Term s (PBool :--> f b :--> f b)
punless = phoistAcyclic $ plam $ \b comp -> pif b (ppure # pboring) comp
