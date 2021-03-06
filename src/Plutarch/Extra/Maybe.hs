{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}

module Plutarch.Extra.Maybe (
    -- * Utility functions for working with 'PMaybe'
    pfromJust,
    ptraceIfNothing,
    pisJust,
    pmaybe,

    -- * Utility functions for working with 'PMaybeData'
    pfromDJust,
    pisDJust,

    -- * Conversion between 'PMaybe' and 'PMaybeData'
    pmaybeToMaybeData,

    -- * TermCont-based combinators
    pexpectJustC,
) where

import Data.Kind (Type)
import Plutarch (
    PCon (pcon),
    S,
    Term,
    phoistAcyclic,
    plam,
    pmatch,
    (#),
    type (:-->),
 )
import Plutarch.Api.V1.Maybe (PMaybeData (PDJust, PDNothing))
import Plutarch.Bool (PBool)
import Plutarch.Builtin (PIsData, pdata, pfromData)
import Plutarch.DataRepr (pdcons, pdnil, pfield)
import Plutarch.Lift (pconstant)
import Plutarch.Maybe (PMaybe (PJust, PNothing))
import Plutarch.String (PString)
import Plutarch.TermCont (TermCont, tcont)
import Plutarch.Trace (ptraceError)

--------------------------------------------------------------------------------
-- Utility functions for working with 'PMaybe'.

{- | Extracts the element out of a 'PJust' and throws an error if its argument is 'PNothing'.

    @since 1.1.0
-}
pfromJust ::
    forall (a :: S -> Type) (s :: S).
    Term s (PMaybe a :--> a)
pfromJust = phoistAcyclic $
    plam $ \t -> pmatch t $ \case
        PNothing -> ptraceError "pfromJust: found PNothing"
        PJust x -> x

{- | Extracts the element out of a 'PJust' and throws a custom error if it's given a 'PNothing'.

    @since 1.0.0
-}
ptraceIfNothing ::
    forall (a :: S -> Type) (s :: S).
    -- | The custom error message.
    Term s PString ->
    Term s (PMaybe a) ->
    Term s a
ptraceIfNothing err t = pmatch t $ \case
    PNothing -> ptraceError err
    PJust x -> x

{- | Yields true if the given 'PMaybe' value is of form @'PJust' _@.

    @since 1.1.0
-}
pisJust ::
    forall (a :: S -> Type) (s :: S).
    Term s (PMaybe a :--> PBool)
pisJust = phoistAcyclic $
    plam $ \v' ->
        pmatch v' $ \case
            PJust _ -> pconstant True
            _ -> pconstant False

{- | Extract a 'PMaybe' by providing a default value in case of 'PJust'.

    @since 1.1.0
-}
pmaybe ::
    forall (a :: S -> Type) (s :: S).
    Term s (a :--> PMaybe a :--> a)
pmaybe = phoistAcyclic $
    plam $ \e a -> pmatch a $ \case
        PJust a' -> a'
        PNothing -> e

--------------------------------------------------------------------------------
-- Utility functions for working with 'PMaybeData'.

{- | Extracts the element out of a 'PDJust' and throws an error if its argument is 'PDNothing'.

    @since 1.1.0
-}
pfromDJust ::
    forall (a :: S -> Type) (s :: S).
    (PIsData a) =>
    Term s (PMaybeData a :--> a)
pfromDJust = phoistAcyclic $
    plam $ \t -> pmatch t $ \case
        PDNothing _ -> ptraceError "pfromDJust: found PDNothing"
        PDJust x -> pfromData $ pfield @"_0" # x

{- | Yield True if a given 'PMaybeData' is of form @'PDJust' _@.

    @since 1.1.0
-}
pisDJust ::
    forall (a :: S -> Type) (s :: S).
    Term s (PMaybeData a :--> PBool)
pisDJust = phoistAcyclic $
    plam $ \x -> pmatch x $ \case
        PDJust _ -> pconstant True
        _ -> pconstant False

--------------------------------------------------------------------------------
-- Conversion between 'PMaybe' and 'PMaybeData'.

{- | Copnsturct a 'PMaybeData' given a 'PMaybe'. Could be useful if you want to "lift" from 'PMaybe' to 'Maybe'.

    @since 1.1.0
-}
pmaybeToMaybeData ::
    forall (a :: S -> Type) (s :: S).
    (PIsData a) =>
    Term s (PMaybe a :--> PMaybeData a)
pmaybeToMaybeData = phoistAcyclic $
    plam $ \t -> pmatch t $ \case
        PNothing -> pcon $ PDNothing pdnil
        PJust x -> pcon $ PDJust $ pdcons @"_0" # pdata x # pdnil

{- | Escape with a particular value on expecting 'Just'. For use in monadic context.

    @since 1.1.0
-}
pexpectJustC ::
    forall (a :: S -> Type) (r :: S -> Type) (s :: S).
    Term s r ->
    Term s (PMaybe a) ->
    TermCont @r s (Term s a)
pexpectJustC escape ma = tcont $ \f ->
    pmatch ma $ \case
        PJust v -> f v
        PNothing -> escape
