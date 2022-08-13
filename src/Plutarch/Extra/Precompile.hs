{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}

{- | Pre-compiling Plutarch functions and applying them.

 Speeds up benchmarking and testing.
-}
module Plutarch.Extra.Precompile (
    applyScript,
    -- Exporting the data constructor on purpose, since users might want to
    -- deserialize compiled terms.  If someone wants to subvert type safety using
    -- Scripts, they can do that regardless of this export.
    CompiledTerm (..),
    compile',
    toDebuggableScript,
    applyCompiledTerm,
    applyCompiledTerm',
    applyCompiledTerm2,
    applyCompiledTerm2',
    (##),
    (##~),
    (###),
    (###~),
    LiftError (..),
    pliftCompiled,
    toPTerm',
    toPTerm,
) where

import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Stack (HasCallStack)
import Plutarch.FFI (unsafeForeignImport)
import PlutusTx.Code (CompiledCodeIn (DeserializedCode))
import Plutarch.Evaluate (EvalError)
import Plutarch.Extra.DebuggableScript (
    DebuggableScript (DebuggableScript),
    debugScript,
    finalEvalDebuggableScript,
    mustCompileD,
    mustEvalD,
    script,
 )
import Plutarch.Lift (
    PUnsafeLiftDecl (PLifted),
    LiftError (..),
 )
import Plutarch.Prelude (S, Term, Type, (:-->), ClosedTerm, plift, PLift)
import PlutusLedgerApi.V1.Scripts (Script (Script))
import UntypedPlutusCore (Program (Program, _progAnn, _progTerm, _progVer))
import qualified UntypedPlutusCore.Core.Type as UplcType
import qualified UntypedPlutusCore as UPLC

-- | Apply a function to an argument on the compiled 'Script' level.
applyScript :: Script -> Script -> Script
applyScript f a =
    if fVer /= aVer
        then error "apply: Plutus Core version mismatch"
        else
            Script
                Program
                    { _progTerm = UplcType.Apply () fTerm aTerm
                    , _progVer = fVer
                    , _progAnn = ()
                    }
  where
    (Script Program{_progTerm = fTerm, _progVer = fVer}) = f
    (Script Program{_progTerm = aTerm, _progVer = aVer}) = a

applyDebuggableScript :: DebuggableScript -> DebuggableScript -> DebuggableScript
applyDebuggableScript f a =
    DebuggableScript
        { script = applyScript f.script a.script
        , debugScript = applyScript f.debugScript a.debugScript
        }

-- | Type-safe wrapper for compiled Plutarch functions.
newtype CompiledTerm (a :: S -> Type) = CompiledTerm DebuggableScript

{- | Compile a closed Plutarch 'Term' to a 'CompiledTerm'.

 Beware, the Script inside contains everything it needs. You can end up with
 multiple copies of the same helper function through compiled terms (including
 RHS terms compiled by '##' and '##~').
-}
compile' ::
    forall (a :: S -> Type).
    (forall (s :: S). Term s a) ->
    CompiledTerm a
compile' t = CompiledTerm $ mustCompileD t

-- | Convert a 'CompiledTerm' to a 'Script'.
toDebuggableScript :: forall (a :: S -> Type). CompiledTerm a -> DebuggableScript
toDebuggableScript (CompiledTerm dscript) = dscript

{- | Apply a 'CompiledTerm' to a closed Plutarch 'Term'.

 Evaluates the argument before applying. You want this for benchmarking the
 compiled function. Helps to avoid tainting the measurement by input
 conversions.
-}
applyCompiledTerm ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    (forall (s :: S). Term s a) ->
    CompiledTerm b
applyCompiledTerm (CompiledTerm sf) a =
    CompiledTerm $ applyDebuggableScript sf (mustEvalD $ mustCompileD a)

{- | Apply a 'CompiledTerm' to a closed Plutarch 'Term'.

 Does NOT evaluate the argument before applying. Using this seems to save very
 little overhead, not worth it for efficiency. Only use it to make argument
 evaluation count for benchmarking.
-}
applyCompiledTerm' ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    (forall (s :: S). Term s a) ->
    CompiledTerm b
applyCompiledTerm' (CompiledTerm sf) a =
    CompiledTerm $ applyDebuggableScript sf (mustCompileD a)

{- | Apply a 'CompiledTerm' to a 'CompiledTerm'.

 Evaluates the argument before applying. You want this for benchmarking the
 compiled function. Helps to avoid tainting the measurement by input
 conversions.
-}
applyCompiledTerm2 ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    CompiledTerm a ->
    CompiledTerm b
applyCompiledTerm2 (CompiledTerm sf) (CompiledTerm sa) =
    CompiledTerm $ applyDebuggableScript sf (mustEvalD sa)

{- | Apply a 'CompiledTerm' to a 'CompiledTerm'.

 Does NOT evaluate the argument before applying. Using this seems to save very
 little overhead, not worth it for efficiency. Only use it to make argument
 evaluation count for benchmarking.
-}
applyCompiledTerm2' ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    CompiledTerm a ->
    CompiledTerm b
applyCompiledTerm2' (CompiledTerm sf) (CompiledTerm sa) =
    CompiledTerm $ applyDebuggableScript sf sa

-- | Alias for 'applyCompiledTerm'.
(##) ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    (forall (s :: S). Term s a) ->
    CompiledTerm b
(##) = applyCompiledTerm

infixl 8 ##

-- | Alias for 'applyCompiledTerm\''.
(##~) ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    (forall (s :: S). Term s a) ->
    CompiledTerm b
(##~) = applyCompiledTerm'

infixl 8 ##~

-- | Alias for 'applyCompiledTerm2'.
(###) ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    CompiledTerm a ->
    CompiledTerm b
(###) = applyCompiledTerm2

infixl 7 ###

-- | Alias for 'applyCompiledTerm2\''.
(###~) ::
    forall (a :: S -> Type) (b :: S -> Type).
    CompiledTerm (a :--> b) ->
    CompiledTerm a ->
    CompiledTerm b
(###~) = applyCompiledTerm2'

infixl 7 ###~

--  Copied and adapted the stuff below from 'Plutarch.Lift'.
--  Also added trace messages in the exceptions.

toPTerm' ::
    forall (p :: S -> Type).
    CompiledTerm p ->
    (Either EvalError (ClosedTerm p), ExBudget, [Text])
toPTerm' prog =
    case finalEvalDebuggableScript . toDebuggableScript $ prog of
        (Right (Script (UPLC.Program _ version term)), b, t) -> 
            let program = UPLC.Program () version $ UPLC.termMapNames UPLC.fakeNameDeBruijn term
            in (Right $ unsafeForeignImport $ DeserializedCode program Nothing mempty, b, t)
        (Left e, b, t) -> (Left e, b, t)

toPTerm ::
    forall (p :: S -> Type).
    HasCallStack =>
    CompiledTerm p ->
    ClosedTerm p
toPTerm prog =
    case toPTerm' prog of
        (Right x, _, _) -> x
        (Left x, _, _) -> error $ show x

{- | Convert a 'CompiledTerm' to the associated Haskell value. Fail otherwise.

 This will fully evaluate the compiled term, and convert the resulting value.
-}
pliftCompiled ::
    forall (p :: S -> Type). PLift p => CompiledTerm p -> PLifted p
pliftCompiled prog = case toPTerm' prog of
    (Right term, _, _) -> plift term
    (Left e, _, logs) -> error $
            "plift failed: erring term: "
                <> Text.unpack (Text.unlines $ Text.pack (show e) : logs)
