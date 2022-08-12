{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-all #-}

module Plutarch.Extra.Evaluated (
    EvaluatedTerm(..),
    (!#),
    (!#$),
    (##),
    (##$),
    pelift,
    peconstant,
) where

import Data.Text (Text)
import Plutarch.Lift
import Plutarch.Prelude
import Plutarch.Internal
import Plutarch.Evaluate
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
import Data.Default (def)
import Data.Type.Bool

data EvaluatedTerm (evaluated :: Bool) (p :: S -> Type)
    = EvaluatedTerm (forall s. Term s p)

evaluateTerm' ::
    Config ->
    EvaluatedTerm e p ->
    Either Text (Either EvalError (EvaluatedTerm 'True p), ExBudget, [Text])
evaluateTerm' config (EvaluatedTerm t) =
    go <$> evalTerm config t
    where
      go :: (Either EvalError (ClosedTerm p),a, b) ->
            (Either EvalError (EvaluatedTerm 'True p),a,b)
      go (x, y, z) = (EvaluatedTerm <$> x, y, z)
    
evaluateTerm :: EvaluatedTerm e p -> EvaluatedTerm 'True p
evaluateTerm (EvaluatedTerm t) =
    case evalTerm def t of
        Left err -> error $ show err
        Right (Right x, _, _) -> EvaluatedTerm x
        Right (Left err, _, _) -> error $ show err

eapp ::
    forall (e :: Bool) (f :: Bool) (p :: S -> Type) (q :: S -> Type).
    EvaluatedTerm e (p :--> q) ->
    EvaluatedTerm f p ->
    EvaluatedTerm 'False q
eapp (EvaluatedTerm f) (EvaluatedTerm x) = EvaluatedTerm $ f # x

eapp' ::
    forall (e :: Bool) (p :: S -> Type) (q :: S -> Type).
    ClosedTerm (p :--> q) ->
    EvaluatedTerm e p ->
    EvaluatedTerm 'False q
eapp' f (EvaluatedTerm x) = EvaluatedTerm $ f # x

(!#) ::
    forall (e :: Bool) (f :: Bool) (p :: S -> Type) (q :: S -> Type).    
    EvaluatedTerm e (p :--> q) ->
    EvaluatedTerm f p ->
    EvaluatedTerm 'False q
(!#) = eapp

infixl 8 !#

(!#$) ::
    forall (e :: Bool) (f :: Bool) (p :: S -> Type) (q :: S -> Type).    
    EvaluatedTerm e (p :--> q) ->
    EvaluatedTerm f p ->
    EvaluatedTerm 'False q
(!#$) = eapp

infixr 0 !#$

(##) ::
    forall (e :: Bool) (f :: Bool) (p :: S -> Type) (q :: S -> Type).    
    ClosedTerm (p :--> q) ->
    EvaluatedTerm f p ->
    EvaluatedTerm 'False q
(##) = eapp'

infixl 8 ##

(##$) ::
    forall (e :: Bool) (f :: Bool) (p :: S -> Type) (q :: S -> Type).    
    ClosedTerm (p :--> q) ->
    EvaluatedTerm f p ->
    EvaluatedTerm 'False q
(##$) = eapp'

infixr 0 ##$    

pelift ::
    forall (e :: Bool) (p :: S -> Type).
    PLift p =>
    EvaluatedTerm e p ->
    PLifted p
pelift (EvaluatedTerm x) = plift x

peconstant ::
    forall (e :: Bool) (p :: S -> Type).    
    PLift p =>
    PLifted p ->
    EvaluatedTerm 'True p
peconstant x = EvaluatedTerm $ pconstant x    
