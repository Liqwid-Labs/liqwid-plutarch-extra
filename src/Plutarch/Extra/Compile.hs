{-# LANGUAGE RankNTypes #-}

module Plutarch.Extra.Compile (mustCompileNoTracing) where

import qualified Data.Text as T
import Plutarch (
    Config (Config, tracingMode),
    TracingMode (NoTracing),
    compile,
 )
import PlutusLedgerApi.V2 (Script)

{- | Compile a ClosedTerm, throwing an error if unsuccessful.

     Uses `NoTracing` configuration.

     @since 2.0.0
-}
mustCompileNoTracing :: forall (a :: S -> Type). ClosedTerm a -> Script
mustCompileNoTracing t = case compile conf t of
    Left err -> error $ unwords ["Plutarch compilation error:", T.unpack err]
    Right s -> s
  where
    conf = Config{tracingMode = NoTracing}
