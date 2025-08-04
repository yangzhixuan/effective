{-|
Module      : Control.Effect.Nondet.Logic
Description : Effects for nondeterministic computations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects and handlers for nondeterministic computations,
including choice and failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet.Logic
  ( Choose, Choose_(Choose)
  , Empty , Empty_(Empty)  , empty
  , Once  , Once_ (..)     , once
  , list
  , nondet
  , backtrackAlg
  , backtrackOnceAlg
  , backtrackAlg'
  , backtrack
  ) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative

import Control.Effect.Nondet.Type

import Control.Monad.Logic hiding (once)

list :: Handler [Empty, Choose] '[] '[LogicT] '[[]]
list = alternative observeAllT

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`LogicT` monad transformer, which collects all possible results.
{-# INLINE nondet #-}
nondet :: Handler [Empty, Nondet] '[] '[LogicT] '[[]]
nondet = handler' observeAllT nondetAlg

-- | `nondetAlg` defines the semantics of backtracking for the t`Empty`,
-- t`Choose`, effects in the context of the t`LogicT` monad transformer.
nondetAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Empty, Nondet] (LogicT m) x -> LogicT m x)
nondetAlg oalg op
  | Just (Alg Empty)            <- prj op = empty
  | Just (Alg (Choose xs ys))   <- prj op = pure xs <|> pure ys

-- | `backtrackAlg` defines the semantics of backtracking for the t`Empty`,
-- t`Choose`, and t`Once` effects in the context of the t`LogicT` monad transformer.
backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Empty, Nondet, Once] (LogicT m) x -> LogicT m x)
backtrackAlg oalg op
  | Just (Alg Empty)            <- prj op = empty
  | Just (Alg (Choose xs ys))   <- prj op = pure xs <|> pure ys
  | Just (Scp (Once p))         <- prj op =
      LogicT (\cons nil -> runLogicT p cons nil)

--    LogicT $ do mx <- runLogicT p
--                case mx of
--                  Nothing       -> return Nothing
--                  Just (x, mxs) -> return (Just (x, empty))

-- | `backtrackOnceAlg` defines the semantics of backtracking for the t`Once`
-- effect in the context of the t`ListT` monad transformer.
backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (LogicT m) x -> LogicT m x)
backtrackOnceAlg oalg op
  | Just (Scp (Once p))         <- prj op =
      LogicT (\cons nil -> runLogicT p cons nil)

-- | `backtrackAlg'` combines the semantics of alternative and backtracking
-- for the t`Empty`, t`Choose`, and t`Once` effects.
backtrackAlg'
  :: Monad m => (forall x. Effs '[] m x -> m x)
  -> (forall x. Effs [Empty, Choose, Once] (LogicT m) x -> LogicT m x)
backtrackAlg' oalg = (getAT alternativeAT oalg) # backtrackOnceAlg oalg

-- | `backtrack` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrack :: Handler [Empty, Choose, Once] '[] '[LogicT] '[[]]
backtrack = handler' observeAllT backtrackAlg'