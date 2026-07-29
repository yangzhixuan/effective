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
  ( module Control.Effect.Nondet.Operations
  , module Control.Effect.Nondet.Logic
  , LogicT (..)
  ) where

import Control.Effect hiding (emptyAlg)
import Control.Effect.Nondet.Alternative
import Control.Effect.Nondet.Operations
import Control.Monad.Logic hiding (once)
import qualified Control.Monad.Logic as L

{-# INLINE emptyAlg #-}
emptyAlg :: forall m a. Monad m => Empty (LogicT m) a -> LogicT m a
emptyAlg Empty = empty

{-# INLINE chooseAlg #-}
chooseAlg :: Monad m => Choose (LogicT m) a -> LogicT m a
chooseAlg (Choose xs ys) = xs <|> ys

{-# INLINE nondetOrAlg #-}
nondetOrAlg :: forall m a. Monad m => NondetOr (LogicT m) a -> LogicT m a
nondetOrAlg (NondetOr xs ys) = pure xs <|> pure ys

{-# INLINE onceAlg #-}
onceAlg :: Monad m => Once (LogicT m) a -> LogicT m a
onceAlg (Once p) = L.once p

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`LogicT` monad transformer, which collects all possible results.
nondet :: Handler [Empty, NondetOr] '[] '[LogicT] a [a]
nondet = handler' observeAllT (emptyAlg :#. nondetOrAlg)

-- | This handler additionally handles t`Once` and the scoped operation `Choose` (the
-- the `Alternative` instance on t`Prog` uses `Choose`).
backtrack :: Handler [Empty, Choose, NondetOr, Once] '[] '[LogicT] a [a]
backtrack = handler' observeAllT (emptyAlg :# chooseAlg :# nondetOrAlg :#. onceAlg)

-- | A variant of `nondet` that additionally handles t`Choose`.
nondet' :: Handler [Empty, Choose, NondetOr] '[] '[LogicT] a [a]
nondet' = handler' observeAllT (emptyAlg :# chooseAlg :#. nondetOrAlg)

-- | A variant of `backtrack` that does not handle t`Choose`.
-- supporting backtracking.
backtrack' :: Handler [Empty, NondetOr, Once] '[] '[LogicT] a [a]
backtrack' = handler' observeAllT (emptyAlg :# nondetOrAlg :#. onceAlg)

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying @Alternative@ instance for @t m@ given by a transformer @t@.
nondetAT :: AlgTrans '[Empty, NondetOr] '[] '[LogicT] Monad
nondetAT = algTrans' (emptyAlg :#. nondetOrAlg)

-- Handlers for lightweight staging

nondetC :: HandlerC [Empty, NondetOr] '[] '[LogicT] a [a]
nondetC = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] :#$ [|| NT nondetOrAlg ||] :#$ emptyAlgC)