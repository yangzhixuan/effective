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
  ( module Control.Effect.Nondet.Type
  , module Control.Effect.Nondet.Logic
  , Empty, Choose
  , LogicT (..)
  ) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative
import Control.Effect.Nondet.Type
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

list :: Handler [Empty, Choose] '[] '[LogicT] a [a]
list = alternative observeAllT

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`LogicT` monad transformer, which collects all possible results.
nondet :: Handler [Empty, NondetOr] '[] '[LogicT] a [a]
nondet = handler' observeAllT (emptyAlg :#. nondetOrAlg)

nondet' :: Handler [Empty, Choose, NondetOr] '[] '[LogicT] a [a]
nondet' = handler' observeAllT (emptyAlg :# chooseAlg :#. nondetOrAlg)

backtrack :: Handler [Empty, Choose, NondetOr, Once] '[] '[LogicT] a [a]
backtrack = handler' observeAllT (emptyAlg :# chooseAlg :# nondetOrAlg :#. onceAlg)

-- | `backtrack'` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`LogicT` monad transformer,
-- supporting backtracking.
backtrack' :: Handler [Empty, NondetOr, Once] '[] '[LogicT] a [a]
backtrack' = handler' observeAllT (emptyAlg :# nondetOrAlg :#. onceAlg)

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
nondetAT :: AlgTrans '[Empty, NondetOr] '[] '[LogicT] Monad
nondetAT = algTrans' (emptyAlg :#. nondetOrAlg)

-- Handlers for lightweight staging

nondetC :: HandlerC [Empty, NondetOr] '[] '[LogicT] a [a]
nondetC = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] $:# [|| NT nondetOrAlg ||] $:# EndAC)

listC :: HandlerC [Empty, Choose] '[] '[LogicT] a [a]
listC = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] $:# [|| NT $ \(Choose a b) -> (a <|> b) ||] $:# EndAC)
