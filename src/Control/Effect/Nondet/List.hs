{-|
Module      : Control.Effect.Nondet.List
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

module Control.Effect.Nondet.List
  ( module Control.Effect.Nondet.Type
  , module Control.Effect.Nondet.List
  , Choose
  , Empty
  , ListT (..)
  ) where

import Prelude hiding (or)

import Control.Effect.Nondet.Type
import Control.Effect
import Control.Effect.Alternative
import Control.Monad.Trans.List

{-# INLINE emptyAlg #-}
emptyAlg :: forall m a. Monad m => Empty (ListT m) a -> ListT m a
emptyAlg Empty = empty

{-# INLINE chooseAlg #-}
chooseAlg :: Monad m => Choose (ListT m) a -> ListT m a
chooseAlg (Choose xs ys) = xs <|> ys

{-# INLINE nondetOrAlg #-}
nondetOrAlg :: forall m a. Monad m => NondetOr (ListT m) a -> ListT m a
nondetOrAlg (NondetOr xs ys) = pure xs <|> pure ys

{-# INLINE onceAlg #-}
onceAlg :: Monad m => Once (ListT m) a -> ListT m a
onceAlg (Once xs) = ListT $ do
  mx <- runListT xs
  case mx of Nothing       -> return Nothing
             Just (x, mxs) -> return (Just (x, empty))

list :: Handler [Empty, Choose] '[] '[ListT] a [a]
list = alternative runListT'

-- | The `nondet` handler transforms nondeterminism effects t`Empty` and t`Choose`
-- into the t`ListT` monad transformer, which collects all possible results.
nondet :: Handler [Empty, NondetOr] '[] '[ListT] a [a]
nondet = handler' runListT' (emptyAlg :#. nondetOrAlg)

nondet' :: Handler [Empty, Choose, NondetOr] '[] '[ListT] a [a]
nondet' = handler' runListT' (emptyAlg :# chooseAlg :#. nondetOrAlg)

backtrack :: Handler [Empty, Choose, NondetOr, Once] '[] '[ListT] a [a]
backtrack = handler' runListT' (emptyAlg :# chooseAlg :# nondetOrAlg :#. onceAlg)

-- | `backtrack'` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrack' :: Handler [Empty, NondetOr, Once] '[] '[ListT] a [a]
backtrack' = handler' runListT' (emptyAlg :# nondetOrAlg :#. onceAlg)

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying `Alternative` instance for @t m@ given by a transformer @t@.
nondetAT :: AlgTrans '[Empty, NondetOr] '[] '[ListT] Monad
nondetAT = algTrans' (emptyAlg :#. nondetOrAlg)

-- Handlers for lightweight staging

nondetC :: HandlerC [Empty, NondetOr] '[] '[ListT] a [a]
nondetC = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] :#$ [|| NT nondetOrAlg ||] :#$ EndAC)

listC :: HandlerC [Empty, Choose] '[] '[ListT] a [a]
listC = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] :#$ [|| NT $ \(Choose a b) -> (a <|> b) ||] :#$ EndAC)