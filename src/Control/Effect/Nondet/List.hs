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
  , Choose
  , Empty
  , nondet, nondetAT
  , nondet'
  , nondetC
  , list, listC
  , backtrack
  , backtrack'
  ) where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative

import Control.Effect.Nondet.Type
import Control.Monad.Trans.List

list :: Handler [Empty, Choose] '[] '[ListT] a [a]
list = alternative runListT'

list' :: Handler [Search, Empty, Choose] '[] '[ListT] a [a]
list' = searchListAlg <: list

searchListAlg :: AlgTrans '[Search] '[] '[ListT] Monad
searchListAlg = algTrans1 $ \oalg (Scp (Search_ xs)) -> xs

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`ListT` monad transformer, which collects all possible results.
{-# INLINE nondet #-}
nondet :: Handler [Empty, NondetOr] '[] '[ListT] a [a]
nondet = handler' runListT' nondetAlg

{-# INLINE nondet' #-}
nondet' :: Handler [Empty, Choose, NondetOr] '[] '[ListT] a [a]
nondet' = handler' runListT' (alternativeAlg # (nondetOrAlg #: hnil))

{-# INLINE nondetAlg #-}
nondetAlg
  :: forall m. Monad m
  => Algebra [Empty, NondetOr] (ListT m)
nondetAlg = emptyAlg #: nondetOrAlg #: hnil

{-# INLINE emptyAlg #-}
emptyAlg :: forall m a. Monad m => Empty (ListT m) a -> ListT m a
emptyAlg Empty' = empty

{-# INLINE nondetOrAlg #-}
nondetOrAlg :: forall m a. Monad m => NondetOr (ListT m) a -> ListT m a
nondetOrAlg (NondetOr' xs ys) = pure xs <|> pure ys

backtrack :: Handler [Empty, Choose, NondetOr, Once] '[] '[ListT] a [a]
backtrack = handler' runListT' (alternativeAlg # (nondetOrAlg #: onceAlg #: hnil))

onceAlg :: Monad m => Once (ListT m) a -> ListT m a
onceAlg (Once' xs) = ListT $ do
  mx <- runListT xs
  case mx of Nothing       -> return Nothing
             Just (x, mxs) -> return (Just (x, empty))


-- | `backtrack'` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrack' :: Handler [Empty, NondetOr, Once] '[] '[ListT] a [a]
backtrack' = handler' runListT' (emptyAlg #: nondetOrAlg #: onceAlg #: hnil)

-- | `backtrackOnce` is a handler that transforms nondeterministic effect
-- t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrackOnce :: Handler '[Once] '[] '[ListT] a [a]
backtrackOnce = handler' runListT' (onceAlg #: hnil)

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
nondetAT
  :: AlgTrans '[Empty, NondetOr] '[] '[ListT] Monad
nondetAT = algTrans' nondetAlg

-- Handlers for lightweight staging

nondetC :: HandlerC [Empty, NondetOr] '[] '[ListT] a [a]
nondetC = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] #:$ [|| NT nondetOrAlg ||] #:$ EndAC)

listC :: HandlerC [Empty, Choose] '[] '[ListT] a [a]
listC = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] #:$ [|| NT $ \(Choose' a b) -> (a <|> b) ||] #:$ EndAC)
