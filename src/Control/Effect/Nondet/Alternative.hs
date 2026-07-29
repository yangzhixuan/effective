{-|
Module      : Control.Effect.Alternative
Description : Effects for alternatives with choose and empty
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides operations corresponding to the `Alternative` typeclass of
Haskell. Two operations t`Empty` and t`Choose` are defined, corresponding to
`Ap.empty` and `Ap.<|>` of `Alternative` respectively. The monad `Prog effs`
also instantiate `Alternative`.

In this library there is another module "Control.Effect.Nondet" that provides
some additional operations for nondeterminism. See the documentation in
"Control.Effect.Nondet" for more explanation.
-}

{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.Nondet.Alternative (
  -- * Syntax
  -- ** Operations

  -- | The operations for alternatives use 'empty' and '<|>' directly
  -- from the 'Control.Applicative.Alternative' type class.
  --
  -- 'empty' is an algebraic operation:
  --
  -- > empty >>= k = empty
  --
  -- '<|>' is a scoped operation.
  Ap.empty, emptyP, emptyM,
  (<|>), chooseP, chooseM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  emptyN, chooseN,
#endif
  select, selects,

  -- ** Signatures
  Empty, Empty_(..), pattern Empty,
  Choose, Choose_(..), pattern Choose,

  -- * Semantics
  -- ** Handlers
  alternative,
  list, listC,
  logic, logicC,

  -- ** Algebras
  alternativeAT,

  -- ** Re-exported carriers
  Li.ListT (..),
  Lo.LogicT (..)
) where

import Control.Effect hiding (emptyAlg)
import Control.Effect.Nondet.Type
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Applicative ((<|>), Alternative)
import Control.Applicative qualified as Ap

import qualified Control.Monad.Logic as Lo
import qualified Control.Monad.Trans.List as Li

-- | The 'alternative' handler makes use of an 'Alternative' functor @f@
-- as well as a transformer @t@ that produces an 'Alternative' functor @t m@.
-- for any monad @m@ to provide semantics.
{-# INLINE alternative #-}
alternative
  :: forall t f a.
     (forall m. Monad m => Alternative (t m))
  => (forall m. Monad m => (forall a. t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] '[t] a (f a)
alternative run = Handler (runner' run) alternativeAT

-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
alternativeAT
  :: forall t.
     (forall m. Monad m => Alternative (t m))
  => AlgTrans '[Empty, Choose] '[] '[t] Monad
alternativeAT = algTrans' (emptyAlg :#. chooseAlg)

{-# INLINE emptyAlg #-}
emptyAlg :: Alternative (t m) => Empty (t m) x -> t m x
emptyAlg Empty = Ap.empty

{-# INLINE chooseAlg #-}
chooseAlg :: Alternative (t m) => Choose (t m) x -> t m x
chooseAlg (Choose xs ys) = xs <|> ys

-- | A specialisation of `alternative` to @ListT@
list :: Handler [Empty, Choose] '[] '[Li.ListT] a [a]
list = alternative Li.runListT'

-- | A specialisation of `alternative` to @LogicT@.
logic :: Handler [Empty, Choose] '[] '[Lo.LogicT] a [a]
logic = alternative Lo.observeAllT

-- | Staged version of `list`
listC :: HandlerC [Empty, Choose] '[] '[Li.ListT] a [a]
listC = HandlerC
  (RunnerC $ \_ -> [|| Li.runListT' ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] :#$ [|| NT chooseAlg ||] :#$ emptyAlgC)

-- | Staged version of `logic`
logicC :: HandlerC [Empty, Choose] '[] '[Lo.LogicT] a [a]
logicC = HandlerC
  (RunnerC $ \_ -> [|| Lo.observeAllT ||])
  (AlgTransC $ \_ -> [|| NT emptyAlg ||] :#$ [|| NT $ \(Choose a b) -> (a <|> b) ||] :#$ emptyAlgC)