{-|
Module      : Control.Effect.IO
Description : Effects for input/output
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}

module Control.Effect.IO (
  -- * Syntax
  -- ** Operations
  Alg (..),
  IO,
  io,

  -- * Semantics
  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',

  -- * Algebras
  ioAlg,
)
  where

import Control.Effect
import Control.Effect.Internal.Handler
import Control.Effect.Family.Algebraic
import Data.List.Kind
import Data.HFunctor

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra '[Alg IO] IO
ioAlg = nativeAlg

-- | Treating an IO computation as an operation of signature `Alg IO`.
io :: Members '[Alg IO] sig => IO a -> Prog sig a
io op = call (Alg op)

-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog '[Alg IO] a -> IO a
evalIO = eval ioAlg

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. The handler is
-- allowed to emit the operation @Alg IO@ and the program can used @Alg IO@ too.
handleIO
  :: forall sigs osigs ts a b
  . ( Monad (Apply ts IO)
    , ForwardsM '[Alg IO] ts
    , Injects osigs '[Alg IO]
    , HandleM# sigs '[Alg IO] )
  => Handler sigs osigs ts a b
  -> Prog (sigs `Union` '[Alg IO]) a -> IO b
handleIO = handleM @sigs ioAlg

type HandleIO# sigs osigs sigs1 =
  ( Injects (sigs1 :\\ sigs) sigs1
  , Append sigs (sigs1 :\\ sigs)
  , HFunctor (Effs (sigs `Union` sigs1)))

-- | @`handleIO'` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects that are a subset of the IO effects and additionally
-- the program may also use a subset @sigs1@ of the IO effects (which must
-- be forwardable through the monad transformer @ts@).
-- The type argument @sigs1@ usually can't be inferred and needs given
-- explicitly.
-- This function is useful when you want to use some non-algebraic operations
-- that come with the IO-monad. Otherwise `handleIO` should be used.
handleIO'
  :: forall sigs1 iosig sigs osigs ts a b
  . ( Injects osigs iosig
    , ForwardsM sigs1 ts
    , Monad (Apply ts IO)
    , Injects sigs1 iosig
    , HandleIO# sigs osigs sigs1 )
  => Proxy sigs1
  -> Algebra iosig IO
  -> Handler sigs osigs ts a b
  -> Prog (sigs `Union` sigs1) a -> IO b
handleIO' p ioAlg h = handleMFwds p ioAlg h