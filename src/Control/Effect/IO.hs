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
  -- ** Handlers
  constIO,

  -- ** Carriers
  ConstIO (..),

  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',

  -- * Algebras
  ioAlg, ioAlgC
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

ioAlgC :: AlgebraC '[Alg IO] IO
ioAlgC = nativeAlgC

-- | Treating an IO computation as an operation of signature `Alg IO`.
io :: IO a -> a ! '[Alg IO]
io op = call (Alg op)

-- | A carrier that stores an `IO` action and ignores the lower monad.
--
-- This is useful as the final carrier in a handler stack when all remaining
-- operations have been translated to `Alg IO`. It is not a monad transformer:
-- there is no general way to lift an arbitrary lower-monad action into `IO`.
newtype ConstIO m a = ConstIO { runConstIO :: IO a }

instance Functor (ConstIO m) where
  {-# INLINE fmap #-}
  fmap f (ConstIO iox) = ConstIO (fmap f iox)

instance Applicative (ConstIO m) where
  {-# INLINE pure #-}
  pure = ConstIO . pure

  {-# INLINE (<*>) #-}
  ConstIO iof <*> ConstIO iox = ConstIO (iof <*> iox)

instance Monad (ConstIO m) where
  {-# INLINE (>>=) #-}
  ConstIO iox >>= f = ConstIO (iox >>= runConstIO . f)

-- | Collect `Alg IO` operations into a final `IO` action.
--
-- This handler is intended to be used as the final handler of a stack, for example
-- @handle (h |> constIO) p@. Any effects handled after this handler are ignored.
constIO :: Handler '[Alg IO] '[] '[ConstIO] a (IO a)
constIO = Handler run alg
  where
    run :: Runner '[] '[ConstIO] a (IO a) Monad
    run = Runner (\_ -> pure . runConstIO)

    alg :: AlgTrans '[Alg IO] '[] '[ConstIO] Monad
    alg = algTrans1 (\_ (Alg iox) -> ConstIO iox)

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

type HandleIO# effs oeffs xeffs =
  ( Injects (xeffs :\\ effs) xeffs )

-- | @`handleIO'` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects that are a subset of the IO effects and additionally
-- the program may also use a subset @xsigs@ of the IO effects (which must
-- be forwardable through the monad transformer @ts@).
-- The type argument @xsigs@ usually can't be inferred and needs to be given
-- explicitly.
-- This function is useful when you want to use some non-algebraic operations
-- that come with the IO-monad. Otherwise `handleIO` should be used.
handleIO'
  :: forall xsigs iosig sigs osigs ts a b
  . ( Injects osigs iosig
    , ForwardsM xsigs ts
    , Monad (Apply ts IO)
    , Injects xsigs iosig
    , HandleIO# sigs osigs xsigs )
  => Proxy xsigs
  -> Algebra iosig IO
  -> Handler sigs osigs ts a b
  -> Prog (sigs `Union` xsigs) a -> IO b
handleIO' p ioAlg h = handleMFwds p ioAlg h
