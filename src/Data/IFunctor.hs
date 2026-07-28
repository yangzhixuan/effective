{-|
Module      : Data.IFunctor
Description : Higher-order functors
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module contains the `IFunctor` class, which descibes higher-order functors.
-}

{-# LANGUAGE QuantifiedConstraints #-}

module Data.IFunctor where

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.State.Lazy as Lazy

import Data.Kind ( Type )

-- | A type @h@ is a higher-order functor if it provides a function `imap` which,
-- given any functors @f@ and @g@ lets you apply a natural transformation
-- @forall x . f x -> g x@ between them. Given any functor @f@, the type @h f@ must
-- also be a functor, and `imap` must adhere to the following laws:
--
-- [Identity]     @`imap` id = id@
-- [Composition]  @`imap` (h . k) = `imap` h . `imap` k@
--
class IFunctor (h :: (i -> (k -> Type)) -> (j -> (k -> Type))) where
  imap :: (forall i x . f i x -> g i x) -> (forall j . h f j a -> h g j a)

instance IFunctor IdentityT where
  imap h (IdentityT x) = IdentityT (h x)

instance (IFunctor h, IFunctor k) =>
  IFunctor (ComposeT h k) where
    {-# INLINE imap #-}
    imap
      :: ( IFunctor h, IFunctor k, Functor f, Functor g )
      => (forall x. f x -> g x)
      -> ComposeT h k f a
      -> ComposeT h k g a
    imap h (ComposeT x) = ComposeT (imap (imap h) x)

instance IFunctor MaybeT where
  imap h (MaybeT mx) = MaybeT (h mx)

instance IFunctor (ExceptT e) where
  imap h (ExceptT mx) = ExceptT (h mx)

instance IFunctor (ReaderT s) where
  imap h (ReaderT mx) = ReaderT (\r -> h (mx r))

instance IFunctor (WriterT w) where
  imap h (WriterT mx) = WriterT (h mx)

instance IFunctor (Strict.StateT s) where
  imap h (Strict.StateT p) = Strict.StateT (\s -> h (p s))

instance IFunctor (Lazy.StateT s) where
  imap h (Lazy.StateT p) = Lazy.StateT (\s -> h (p s))
