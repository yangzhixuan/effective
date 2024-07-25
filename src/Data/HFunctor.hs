{-# LANGUAGE QuantifiedConstraints #-}

module Data.HFunctor where

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.State.Lazy as Lazy

import Data.Kind ( Type )

instance HFunctor IdentityT where
  hmap h (IdentityT x) = IdentityT (h x)

instance (HFunctor h, HFunctor k) =>
  HFunctor (ComposeT h k) where
    {-# INLINE hmap #-}
    hmap :: (HFunctor h, HFunctor k, Functor f, Functor g) =>
      (forall x. f x -> g x) -> ComposeT h k f a -> ComposeT h k g a
    hmap h (ComposeT x) = ComposeT (hmap (hmap h) x)

class (forall f . Functor f => Functor (h f)) => HFunctor (h :: (Type -> Type) -> (Type -> Type)) where
  hmap :: (Functor f, Functor g) => (forall x . f x -> g x) -> (h f) a -> (h g) a

instance HFunctor MaybeT where
  hmap h (MaybeT mx) = MaybeT (h mx)

instance HFunctor (ExceptT e) where
  hmap h (ExceptT mx) = ExceptT (h mx)

instance HFunctor (ReaderT s) where
  hmap h (ReaderT mx) = ReaderT (\r -> h (mx r))

instance HFunctor (WriterT w) where
  hmap h (WriterT mx) = WriterT (h mx)

instance HFunctor (Strict.StateT s) where
  hmap h (Strict.StateT p) = Strict.StateT (\s -> h (p s))

instance HFunctor (Lazy.StateT s) where
  hmap h (Lazy.StateT p) = Lazy.StateT (\s -> h (p s))
