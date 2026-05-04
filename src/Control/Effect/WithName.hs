{-|
Module      : Control.Effect.WithName
Description : Making copies of existing effects with names
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides an \'imitater\' effect that clones an existing effect.
The effect @WithName name sig@ is simply a newtype wrapper of @sig@, so the
existing handlers of @sig@ can be transported to be handlers of @WithName name sig@.
A typical use case of this effect is for having multiple instances of mutable state.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving, QuantifiedConstraints, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
{-# LANGUAGE RequiredTypeArguments #-}
#endif

module Control.Effect.WithName (
  -- * Syntax
  WithName (..),
  (:@),
  Rename,
  RenameAll,

  -- * Semantics
  renameEff, renameEffAT,
  renameOEff, renameOEffAT,
  renameEffs, renameEffsAT,
  renameOEffs, renameOEffsAT,
  renameIOEffs, renameIOEffsAT,
  callP, callPAlg, callPScp,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  callN, callNAlg, callNScp,
#endif
) where

import Control.Effect.Internal.Effs
import Control.Effect.Internal.Forward
import Control.Effect.Internal.Handler
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Prog
import Data.Proxy
import Data.List.Kind
import Data.HFunctor
import Unsafe.Coerce
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Data.Kind (Type)
import GHC.Base (Symbol)

import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.Runner

-- | Make a copy of an effect signature and attach a name to it.
-- This is useful when more than one instances of the same effect
-- are needed in a program.
newtype WithName
  (name :: Symbol)
  (sig  :: Effect)
  (f    :: Type -> Type)
  (k    :: Type)
  = WithName { unWithName :: sig f k } deriving (Functor, HFunctor)

-- A binary operator for @WithName@
type (:@) :: Symbol -> Effect -> Effect
type name :@ sig = WithName name sig

instance Forward sig t => Forward (WithName name sig) t where
  type FwdConstraint (WithName name sig) t = FwdConstraint sig t
  fwd alg (WithName op) = fwd (alg . WithName) op

-- | @Rename name sig sigs@ replaces (the first occurrence of) @sig@ in @sigs@ with @WithName name sig@.
type family Rename (name :: Symbol) (sig :: Effect) (sigs :: [Effect]) :: [Effect] where
  Rename name sig '[]            = '[]
  Rename name sig (sig : sigs')  = WithName name sig : sigs'
  Rename name sig (sig' : sigs') = sig' : Rename name sig sigs'

-- | @RenameAll name sigs@ tags every effect in @sigs@ with the name @name@.
type family RenameAll (name :: Symbol) (sigs :: [Effect]) :: [Effect] where
  RenameAll name '[] = '[]
  RenameAll name (sig : sigs') = WithName name sig : RenameAll name sigs'

-- | Rename a single member in the input effects.
--
-- The implementation is based on unsafe coercision but it is actually safe because
-- @Effs sigs f x@ and @Effs (Rename name sig sigs) f x@ will always have the exactly
-- the same representation, although GHC doesn't see this.
renameEff :: Proxy name -> Proxy sig -> Handler sigs osigs ts a b
          -> Handler (Rename name sig sigs) osigs ts a b
renameEff p q = unsafeCoerce

-- | Rename all input effects.
renameEffs :: Proxy name -> Handler sigs osigs ts a b
           -> Handler (RenameAll name sigs) osigs ts a b
renameEffs p = unsafeCoerce

-- | Rename a single member in the output effects.
renameOEff :: Proxy name -> Proxy sig -> Handler sigs osigs ts a b
           -> Handler sigs (Rename name sig osigs) ts a b
renameOEff p q = unsafeCoerce

-- | Rename all output effects.
renameOEffs :: Proxy name -> Handler sigs osigs ts a b
            -> Handler sigs (RenameAll name osigs) ts a b
renameOEffs p = unsafeCoerce

-- | Rename all input and output effects.
renameIOEffs :: Proxy name -> Handler sigs osigs ts a b
             -> Handler (RenameAll name sigs) (RenameAll name osigs) ts a b
renameIOEffs p = unsafeCoerce

renameEffAT :: Proxy name -> Proxy sig -> AlgTrans sigs osigs ts cs
            -> AlgTrans (Rename name sig sigs) osigs ts cs
renameEffAT p q = unsafeCoerce

-- | Rename all input effects.
renameEffsAT :: Proxy name -> AlgTrans sigs osigs ts cs
           -> AlgTrans (RenameAll name sigs) osigs ts cs
renameEffsAT p = unsafeCoerce

-- | Rename a single member in the output effects.
renameOEffAT :: Proxy name -> Proxy sig -> AlgTrans sigs osigs ts cs
           -> AlgTrans sigs (Rename name sig osigs) ts cs
renameOEffAT p q = unsafeCoerce

-- | Rename all output effects.
renameOEffsAT :: Proxy name -> AlgTrans sigs osigs ts cs
            -> AlgTrans sigs (RenameAll name osigs) ts cs
renameOEffsAT p = unsafeCoerce

-- | Rename all input and output effects.
renameIOEffsAT :: Proxy name -> AlgTrans sigs osigs ts cs
             -> AlgTrans (RenameAll name sigs) (RenameAll name osigs) ts cs
renameIOEffsAT p = unsafeCoerce

-- Call an operation with a given name. The name is given by a @Proxy@ argument.
callP :: forall name sig sigs a . (HFunctor sig, Member (WithName name sig) sigs)
      => Proxy name -> sig (Prog sigs) a -> Prog sigs a
callP _ x = call (WithName @name x)

-- | Special case of `callP` for algebraic operations
callPAlg :: forall name f sigs a.(Member (WithName name (Alg f)) sigs, Functor f)
         => Proxy name -> f a -> Prog sigs a
callPAlg p f = callP p (Alg f)

-- | Special case of `callP` for scoped operations
callPScp :: forall name f sigs a. (Member (WithName name (Scp f)) sigs, Functor f)
         => Proxy name -> f (Prog sigs a) -> Prog sigs a
callPScp p f = callP p (Scp f)

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
-- Call an operation with a given name. The name is given by a required type argument.
callN :: forall name -> forall sig sigs a . (HFunctor sig, Member (WithName name sig) sigs)
      => sig (Prog sigs) a -> Prog sigs a
callN n x = call (WithName @n x)

-- | Special case of `callN` for algebraic operations
callNAlg :: forall name -> forall f sigs a. (Member (WithName name (Alg f)) sigs, Functor f)
         => f a -> Prog sigs a
callNAlg n f = callN n (Alg f)

-- | Special case of `callN` for scoped operations
callNScp :: forall name -> forall f sigs a. (Member (WithName name (Scp f)) sigs, Functor f)
         => f (Prog sigs a) -> Prog sigs a
callNScp n f = callN n (Scp f)
#endif