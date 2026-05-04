{-|
Module      : Control.Effect.Internal.Effs.Type
Description : The union type for effect operations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal.Effs.Sum.Type
  ( Effs (..)
  , Algebra
  , Effect
  , absurdEffs
  ) where

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | A higher-order algebra for the union of effects @sigs@ with
-- carrier being the functor @f@.
type Algebra sigs f =
  forall x . Effs sigs f x -> f x

-- | @Effs sigs f a@ creates a union of the effect signatures in the list @sigs@.
type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Eff  :: !(sig f a) -> Effs (sig ': sigs) f a
  Effs :: !(Effs sigs f a) -> Effs (sig ': sigs) f a

instance Functor f => Functor (Effs '[] f) where
  {-# INLINE fmap #-}
  fmap f x = case x of {}

instance (Functor f, Functor (sig f), Functor (Effs sigs f)) => Functor (Effs (sig ': sigs) f) where
  {-# INLINE fmap #-}
  fmap f (Eff x)  = Eff (fmap f x)
  fmap f (Effs x) = Effs (fmap f x)

instance HFunctor (Effs '[]) where
  {-# INLINE hmap #-}
  hmap h x = case x of {}

instance (HFunctor (Effs sigs), HFunctor sig) => HFunctor (Effs (sig ': sigs)) where
  {-# INLINE hmap #-}
  hmap h (Eff x)  = Eff (hmap h x)
  hmap h (Effs x) = Effs (hmap h x)

-- | @`EffIndex` sig sigs@ finds the index of @sig@ in @sigs@, where
-- the last element has index @0@, and the head element has index @Length sigs - 1@.
type family EffIndex (sig :: a) (sigs :: [a]) :: Nat where
  EffIndex sig (sig ': sigs) = Length sigs
  EffIndex sig (_ ': sigs)   = EffIndex sig sigs

-- | Given @sigs1@ which is a subset of effects in @sigs2@, @`EffIndexes` sigs1
-- sigs2@ finds the index @`EffIndex` sig sigs2@ for each @sig@ in @sigs1@, and
-- returns this as a list of indices.
type family EffIndexes (sigs1 :: [a]) (sigs2 :: [a]) :: [Nat] where
  EffIndexes '[] sigs2            = '[]
  EffIndexes (sig ': sigs1) sigs2 = EffIndex sig sigs2 ': EffIndexes sigs1 sigs2

-- | A value of type @Effs '[] f x@ cannot be created, and this is the
-- absurd destructor for this type.
{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}