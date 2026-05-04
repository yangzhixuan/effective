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

module Control.Effect.Internal.Effs.Indexed.Type where

import Data.Kind ( Type )
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | A higher-order algebra for the union of effects @sigs@ with
-- carrier being the functor @f@.
type Algebra sigs f =
  forall x . Effs sigs f x -> f x

-- | A higher-order algebra for a single effect @sig@ with
-- carrier being the functor @f@.
type Algebra1 sig f =
  forall x . sig f x -> f x

-- | @Effs sigs f a@ creates a union of the effect signatures in the list @sigs@.
type Effs :: [Effect] -> Effect
data Effs sigs f a where
  -- | @`Effn` n op@ places an operation @n@ away from the last element of the list.
  Effn :: {-# UNPACK #-} !Int -> !(sig f a) -> Effs sigs f a

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

-- | @Member sig sigs@ holds when @sig@ is contained in @sigs@.
type Member :: Effect -> [Effect] -> Constraint
type Member sig sigs = (KnownNat (EffIndex sig sigs))

-- | @Member sigs sigs'@ holds when every @sig@ which is a 'Member' of in @sigs@
-- is also a 'Member' of @sigs'@.
type family Members (sigs1 :: [Effect]) (sigs2 :: [Effect]) :: Constraint where
  Members '[] sigs2       = ()
  Members (sig ': sigs1) sigs2 = (Member sig sigs2, Members sigs1 sigs2)
