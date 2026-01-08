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
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.Internal.Effs.Sum.Type
  ( Effs (..)
  , Algebra
  , Effect
  , absurdEffs
  ) where

import Data.Kind ( Type )
import Data.HFunctor
import Data.Coproduct.Fancy

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | The coproduct of a list of effects.
type Effs :: [Effect] -> Effect
newtype Effs sigs  f a = Effs' { unEffs :: Coprod (f ~$~ a) sigs }

-- | It is slightly annoying that we have to define a newtype @Effs@ so that
-- we can give it instances of @Functor@ and @HFunctor@, while @Coprod@ itself
-- is already a newtype wrapper. To simplify the notation we define a pattern
-- synonym to strip away two layers of newtype wrappers once.
pattern Effs g = Effs' (MkCoprod g)

-- | An auxiliary definition for using `Coprod` to take the coproducts of
-- effects. Too bad in Haskell we have to introduce a layer of @newtype@
-- wrappers for this to work.
type (~$~) :: k1 -> k2 -> (k1 -> k2 -> Type) -> Type
newtype (~$~) f a sig = Apply2 { unApply2 :: sig f a }

-- | A higher-order algebra for the list of effects @effs@ with
-- carrier being the functor @f@. This type is isomorphic to the type
-- @forall a . Effs sigs f a -> f a@, but the definition below is more
-- friendly to static simplification.
type Algebra sigs f = forall a . Cases (f ~$~ a) sigs (f a)

-- | @Effs sigs f@ is a functor if for every element @sig@ of @sigs@, @sig f@
-- is a functor. We need an auxiliary class `FunctorEffsAux` to do induction
-- on @sigs@.
instance FunctorEffsAux sigs f => Functor (Effs sigs f) where
  {-# INLINE fmap #-}
  fmap f (Effs g) = Effs (\cs -> g (fmapCases f cs))

class FunctorEffsAux sigs f where
  fmapCases :: (a -> b) -> Cases (f ~$~ b) sigs c -> Cases (f ~$~ a) sigs c

instance FunctorEffsAux '[] f where
  {-# INLINE fmapCases #-}
  fmapCases _ _ = EndCases

instance (Functor (sig f), FunctorEffsAux sigs f) => FunctorEffsAux (sig ': sigs) f where
  {-# INLINE fmapCases #-}
  fmapCases f (c, cs) = (c . Apply2 . fmap f . unApply2 , fmapCases f cs)

-- | @Effs sigs@ is a higher-order functor if for every element @sig@ of @sigs@ is one
-- We need an auxiliary class `HFunctorEffsAux` to do induction on @sigs@.
instance (forall f. FunctorEffsAux sigs f, HFunctorEffsAux sigs) => HFunctor (Effs sigs) where
  {-# INLINE hmap #-}
  hmap tau (Effs g) = Effs $ g . hmapCases tau

class HFunctorEffsAux sigs where
  hmapCases :: (Functor g, Functor f) => (forall x. g x -> f x) -> Cases (f ~$~ a) sigs b -> Cases (g ~$~ a) sigs b

instance HFunctorEffsAux '[] where
  {-# INLINE hmapCases #-}
  hmapCases _ _ = EndCases

instance (HFunctor sig, HFunctorEffsAux sigs) => HFunctorEffsAux (sig ': sigs) where
  {-# INLINE hmapCases #-}
  hmapCases tau (c, cs) = (c . Apply2 . hmap tau . unApply2, hmapCases tau cs)

-- | A value of type @Effs '[] f x@ cannot be created, and this is the
-- absurd destructor for this type.
{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs (Effs g) = g EndCases