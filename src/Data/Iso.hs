{-|
Module      : Data.Iso
Description : Isomorphisms
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module defines a type @Iso a b@ for a pair of functions @a -> b@
and @b -> a@ that are supposed to form an isomorphism.
-}
module Data.Iso where

data Iso a b = Iso { fwd :: !(a -> b), bwd :: !(b -> a) }

-- | Identity function is an isomorphism.
refl :: Iso a a
refl = Iso id id

-- | Isomorphism are invertible.
sym :: Iso a b -> Iso b a
sym (Iso f g) = Iso g f

-- | Compose two isomorphisms.
trans :: Iso a b -> Iso b c -> Iso a c
trans (Iso f g) (Iso h k) = Iso (h . f) (g . k)

-- | Isomorphisms are preserved by functors.
cong :: Functor f => Iso a b -> Iso (f a) (f b)
cong (Iso f g) = Iso (fmap f) (fmap g)