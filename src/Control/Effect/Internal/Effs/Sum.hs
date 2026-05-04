{-|
Module      : Control.Effect.Internal.Effs
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
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal.Effs.Sum
  ( module Control.Effect.Internal.Effs.Sum.Type
  , inj
  , prj
  , (#)
  , Append (..)
  , weakenAlg
  , hunion
  , hcons
  , Injects (..)
  , Member
  , Members
  )
  where

import Control.Effect.Internal.Effs.Sum.Type
import Data.List.Kind
import GHC.Exts

infixr 6 #
-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall sigs1 sigs2 m .
  (Monad m, Append sigs1 sigs2)
  => (Algebra sigs1 m)
  -> (Algebra sigs2 m)
  -> (Algebra (sigs1 :++ sigs2) m)
falg # galg = heither @sigs1 @sigs2 (falg) (galg)

hcons :: (x h a -> b) -> (Effs xs h a -> b) -> (Effs (x ': xs) h a -> b)
hcons alg algs (Eff x)   = alg x
hcons alg algs (Effs xs) = algs xs

-- | This type class provides operations that support appending
-- two effect lists together.
type  Append :: [Effect] -> [Effect] -> Constraint
class Append xs ys where
  -- | Creates an alebra that can work with either signatures in @sigs1@
  -- or @sigs2@ by using the provided algebras as appropriate.
  heither :: (Effs xs h a -> b) -> (Effs ys h a -> b) -> (Effs (xs :++ ys) h a -> b)

  -- | Weakens an an operation of type @Effs sigs1 f a@ to one of type @Effs (sigs1 :++ sigs2) f a@.
  hinl :: Effs xs f a -> Effs (xs :++ ys) f a

  -- | Weakens an an operation of type @Effs sigs2 f a@ to one of type @Effs (sigs1 :++ sigs2) f a@.
  hinr :: Effs ys f a -> Effs (xs :++ ys) f a

  -- | Attempts to project a value of type @Effs sigs1 f a@ from a union of type @Effs (sigs1 :++ sigs2) f a@.
  houtl :: Effs (xs :++ ys) f a -> Maybe (Effs xs f a)

  -- | Attempts to project a value of type @Effs sigs2 f a@ from a union of type @Effs (sigs1 :++ sigs2) f a@.
  houtr :: Effs (xs :++ ys) f a -> Maybe (Effs ys f a)

instance Append '[] ys where
  {-# INLINE heither #-}
  heither :: (Effs '[] f a -> b) -> (Effs ys f a -> b) -> (Effs ('[] :++ ys) f a -> b)
  heither xalg yalg = yalg

  {-# INLINE hinl #-}
  hinl :: Effs '[] f a -> Effs ys f a
  hinl = undefined -- absurdEffs

  {-# INLINE hinr #-}
  hinr :: Effs ys f a -> Effs ys f a
  hinr = id

  {-# INLINE houtl #-}
  houtl :: Effs ys f a -> Maybe (Effs '[] f a)
  houtl = const Nothing

  {-# INLINE houtr #-}
  houtr :: Effs ys f a -> Maybe (Effs ys f a)
  houtr = Just

instance Append xs ys => Append (x ': xs) ys where
  {-# INLINE heither #-}
  heither :: (Effs (x : xs) f a -> b) -> (Effs ys f a -> b) -> Effs ((x : xs) :++ ys) f a -> b
  heither xalg yalg (Eff x)  = xalg (Eff x)
  heither xalg yalg (Effs x) = heither (xalg . Effs) yalg x

  {-# INLINE hinl #-}
  hinl :: Effs (x : xs) f a -> Effs ((x : xs) :++ ys) f a
  hinl (Eff x)  = Eff x
  hinl (Effs x) = Effs (hinl @xs @ys x)

  {-# INLINE hinr #-}
  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  {-# INLINE houtl #-}
  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  {-# INLINE houtr #-}
  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x

-- | Weakens an algera that works on @sigs2@ to work on @sigs1@ when
-- every effect in @sigs1@ is in @sigs2@.
{-# INLINE weakenAlg #-}
weakenAlg
  :: forall sigs1 sigs2 m x . (Injects sigs1 sigs2)
  => (Effs sigs2 m x -> m x)
  -> (Effs sigs1  m x -> m x)
weakenAlg alg = alg . injs

-- | Constructs an algebra for the union containing @sigs1 `Union` sigs2@
-- by using an algebra for the union @sigs1@ and aonther for the union @sigs2@.
-- If an effect is in both @sigs1@ and @sigs2@, the algebra for @sigs1@ is used.
{-# INLINE hunion #-}
hunion :: forall sigs1 sigs2 f a b
  .  ( Append sigs1 (sigs2 :\\ sigs1), Injects (sigs2 :\\ sigs1) sigs2 )
  => (Effs sigs1 f a -> b) -> (Effs sigs2 f a -> b)
  -> (Effs (sigs1 `Union` sigs2) f a -> b)
hunion xalg yalg = heither @sigs1 @(sigs2 :\\ sigs1) xalg (yalg . injs)

-- | @Injects xs ys@ means that all of @xs@ is in @xys@.
-- Some other effects may be in @xys@, so @xs <= xys@.
type  Injects :: [Effect] -> [Effect] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

instance Injects '[] xys where
  {-# INLINE injs #-}
  injs :: Effs '[] f a -> Effs xys f a
  injs = absurdEffs

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  {-# INLINE injs #-}
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

-- | @Member' sig sigs n@ holds when @sig@ is contained in @sigs@ at index @n@.
class Member sig sigs where
  -- | Constructs an operation in the union @Effs sigs f a@ from a single
  -- operation @sig f a@, when @sig@ is in @sigs@.
  inj :: sig f a -> Effs sigs f a

  -- | Attempts to project an operation of type @sig f a@ from a the union @Effs sigs f a@,
  -- when @sig@ is in @sigs@.
  prj :: Effs sigs f a -> Maybe (sig f a)

instance {-# OVERLAPPING #-} Member sig (sig ': sigs) where
  {-# INLINE inj #-}
  inj :: sig f a -> Effs (sig ': sigs) f a
  inj x = Eff x

  {-# INLINE prj #-}
  prj :: Effs (sig : sigs) f a -> Maybe (sig f a)   -- Should we Church-encode the Maybe for better inlining
  prj (Eff x) = Just x
  prj _       = Nothing

instance (Member sig sigs) => Member sig (sig' : sigs) where
  {-# INLINE inj #-}
  inj x = Effs . inj $ x

  {-# INLINE prj #-}
  prj (Eff _)  = Nothing
  prj (Effs x) = prj x


-- | @Member sigs sigs'@ holds when every @sig@ which is a 'Member' of in @sigs@
-- is also a 'Member' of @sigs'@.
type family Members (sigs1 :: [Effect]) (sigs2 :: [Effect]) :: Constraint where
  Members '[] sigs2       = ()
  Members (sig ': sigs1) sigs2 = (Member sig sigs2, Members sigs1 sigs2)