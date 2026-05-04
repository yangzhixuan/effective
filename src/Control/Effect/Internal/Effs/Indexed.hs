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

module Control.Effect.Internal.Effs.Indexed
  ( module Control.Effect.Internal.Effs.Indexed.Type
  , module Control.Effect.Internal.Effs.Indexed.Class
  , pattern Eff
  , pattern Effs
  , open
  , openEff
  , openEffs
  , inj
  , prj
  , (#)
  , weakenEffs
  , hinl
  , hinr
  , houtl
  , houtr
  , weakenAlg
  , hunion
  , heither
  )
  where

import Control.Effect.Internal.Effs.Indexed.Type
import Control.Effect.Internal.Effs.Indexed.Class
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce

--	total alloc = 928,740,800 bytes  (excludes profiling overheads)
-- 	total time  =        0.35 secs   (348 ticks @ 1000 us, 1 processor)

-- import Control.Effect.Internal.Effs.Array
--	total time  =        0.36 secs   (359 ticks @ 1000 us, 1 processor)
--	total alloc = 1,023,990,040 bytes  (excludes profiling overheads)

-- | Matches an effect @sig@ at the head of a signature @sig ': sigs@.

{-# INLINE Eff #-}
pattern Eff :: (HFunctor sig, KnownNat (1 + Length sigs), KnownNat (Length sigs))
  => sig f a -> Effs (sig ': sigs) f a
pattern Eff op <- (openEff -> Just op) where
  Eff op = inj op

{-# INLINE Effs #-}
-- | Matches the tail @sigs@ of effects of a signature @sig ': sigs@.
pattern Effs :: forall sig sigs f a . KnownNat (Length sigs)
  => Effs sigs f a -> Effs (sig ': sigs) f a
pattern Effs op <- (openEffs -> Just op) where
  Effs op = coerce @(Effs sigs f a) @(Effs (sig ': sigs) f a) op

-- | Inspects an operation in the union @sig ': sigs@ and returns the operation
-- specialied to @sig@ if possible, or a union @sigs@ otherwise.
{-# INLINE open #-}
open :: forall sig sigs f a . KnownNat (Length sigs) => Effs (sig ': sigs) f a -> Either (Effs sigs f a) (sig f a)
open  sig@(Effn n (op :: psig f a))
  | n == fromInteger (natVal' (proxy#@(Length sigs))) = Right (unsafeCoerce @(psig f a) @(sig f a) op)
  | otherwise                                         = Left (coerce @(Effs (sig ': sigs) f a) @(Effs sigs f a) sig)

-- | Inspects an operation in the union @sig ': sigs@ and returns the operation
-- specialied to @sig@ if possible.
{-# INLINE openEff #-}
openEff :: forall sig sigs f a . Member sig sigs
  => Effs sigs f a -> Maybe (sig f a)
openEff (Effn n op)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(sig f a) op)
  | otherwise = Nothing
  where n' = fromInteger (natVal' (proxy#@(EffIndex sig sigs)))

-- | Inspects an operation in the union @sig ': sigs@ and returns
-- a union @sigs@ if possible.
{-# INLINE openEffs #-}
openEffs :: forall sig sigs f a . KnownNat (Length sigs)
  => Effs (sig ': sigs) f a -> Maybe (Effs sigs f a)
openEffs effn@(Effn n op)
  | n == m    = Nothing
  | otherwise = Just (coerce @(Effs (sig ': sigs) f a) @(Effs sigs f a) effn)
  where m = fromInteger (natVal' (proxy#@(Length sigs)))


-- | Constructs an operation in the union @Effs sigs f a@ from a single
-- operation @sig f a@, when @sig@ is in @sigs@.
{-# INLINE inj #-}
inj :: forall sig sigs f a . (Member sig sigs) => sig f a -> Effs sigs f a
inj = Effn n
  where
    n = fromInteger (natVal' (proxy# @(EffIndex sig sigs)))

-- | Attempts to project an operation of type @sig f a@ from a the union @Effs sigs f a@,
-- when @sig@ is in @sigs@.
{-# INLINE prj #-}
prj :: forall sig sigs f a . (Member sig sigs)
  => Effs sigs f a -> Maybe (sig f a)
prj (Effn n x)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(sig f a) x)
  | otherwise = Nothing
  where
    n' = fromInteger (natVal' (proxy# @(EffIndex sig sigs)))

-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall sigs1 sigs2 m .
  (Monad m, KnownNat (Length sigs2))
  => (Algebra sigs1 m)
  -> (Algebra sigs2 m)
  -> (Algebra (sigs1 :++ sigs2) m)
falg # galg = heither @sigs1 @sigs2 (falg) (galg)

-- | Weakens the signature of an operation in the union containing @sigs@
-- to one that contains @sig ': sigs@ for any @sig@.
{-# INLINE weakenEffs #-}
weakenEffs :: forall sig sigs f a . Effs sigs f a -> Effs (sig ': sigs) f a
weakenEffs = coerce @(Effs sigs f a) @(Effs (sig ': sigs) f a)

--instance Functor f => Functor (Effs sigs f) where
--  {-# INLINE fmap #-}
--  fmap f (Effn n op) = Effn n (fmap f op)

instance Functor (Effs '[] f) where
  {-# INLINE fmap #-}
  fmap f = absurdEffs

instance (Functor f, Functor (sig f), Functor (Effs sigs f), KnownNat (Length sigs))
  => Functor (Effs (sig ': sigs) f) where
  {-# INLINE fmap #-}
  fmap f e = case open e of
    Left  o -> coerce (fmap f o)
    Right o -> inj (fmap f o)

instance HFunctor (Effs '[]) where
  {-# INLINE hmap #-}
  hmap h = absurdEffs

instance (HFunctor sig, HFunctor (Effs sigs), KnownNat (Length sigs))
  => HFunctor (Effs (sig ': sigs)) where
  {-# INLINE hmap #-}
  hmap h e = case open e of
    Left o  -> coerce (hmap h o)
    Right o -> inj (hmap h o)


-- | Weakens an an operation of type @Effs sigs1 f a@ to one of type @Effs (sigs1 :++ sigs2) f a@.
{-# INLINE hinl #-}
hinl :: forall sigs1 sigs2 f a . KnownNat (Length sigs2)
  => Effs sigs1 f a -> Effs (sigs1 :++ sigs2) f a
hinl (Effn n op) = Effn (m + n) op
  where
    -- m = fromInteger (fromSNat (natSing @(Length sigs2)))
    m = fromInteger (natVal' (proxy# @(Length sigs2)))

-- | Weakens an an operation of type @Effs sigs2 f a@ to one of type @Effs (sigs1 :++ sigs2) f a@.
{-# INLINE hinr #-}
hinr :: forall sigs1 sigs2 f a . Effs sigs2 f a -> Effs (sigs1 :++ sigs2) f a
hinr = coerce @(Effs sigs2 f a) @(Effs (sigs1 :++ sigs2) f a)

-- | Attempts to project a value of type @Effs sigs1 f a@ from a union of type @Effs (sigs1 :++ sigs2) f a@.
{-# INLINE houtl #-}
houtl :: forall sigs1 sigs2 f a . KnownNat (Length sigs2)
  => Effs (sigs1 :++ sigs2) f a -> Maybe (Effs sigs1 f a)
houtl (Effn n op)
  | n < m     = Nothing
  | otherwise = Just (Effn (n - m) op)
  where
    m = fromInteger (natVal' (proxy# @(Length sigs2)))

-- | Attempts to project a value of type @Effs sigs2 f a@ from a union of type @Effs (sigs1 :++ sigs2) f a@.
{-# INLINE houtr #-}
houtr :: forall sigs1 sigs2 f a . KnownNat (Length sigs2)
  => Effs (sigs1 :++ sigs2) f a -> Maybe (Effs sigs2 f a)
houtr effn@(Effn n op)
  | n < m     = Just (coerce @(Effs (sigs1 :++ sigs2) f a) @(Effs sigs2 f a) effn)
  | otherwise = Nothing
  where
    m = fromInteger (natVal' (proxy# @(Length sigs2)))


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
{-# INLINE hunion #-}
hunion :: forall sigs1 sigs2 f a b . Injects (sigs2 :\\ sigs1) sigs2
  => (Effs sigs1 f a -> b) -> (Effs sigs2 f a -> b)
  -> (Effs (sigs1 `Union` sigs2) f a -> b)
hunion xalg yalg = heither @sigs1 @(sigs2 :\\ sigs1) xalg (yalg . injs)

-- | Creates an alebra that can work with either signatures in @sigs1@
-- or @sigs2@ by using the provided algebras as appropriate.
{-# INLINE heither #-}
heither :: forall sigs1 sigs2 f a b . KnownNat (Length sigs2)
  => (Effs sigs1 f a -> b) -> (Effs sigs2 f a -> b) -> (Effs (sigs1 :++ sigs2) f a -> b)
heither xalg yalg (Effn n op)
  | n < m     = yalg (Effn n op)
  | otherwise = xalg (Effn (n - m) op)
  where
    -- m = fromInteger (fromSNat (natSing @(Length sigs2)))
    m = fromInteger (natVal' (proxy#@(Length sigs2)))

-- | This type witnesses that two effect lists can be appended together.
type Append xs ys = (KnownLength (xs :++ ys), KnownNat (Length ys), KnownNat (Length xs))

type family KnownLength sigs :: Constraint where
  KnownLength (sig:sigs) = (KnownLength sigs, KnownNat (1 + Length sigs))
  KnownLength sigs = KnownNat (Length sigs)