{-|
Module      : Control.Effect.Internal.Prog
Description : Program constructors and deconstructors
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE LambdaCase #-}

module Control.Effect.Internal.Prog.ProgDirect (
  -- * Program datatype
  Prog (..),

  -- * Program constructors
  call,
  callJ,
  callK,
  progAlg,
  weakenProg,

  -- * Program eliminator
  eval,
  fold,
  ) where
import Control.Effect.Internal.Effs

import Data.HFunctor
#if MIN_VERSION_base(4,18,0)
#else
import Control.Applicative
#endif
import Control.Monad

-- | A program that contains at most the effects in @sigs@,
-- to be processed by a handler in the exact order given in @sigs@.
data Prog (sigs :: [Effect]) a where
  Return :: a -> Prog sigs a
  Call  :: forall sigs a x
        .  (Effs sigs) (Prog sigs) x
        -> (x -> Prog sigs a)
        -> Prog sigs a

-- | Construct a program of type @Prog sigs a@ using an operation @sig@.
{-# INLINE call #-}
call :: forall sig sigs a . Member sig sigs => sig (Prog sigs) a -> Prog sigs a
call x = Call (inj x) Return

-- | A variant of `call` with an continuation argument given as return values.
-- Semantically, @callJ = join . `call`@.
{-# INLINE callJ #-}
callJ :: forall sig sigs a . Member sig sigs => sig (Prog sigs) (Prog sigs a) -> Prog sigs a
callJ x = Call (inj x) id

-- | A variant of `call` with an continuation argument given as a function.
-- Semantically, @callK x k = `call` x >>= k@.
{-# INLINE callK #-}
callK :: forall sig sigs a b . Member sig sigs
      => sig (Prog sigs) a -> (a -> Prog sigs b) -> Prog sigs b
callK x k = Call (inj x) k

instance Functor (Prog sigs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap f (Return x)  = Return (f x)
  fmap f (Call op k) = Call op (fmap f . k)

instance Applicative (Prog sigs) where
  {-# INLINE pure #-}
  pure :: a -> Prog sigs a
  pure  = Return

  {-# INLINE (<*>) #-}
  (<*>) :: Prog sigs (a -> b) -> Prog sigs a -> Prog sigs b
  Return f    <*> p = fmap f p
  Call opf kf <*> q = Call opf ((<*> q) . kf)

  {-# INLINE (*>) #-}
  (*>) :: Prog sigs a -> Prog sigs b -> Prog sigs b
  (*>) = liftA2 (const id)

  {-# INLINE (<*) #-}
  (<*) :: Prog sigs a -> Prog sigs b -> Prog sigs a
  (<*) = liftA2 const

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Prog sigs a -> Prog sigs b -> Prog sigs c
  liftA2 f (Return x) q    = fmap (f x) q
  liftA2 f (Call opx kx) q = Call opx ((flip (liftA2 f) q) . kx)

instance Monad (Prog sigs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  Return x   >>= f = f x
  Call op k  >>= f = Call op (k >=> f)

-- | Weaken a program of type @Prog sigs a@ so that it can be used in
-- place of a program of type @Prog sigs a@, when every @sigs@ is a member of @sigs'@.
weakenProg :: forall sigs sigs' a
  . ( Injects sigs sigs'
    , HFunctor (Effs sigs)
    )
  => Prog sigs a -> Prog sigs' a
weakenProg (Return x)  = Return x
weakenProg (Call op k) = Call (injs @sigs @sigs' (hmap weakenProg op)) (weakenProg . k)


-- | Evaluate a program using the supplied algebra. This is the
-- universal property from initial monad @Prog sig a@ equipped with
-- the algebra @Eff sigs m -> m@.
{-# INLINE eval #-}
eval
  :: forall sigs m a . (Monad m, HFunctor (Effs sigs))
  => Algebra sigs m
  -> Prog sigs a -> m a
eval halg (Return x)   = return x
eval halg (Call op k)  = halg (hmap (eval halg) op) >>= eval halg . k

{-
-- Static argument transform:
-- This degrades performance a bit.
eval halg p =
  let eval' :: forall x . Prog sigs x -> m x
      eval' p' = case p' of
                   Return x     -> return x
                   Call op hk k ->
                     join . halg . fmap (eval' . k)
                                 . hmap (eval' . hk) $ op
  in eval' p
-}

-- | Fold a program using the supplied generator and algebra. This is the
-- universal property from the underlying GADT.
fold :: forall f sigs a . (Functor f, Functor (Effs sigs f), HFunctor (Effs sigs))
  => (forall x . x -> f x)
  -> (forall x . (Effs sigs f) (f x) -> f x)
  -> Prog sigs a -> f a
fold gen alg (Return x) = gen x
fold gen alg (Call op k) =
  alg ((fmap (fold gen alg . k) . hmap (fold gen alg)) op)


-- | Attempt to project an operation of type @sig (Prog sigs) (Prog sigs a)@.
{-# INLINE prjCall #-}
prjCall :: forall sig sigs a . (HFunctor sig, HFunctor (Effs sigs)) =>
  Member sig sigs => Prog sigs a -> Maybe (sig (Prog sigs) (Prog sigs a))
prjCall (Call op k) = prj (fmap k $ op)
prjCall _           = Nothing

-- | Construct a program from an operation in a union.
{-# INLINE progAlg #-}
progAlg :: Algebra sigs (Prog sigs)
progAlg x = Call x return