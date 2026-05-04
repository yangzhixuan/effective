{-|
Module      : Control.Effect.Internal.ProgImp
Description : Programs in impredicatie encoding
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides a representation of effectful programs based on impredicative encoding,
which provides good performance for monadic binding and deep handling, but is very bad at
shallow handling (pattern matching). The @effective@ library emphasises deep handling, so
the representation from this module is suitable for our purpose.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE LambdaCase #-}

module Control.Effect.Internal.Prog.ProgImp (
  -- * Program datatype
  Prog,

  -- * Program constructors
  call,
  callJ,
  callK,
  progAlg,
  weakenProg,

  -- * Program eliminator
  eval,
  )
  where
import Control.Effect.Internal.Effs

import Data.HFunctor
#if MIN_VERSION_base(4,18,0)
#else
import Control.Applicative
#endif
import Control.Monad

-- | The impredicative-encoding of effectful programs
newtype Prog (sigs :: [Effect]) a = Prog { runProg :: forall m. Monad m => Algebra sigs m -> m a }

-- | Construct a program of type @Prog sigs a@ using an operation @sig@.
{-# INLINE call #-}
call :: forall sig sigs a . (Member sig sigs, HFunctor sig) => sig (Prog sigs) a -> Prog sigs a
call x = Prog $ \(alg :: Algebra sigs m) ->
  let r :: forall x. Prog sigs x -> m x
      r p = runProg p alg
  in alg (inj (hmap r x))

-- | A variant of `call` with an continuation argument given as return values.
-- Semantically, @callJ = join . `call`@.
{-# INLINE callJ #-}
callJ :: forall sig sigs a . (Member sig sigs, HFunctor sig)
     => sig (Prog sigs) (Prog sigs a) -> Prog sigs a
callJ = join . call

-- | A variant of `call` with an continuation argument given as a function.
-- Semantically, @callK x k = `call` x >>= k@.
{-# INLINE callK #-}
callK :: forall sig sigs a b . (Member sig sigs, HFunctor sig)
      => sig (Prog sigs) a -> (a -> Prog sigs b) -> Prog sigs b
callK x k = call x >>= k

-- | Construct a program from an operation in a union.
{-# INLINE progAlg #-}
progAlg :: forall sigs. HFunctor (Effs sigs) => Algebra sigs (Prog sigs)
progAlg x = Prog $ \(alg :: Algebra sigs m) ->
  let r :: forall x. Prog sigs x -> m x
      r p = runProg p alg
  in alg (hmap r x)

instance Functor (Prog sigs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap f p = Prog $ \alg -> fmap f (runProg p alg)

instance Applicative (Prog sigs) where
  {-# INLINE pure #-}
  pure :: a -> Prog sigs a
  pure a = Prog $ \alg -> return a

  {-# INLINE (<*>) #-}
  (<*>) :: Prog sigs (a -> b) -> Prog sigs a -> Prog sigs b
  (<*>) = ap

instance Monad (Prog sigs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  p >>= k = Prog $ \alg -> runProg p alg >>= (\a -> runProg (k a) alg)

-- | Weaken a program of type @Prog sigs a@ so that it can be used in
-- place of a program of type @Prog sigs a@, when every @sigs@ is a member of @sigs'@.
weakenProg :: forall sigs sigs' a
  . ( Injects sigs sigs'
    , HFunctor (Effs sigs)
    )
  => Prog sigs a -> Prog sigs' a
weakenProg p = Prog $ \alg -> runProg p (alg . injs)

-- | Evaluate a program using the supplied algebra. This is the
-- universal property from initial monad @Prog sig a@ equipped with
-- the algebra @Eff sigs m -> m@.
{-# INLINE eval #-}
eval
  :: forall sigs m a . (Monad m, HFunctor (Effs sigs))
  => Algebra sigs m
  -> Prog sigs a -> m a
eval alg p = runProg p alg