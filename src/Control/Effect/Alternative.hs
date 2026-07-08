{-|
Module      : Control.Effect.Alternative
Description : Effects for alternatives with choose and empty
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Alternative (
  -- * Syntax
  -- ** Operations

  -- | The operations for alternatives use 'empty' and '<|>' directly
  -- from the 'Control.Applicative.Alternative' type class.
  --
  -- 'empty' is an algebraic operation:
  --
  -- > empty >>= k = empty
  --
  -- '<|>' is a scoped operation.
  Ap.empty, emptyP, emptyM,
  (<|>), chooseP, chooseM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  emptyN, chooseN,
#endif
  select, selects,

  -- ** Signatures
  Empty, Empty_(..), pattern Empty,
  Choose, Choose_(..), pattern Choose,

  -- * Semantics
  -- ** Handlers
  alternative,

  -- ** Algebras
  alternativeAT,
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Applicative ((<|>), Alternative)
import Control.Applicative qualified as Ap

$(makeAlg [e| empty :: 0 |])

$(makeScp [e| choose :: 2 |])

-- | `select` nondeterministically selects an element from a list.
-- If the list is empty, the computation fails.
select :: [a] -> a ! [Choose, Empty]
select xs = foldr ((<|>) . return) empty xs

-- | `selects` generates all permutations of a list, returning each element
-- along with the remaining elements of the list.
selects :: [a] -> (a, [a]) ! [Choose, Empty]
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|> do  (y, ys) <- selects xs
                                           return (y, x:ys)


-- | Instance for 'Alternative' that uses @Empty@ and @Choose@.
instance (Member Empty sigs, Member Choose sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty :: Member Empty sigs => Prog sigs a
  empty = call (Alg Empty_)

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  (<|>) :: (Member Choose sigs) => Prog sigs a -> Prog sigs a -> Prog sigs a
  xs <|> ys = call (Scp (Choose_ xs ys))

-- | The 'alternative' handler makes use of an 'Alternative' functor @f@
-- as well as a transformer @t@ that produces an 'Alternative' functor @t m@.
-- for any monad @m@ to provide semantics.
{-# INLINE alternative #-}
alternative
  :: forall t f a
  .  (forall m . Monad m => Alternative (t m))
  => (forall m . Monad m => (forall a . t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] '[t] a (f a)
alternative run = Handler (runner' run) alternativeAT

-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
alternativeAT
  :: forall t. (forall m . Monad m => Alternative (t m))
  => AlgTrans '[Empty, Choose] '[] '[t] Monad
alternativeAT = algTrans' (emptyAlg :#. chooseAlg)

{-# INLINE emptyAlg #-}
emptyAlg :: Alternative (t m) => Empty (t m) x -> t m x
emptyAlg Empty = Ap.empty

{-# INLINE chooseAlg #-}
chooseAlg :: Alternative (t m) => Choose (t m) x -> t m x
chooseAlg (Choose xs ys) = xs <|> ys