{-|
Module      : Control.Effect.Internal.Effs.Array
Description : Array based union
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Internal.Effs.Indexed.Array where
import Control.Effect.Internal.Effs.Indexed.Type

import Data.List.Kind

import GHC.TypeLits
import GHC.Exts

import Control.Monad.ST
import Data.Array.ST
import Data.Array


-- | Injects sigs1 sigs2 means that all of sigs1 is in sigs2
-- Some other effects may be in sigs2, so sigs1 <= sigs2
class KnownNat (Length sigs1) => Injects sigs1 sigs2 where
  injs :: Effs sigs1 f a -> Effs sigs2 f a
  ixs :: Array Int Int

instance (KnownNats (EffIndexes sigs1 sigs2), KnownNat (Length sigs1))
  => Injects sigs1 sigs2 where
  {-# INLINE injs #-}
  injs (Effn n op) = Effn (ixs @sigs1 @sigs2 ! n) op

  {-# INLINE ixs #-}
  ixs = runSTArray $ do arr <- newArray_ (0, m - 1)
                        natVals (proxy# :: Proxy# (EffIndexes sigs1 sigs2)) arr
                        return arr
    where
      m = fromInteger (natVal' (proxy# :: Proxy# (Length sigs1)))

-- | A class that witnesses that all the type level nats @ns@ can be reflected
-- into a value level list. Indexing starts from the end of the list, so that
-- the last element always has index @0@.
class KnownNat (Length ns) => KnownNats (ns :: [Nat]) where
  natVals :: Proxy# ns -> STArray s Int Int -> ST s ()

instance KnownNats '[] where
  {-# INLINE natVals #-}
  natVals _ _ = return ()

instance (KnownNat x, KnownNats xs, KnownNat (Length (x ': xs))) => KnownNats (x ': xs) where
  {-# INLINE natVals #-}
  natVals _ arr = do writeArray arr (fromInteger $ natVal' (proxy# @(Length xs)))
                                    (fromInteger $ natVal' (proxy# @x))
                     natVals (proxy# :: Proxy# xs) arr