{-|
Module      : Control.Effect.Internal.Effs.Class
Description : Class based union
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}

module Control.Effect.Internal.Effs.Indexed.Class where
import Control.Effect.Internal.Effs.Indexed.Type

import Data.List.Kind

import GHC.TypeLits
import GHC.Exts

-- | Provides an injection when all effects in @sigs1@ are contained in @sigs2@.
class KnownNat (Length sigs1) => Injects sigs1 sigs2 where
  injs :: forall f a . Effs sigs1 f a -> Effs sigs2 f a

instance Injects '[] sigs2 where
  {-# INLINE injs #-}
  injs = absurdEffs

instance ( KnownNat (Length (sig ': sigs1))
         , Injects sigs1 sigs2
         , KnownNat (EffIndex sig sigs2)
         )
  => Injects (sig ': sigs1) sigs2 where
  {-# INLINE injs #-}
  injs :: forall f a . Effs (sig ': sigs1) f a -> Effs sigs2 f a
  injs (Effn n op)
    | n == n'   = Effn i' op
    | otherwise = injs @sigs1 @sigs2 @f @a  (Effn n op)
    where
      n' = fromInteger (natVal' (proxy# @(Length sigs1)))
      i' = fromInteger (natVal' (proxy# @(EffIndex sig sigs2)))
