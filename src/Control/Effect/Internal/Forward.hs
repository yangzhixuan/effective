{-|
Module      : Control.Effect.Internal.Forward
Description : Default forwarding algebras
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module provides a class @ForwardsC cs sigs ts@ that associates the transformer
stack @ts@ with an algebra transformer @`fwdsC` :: AlgTrans sigs sigs ts cs@ that is
expected to be 'the canonical way' to forward the effects @sigs@ along @ts@.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Control.Effect.Internal.Forward
  ( Forward (..)
  , ForwardEffs (..)
  , Forwards (..)
  , ForwardsC (..)
  , ForwardsM (..)
  ) where

import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Algebra
import Language.Haskell.TH (CodeQ)

import Data.Kind
import Data.HFunctor

-- | The class demonstrating that an effect @sig@ on every type constructor satisfying @cs@
-- can be forwarded through a transformer @t@.
-- This is a typeclass that is expected to be instantiated by the user of @effective@ for
-- user-defined transformers @t@, but the user should /use/ the typeclass `Forwards` or `ForwardsC`
-- that automatically deal with forwarding a list of effects along a list of transformers.
class Forward (sig :: Effect) (t :: (Type -> Type) -> (Type -> Type)) where
  -- | @FwdConstraint sig t@ is the constraint that the carrier needs to satisfy in order
  -- to forward the effect @sig@. The default value is the constraint `Monad`.
  type FwdConstraint sig t :: (Type -> Type) -> Constraint
  type FwdConstraint sig t = Monad

  -- | @fwd@ constructs an @eff@-algebra on @t m@ given an @eff@-algebra on @m@, for every
  -- @m :: Type -> Type@ satisfying the constraint @FwdConstraint eff t@.
  fwd :: forall m . FwdConstraint eff t m
      => (forall x . eff m x     -> m x)
      -> (forall x . eff (t m) x -> t m x)

  -- | @fwdC@ is the static version of `fwd` that works on code of algebras. It has a default
  -- implementation in terms of `fwd` but it is possible more efficient implementations exist
  -- for some @t@.
  fwdC :: forall m . FwdConstraint eff t m
       => CodeQ (eff m -.> m)
       -> CodeQ (eff (t m) -.> t m)
  fwdC c = [|| NT $ fwd (at $$c) ||]

{-
-- In theory the following instance is very useful but it causes conflicting
-- definitions of the associated type family @FwdConstraint@ with the instance
-- @Forward (Alg sig) t@, and I don't know how to workaround it.

instance HFunctor sig => Forward sig IdentityT where
  type FwdConstraint sig IdentityT = Functor
  fwd alg = IdentityT . alg . hmap runIdentityT
-}

-- | This class builds a forwarder for an t`Effs` by recursion over @sigs@,
-- by ensuring that each effect can be forwarded through a given @t@.
-- This is an internal typeclass that the user of @effective@ don't need
-- to use explicitly.
class ForwardEffs effs (t :: (Type -> Type) -> (Type -> Type))  where
  type FwdEffsConstraint effs t :: (Type -> Type) -> Constraint
  fwdEffs :: AlgTrans effs effs '[t] (FwdEffsConstraint effs t)

  fwdEffsC :: AlgTransC effs effs '[t] (FwdEffsConstraint effs t)

instance ForwardEffs '[] t where
  type FwdEffsConstraint '[] t = TruthC

  {-# INLINE fwdEffs #-}
  fwdEffs :: AlgTrans '[] '[] '[t] TruthC
  fwdEffs = AlgTrans $ \_ -> endAlg

  fwdEffsC :: AlgTransC '[] '[] '[t] TruthC
  fwdEffsC = AlgTransC $ \EndAC -> EndAC

instance ( HFunctor eff
         , Forward eff t
         , ForwardEffs effs t
         )
         => ForwardEffs (sig ': sigs) t where

  type FwdEffsConstraint (sig ': sigs) t = AndC (FwdConstraint sig t) (FwdEffsConstraint sigs t)

  {-# INLINE fwdEffs #-}
  fwdEffs :: AlgTrans (eff ': effs) (eff ': effs) '[t] (FwdEffsConstraint (eff ': effs) t)
  fwdEffs = AlgTrans $ \(alg :# algs) -> fwd alg :# getAT fwdEffs algs

  fwdEffsC :: AlgTransC (eff : effs) (eff : effs) '[t] (FwdEffsConstraint (eff : effs) t)
  fwdEffsC = AlgTransC $ \(ca :#$ cas) -> fwdC ca :#$ getATC fwdEffsC cas

-- | This class builds a forwarder for an t`Effs` along a list @ts@ of transformers
-- by ensuring that each transformer in @ts@ can forward @sigs@.
-- This class is expected to be used by the user of @effective@ whenever they need
-- to assert that some transformers can forward some effects, but this class is not
-- expected to be instantiated by the user because the following instances reduce
-- @Forwards sigs ts@ to @`Forward` cs sig t@ for every @t@ in @ts@ and every
-- @sig@ in @sigs@.
class Forwards sigs ts where
  type FwdsConstraint sigs ts :: (Type -> Type) -> Constraint
  fwds :: AlgTrans sigs sigs ts (FwdsConstraint sigs ts)

  fwdsC :: AlgTransC effs effs ts (FwdsConstraint effs ts)

instance Forwards effs '[] where
  type FwdsConstraint effs '[] = TruthC

  {-# INLINE fwds #-}
  fwds :: AlgTrans sigs sigs '[] (FwdsConstraint sigs '[])
  fwds = AlgTrans $ \alg -> alg

  fwdsC :: AlgTransC effs effs '[] (FwdsConstraint effs '[])
  fwdsC = AlgTransC $ \alg -> alg

instance (ForwardEffs effs t, Forwards effs ts) => Forwards effs (t ': ts) where
  type FwdsConstraint effs (t ': ts) =
    CompC ts (FwdEffsConstraint effs t) (FwdsConstraint effs ts)

  {-# INLINE fwds #-}
  fwds :: AlgTrans sigs sigs (t ': ts) (FwdsConstraint sigs (t ': ts))
  fwds = AlgTrans $ \(alg :: Algebra sigs m) ->
    getAT (fwdEffs @_ @t) (getAT (fwds @_ @ts) alg)

  fwdsC :: AlgTransC effs effs (t ': ts) (FwdsConstraint effs (t ': ts))
  fwdsC = AlgTransC $ \(calg :: AlgebraC effs m) ->
    getATC (fwdEffsC @_ @t) (getATC (fwdsC @_ @ts) calg)

-- | @ForwardsC cs effs ts@ if and only if effects @effs@ on @m@ can be transformed along
-- the transformer stack @ts@ on input satisfying the constraint @cs@.
class    (Forwards sigs ts, ImpliesC cs (FwdsConstraint sigs ts)) => ForwardsC cs sigs ts where
instance (Forwards sigs ts, ImpliesC cs (FwdsConstraint sigs ts)) => ForwardsC cs sigs ts where

-- | @ForwardsM sigs ts@ if and only if effects @sigs@ on every monad @m@ can be
-- transformed along the transformer stack @ts@.
class    (Forwards sigs ts, ImpliesC Monad (FwdsConstraint sigs ts)) => ForwardsM sigs ts where
instance (Forwards sigs ts, ImpliesC Monad (FwdsConstraint sigs ts)) => ForwardsM sigs ts where
