{-|
Module      : Control.Effect.Internal.Algebra
Description : The data structure for storing effect operations.
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PatternSynonyms #-}

module Control.Effect.Internal.Algebra where

import Data.List.Kind
import Data.Kind (Type, Constraint)
import Data.Sequence.Class
import qualified Data.Sequence as FT
import qualified Data.Primitive.SmallArray as Arr
import Data.Iso
import GHC.Base (Any)
import Unsafe.Coerce (unsafeCoerce)
import Language.Haskell.TH hiding (Type)

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | An algebra for the effects @effs@ with carrier being the functor @f@.
-- Informally,
-- @
-- Algebra s [eff1, ..., eff_n] f = forall x. (eff1 f x -> f x, ..., eff_n f x -> f x)
-- @
-- The parameter @s@ is a data structure (satisfying the contraint `Sequence`) for
-- better internal representation of the components of the algebra.
newtype Algebra_
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  = Algebra { unAlgebra :: forall x. Cases s effs f x (f x) }

-- | The default data structure for storing algebras is finger trees.
type Algebra effs f = Algebra_ FT.Seq effs f

-- | Array-based representation is useful for fast accessing after we
-- construct the algebra.
type AlgebraArray effs f = Algebra_ Arr.SmallArray effs f

-- | @Effs s [eff1, ..., eff_n]@ is the coproduct of @eff1@, ..., @eff_n@, represented
-- using Church encoding:
-- @
--   Effs s [eff1, ..., eff_n] f x
-- = eff1 f x + ... + eff_n f x
-- = forall y. (eff1 f x -> y, ... , eff_n f x -> y) -> y
-- = forall y. Cases f x y -> y
-- @

newtype Effs
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  (x :: Type)
  = Effs { unEffs :: forall y. Cases s effs f x y -> y }

-- | The idea of the type is
-- @
-- Cases s [eff1, ..., eff_n] f x y = (eff1 f x -> y, ..., eff_n f x -> y)
-- @
-- But internally the list is stored using the data structure @s@ (and the `Any` type)
-- for better time complexity.
newtype Cases
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  (x :: Type)
  (y :: Type)
  = Cases { unCases :: s Any }

{-# INLINE endCases #-}
endCases :: Sequence s => Cases s '[] f x y
endCases = Cases $ nil

{-# INLINE consCases #-}
consCases :: Sequence s => (eff f x -> y) -> Cases s effs f x y -> Cases s (eff ': effs) f x y
consCases f (Cases fs) = Cases $ cons (unsafeCoerce @_ @Any f) fs

{-# INLINE tailCases #-}
tailCases :: Sequence s => Cases s (eff:effs) f x y -> Cases s effs f x y
tailCases (Cases aas) = case view aas of Just (_, as) -> Cases as

{-# INLINE headCases #-}
headCases :: Sequence s => Cases s (eff:effs) f x y -> (eff f x -> y)
headCases (Cases aas) = case view aas of Just (a, _) -> unsafeCoerce @Any @_ a

{-# INLINE hnil #-}
hnil :: forall f s. Sequence s => Algebra_ s '[] f
hnil = Algebra $ endCases

{-# INLINE absurdEffs #-}
absurdEffs :: forall f a b s. Sequence s => Effs s '[] f a -> b
absurdEffs (Effs k) = k endCases

{-# INLINE viewAlgebra #-}
viewAlgebra :: forall eff effs m s. Sequence s
            => Algebra_ s (eff : effs) m
            -> (forall x. eff m x -> m x, Algebra_ s effs m)
viewAlgebra (Algebra aas) = (headCases aas, Algebra $ tailCases aas)

{-# INLINE (:#) #-}
pattern (:#) :: Sequence s => (forall x. eff m x -> m x) -> Algebra_ s effs m -> Algebra_ s (eff : effs) m
pattern a :# as <- (viewAlgebra -> (a,as)) where
  a :# (Algebra as) = Algebra (consCases a as)

class Member eff effs where
  {-# INLINE dispatch #-}
  dispatch :: Sequence s => Algebra_ s effs m -> (forall x. eff m x -> m x)
  dispatch (Algebra cases) = dispatchCases cases

  dispatchCases :: Sequence s => Cases s effs m x y -> (eff m x -> y)
  dispatchCases (Cases cs) = unsafeCoerce @Any (index cs (memberIndex @eff @effs))

  dispatchC :: AlgebraC effs f -> CodeQ (eff f -.> f)

  memberIndex :: Int

instance {-# OVERLAPPING #-} Member eff (eff : effs) where
  {-# INLINE memberIndex #-}
  memberIndex = 0

  dispatchC (c, _) = c

instance Member eff effs => Member eff (eff' : effs) where
  {-# INLINE memberIndex #-}
  memberIndex = 1 + (memberIndex @eff @effs)

  dispatchC (_, cs) = dispatchC @eff @effs cs

-- | @Member sigs sigs'@ holds when every @sig@ which is a 'Member' of in @sigs@
-- is also a 'Member' of @sigs'@.
type family Members (xsigs :: [Effect]) (xysigs :: [Effect]) :: Constraint where
  Members '[] xysigs       = ()
  Members (xsig ': xsigs) xysigs = (Member xsig xysigs, Members xsigs xysigs)

{-
class KnownEffs (effs :: [Effect]) where
  lengthEffs :: Int

instance KnownEffs '[] where
  {-# INLINE lengthEffs #-}
  lengthEffs = 0

instance KnownEffs effs => KnownEffs (eff ': effs) where
  {-# INLINE lengthEffs #-}
  lengthEffs = 1 + lengthEffs @effs
-}

class Append (xs :: [Effect]) (ys :: [Effect]) where
  -- | Concatenating two static algebras.
  heitherC :: AlgebraC xs m -> AlgebraC ys m -> AlgebraC (xs :++ ys) m

{-# INLINE joinCases #-}
joinCases :: Sequence s => Cases s xeffs m x y -> Cases s yeffs m x y
          -> Cases s (xeffs :++ yeffs) m x y
joinCases (Cases xs) (Cases ys) = Cases (append xs ys)

{-# INLINE heither #-}
heither :: forall xeffs yeffs m s. Sequence s
        => Algebra_ s xeffs m -> Algebra_ s yeffs m
        -> Algebra_ s (xeffs :++ yeffs) m
heither (Algebra as) (Algebra bs) = Algebra $ joinCases as bs

instance Append '[] ys where
  heitherC :: AlgebraC '[] m -> AlgebraC ys m -> AlgebraC ('[] :++ ys) m
  heitherC EndAC cbs = cbs

instance Append xs ys => Append (x ': xs) ys where
  heitherC :: AlgebraC (x : xs) m -> AlgebraC ys m -> AlgebraC ((x : xs) :++ ys) m
  heitherC (ca, cas) cbs = (ca, heitherC cas cbs)

infixr 6 #
-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall eff1 eff2 m s . Sequence s
  => Algebra_ s eff1 m
  -> Algebra_ s eff2 m
  -> Algebra_ s (eff1 :++ eff2) m
falg # galg = heither falg galg

class Injects (xeffs :: [Effect]) (xyeffs :: [Effect]) where
  -- | Weakens an algera that works on @xyeffs@ to work on @xeffs@ when
  -- every effect in @xeffs@ is in @xyeffs@.
  weakenAlg :: forall m s . Sequence s => Algebra_ s xyeffs m -> Algebra_ s xeffs m

  -- | Weakens an static algebra.
  weakenAlgC :: AlgebraC xyeffs m -> AlgebraC xeffs m

instance Injects '[] xyeffs where
  {-# INLINE weakenAlg #-}
  weakenAlg _ = hnil

  weakenAlgC _ = EndAC

instance (Member xeff xyeffs, Injects xeffs xyeffs) => Injects (xeff : xeffs) (xyeffs) where
  {-# INLINE weakenAlg #-}
  weakenAlg xyAlg = dispatch xyAlg :# weakenAlg @xeffs @xyeffs xyAlg

  weakenAlgC cxys = (dispatchC @xeff @xyeffs cxys, weakenAlgC @xeffs @xyeffs cxys)

-- | Constructs an algebra for the union containing @xeffs `Union` yeffs@
-- by using an algebra for the union @xeffs@ and aonther for the union @yeffs@.
-- If an effect is in both @xeffs@ and @yeffs@, the algebra for @xeffs@ is used.
{-# INLINE hunion #-}
hunion :: forall xeffs yeffs m s.
     (Injects (yeffs :\\ xeffs) yeffs, Sequence s)
  => Algebra xeffs m -> Algebra yeffs m
  -> Algebra (xeffs `Union` yeffs) m
hunion xalg yalg = heither @xeffs @(yeffs :\\ xeffs) xalg (weakenAlg yalg)

-- | An obvious isomorphism between two representations of an algebra for a single effect @eff@.
{-# INLINE singAlgIso #-}
singAlgIso ::
  Iso  (Algebra '[eff] m) (forall x. eff m x -> m x)

singAlgIso = Iso fwd bwd where
  {-# INLINE fwd #-}
  fwd :: Algebra '[eff] m -> (forall x. eff m x -> m x)
  fwd alg = dispatch alg

  {-# INLINE bwd #-}
  bwd :: (forall x. eff m x -> m x) -> Algebra '[eff] m
  bwd alg = alg :# hnil

-- | A variant of `call'` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callM #-}
callM :: forall eff effs a m s . (Member eff effs, Sequence s)
      => Algebra_ s effs m -> eff m a -> m a
callM oalg = dispatch oalg

-- | A variant of `callJ` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callJM #-}
callJM :: forall eff effs a m s . (Monad m, Member eff effs, Sequence s)
      => Algebra effs m -> eff m (m a) -> m a
callJM oalg x = callM oalg x >>= id

-- | A variant of `callK'` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callKM #-}
callKM :: forall eff effs a b m s . (Monad m, Member eff effs, Sequence s)
      => Algebra effs m -> eff m a -> (a -> m b) -> m b
callKM oalg x k = callM oalg x >>= k


-- Definitions related to staged algebras
-----------------------------------------

-- | In current GHC, polymorphic functions and Template Haskell don't seem to work
-- seamlessly together. Newtype wrappers seem necessary in some cases.
newtype NatTrans f g = NT { at :: forall x. f x -> g x }
type (-.>) = NatTrans

type family AlgebraC (effs :: [Effect]) (f :: Type -> Type) = result | result -> effs f where
  AlgebraC '[] f = EndAC '[] f
  AlgebraC (eff ': effs) f = (CodeQ (eff f -.> f), AlgebraC effs f)

-- | This is just a unit type, but it has two phantom type variables which are useful
-- for type inference.
data EndAC (effs :: [Effect]) (f :: Type -> Type) = EndAC

infixr 6 $#
-- | @alg1 #$ alg2@ joins together code of algebras @alg1@ and @alg2@.
($#) :: forall eff1 eff2 m .
    (Monad m, Append eff1 eff2)
  => AlgebraC eff1 m
  -> AlgebraC eff2 m
  -> AlgebraC (eff1 :++ eff2) m
falg $# galg = heitherC @eff1 @eff2 falg galg

{- INLINE $:# -}
($:#) :: CodeQ (eff m -.> m) -> AlgebraC effs m -> AlgebraC (eff ': effs) m
a $:# as = (a, as)

-- | Static version of `hunion`.
hunionC :: forall xeffs yeffs m a b
  .  ( Append xeffs (yeffs :\\ xeffs), Injects (yeffs :\\ xeffs) yeffs )
  => AlgebraC xeffs m -> AlgebraC yeffs m
  -> AlgebraC (xeffs `Union` yeffs) m
hunionC xalg yalg = heitherC @xeffs @(yeffs :\\ xeffs) xalg (weakenAlgC yalg)