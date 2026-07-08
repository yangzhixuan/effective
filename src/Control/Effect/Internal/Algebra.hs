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

module Control.Effect.Internal.Algebra
  ( module Control.Effect.Internal.Algebra
  , module Data.Sequence.Class
  , CodeQ
  )
  where

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
-- Algebra_ s [eff1, ..., eff_n] f = forall x. (eff1 f x -> f x, ..., eff_n f x -> f x)
-- @
-- The parameter @s@ is a data structure (satisfying the contraint `Sequence`) for
-- better internal representation of the components of the algebra.
newtype Algebra_
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  = Algebra { unAlgebra :: forall x. Case_ s effs f x (f x) }

-- | The default data structure for storing algebras is finger trees.
type Algebra effs f = Algebra_ FT.Seq effs f

-- | Array-based representation is useful for fast accessing after we
-- construct the algebra.
type AlgebraArray effs f = Algebra_ Arr.SmallArray effs f

-- | The idea of the type is
-- @
-- Case_ s [eff1, ..., eff_n] f x y = (eff1 f x -> y, ..., eff_n f x -> y)
-- @
-- But internally the list is stored using the data structure @s@ (and the `Any` type)
-- for better time complexity.
newtype Case_
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  (x :: Type)
  (y :: Type)
  = Case { unCase :: s Any }

type Case effs f x y = Case_ FT.Seq effs f x y

-- * Simple functions manipulating cases and algebras.
--------------------------------------------------------------------------------

-- | Constructing an algebra from its components represented as the `Any` type.
{-# INLINE unsafeAlgebra #-}
unsafeAlgebra :: s Any -> Algebra_ s effs m
unsafeAlgebra cs = Algebra (Case cs)

{-# INLINE endCase #-}
{-# INLINE nilCase #-}
endCase, nilCase :: Sequence s => Case_ s '[] f x y
endCase = Case $ nil
nilCase = endCase

{-# INLINE consCase #-}
consCase :: Sequence s => (eff f x -> y) -> Case_ s effs f x y -> Case_ s (eff ': effs) f x y
consCase f (Case fs) = Case $ cons (unsafeCoerce @_ @Any f) fs

{-# INLINE tailCase #-}
tailCase :: Sequence s => Case_ s (eff:effs) f x y -> Case_ s effs f x y
tailCase (Case aas) = case view aas of Just (_, as) -> Case as

{-# INLINE headCase #-}
headCase :: Sequence s => Case_ s (eff:effs) f x y -> (eff f x -> y)
headCase (Case aas) = case view aas of Just (a, _) -> unsafeCoerce @Any @_ a

{-# INLINE endAlg #-}
{-# INLINE nilAlg #-}
endAlg, nilAlg :: forall f s. Sequence s => Algebra_ s '[] f
endAlg = Algebra $ endCase
nilAlg = endAlg

{-# INLINE tailAlg #-}
tailAlg :: forall eff effs f s. Sequence s => Algebra_ s (eff ': effs) f -> Algebra_ s effs f
tailAlg (Algebra cs) = Algebra $ tailCase cs

{-# INLINE viewCase #-}
viewCase :: forall eff effs m x y s. Sequence s
         => Case_ s (eff : effs) m x y
         -> (eff m x -> y, Case_ s effs m x y)
viewCase cs = (headCase cs, tailCase cs)

{-# INLINE viewAlgebra #-}
viewAlgebra :: forall eff effs m s. Sequence s
            => Algebra_ s (eff : effs) m
            -> (forall x. eff m x -> m x, Algebra_ s effs m)
viewAlgebra (Algebra aas) = (headCase aas, Algebra $ tailCase aas)

{-# INLINE toAlgebraArray #-}
toAlgebraArray :: (Sequence s) => Algebra_ s effs m -> AlgebraArray effs m
toAlgebraArray (Algebra (Case s)) = Algebra (Case (seqToArray s))

infixr 5 :#
{-# INLINE (:#) #-}
pattern (:#) :: Sequence s => (forall x. eff m x -> m x) -> Algebra_ s effs m -> Algebra_ s (eff : effs) m
pattern a :# as <- (viewAlgebra -> (a,as)) where
  a :# (Algebra as) = Algebra (consCase a as)

infixr 5 :#.
{-# INLINE (:#.) #-}
pattern (:#.) :: Sequence s => (forall x. eff m x -> m x) -> (forall x. eff' m x -> m x)
              -> Algebra_ s ([eff, eff']) m
pattern a :#. b <- (viewAlgebra -> (a,viewAlgebra -> (b, _))) where
  a :#. b = a :# (b :# endAlg)

infixr 5 :%
{-# INLINE (:%) #-}
pattern (:%) :: Sequence s => (eff m x -> y) -> Case_ s effs m x y -> Case_ s (eff : effs) m x y
pattern a :% as <- (viewCase -> (a,as)) where
  a :% as = consCase a as

infixr 5 :%.
{-# INLINE (:%.) #-}
pattern (:%.) :: Sequence s => (eff m x -> y) -> (eff' m x -> y)
              -> Case_ s [eff, eff'] m x y
pattern a :%. b <- (viewCase -> (a,viewCase -> (b, _))) where
  a :%. b = a :% (b :% endCase)

-- There is a type-safe way to implement the following (by doing induction on @effs@) but the
-- following gives the correct time complexity.
instance Sequence s => Functor (Case_ s effs f x) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Case_ s effs f x a -> Case_ s effs f x b
  fmap f (Case cs) = Case (fmap (unsafePostcomp f) cs) where
    unsafePostcomp :: forall a b. (a -> b) -> Any -> Any
    unsafePostcomp f x = unsafeCoerce @(Any -> b) @Any $ f . unsafeCoerce @Any @(Any -> a) x

-- * Membership of an effect in effect rows
--------------------------------------------------------------------------------

-- TODO: move the member functions out of the Member class.

class Member eff effs where
  {-# INLINE dispatch #-}
  dispatch :: Sequence s => Algebra_ s effs m -> (forall x. eff m x -> m x)
  dispatch (Algebra cases) = dispatchCases cases

  {-# INLINE dispatchCases #-}
  dispatchCases :: Sequence s => Case_ s effs m x y -> (eff m x -> y)
  dispatchCases (Case cs) = unsafeCoerce @Any (index cs (memberIndex @eff @effs))

  dispatchC :: AlgebraC effs f -> CodeQ (eff f -.> f)

  -- TODO (Zhixuan): We are relying on GHC to optimise @(1 + 1 + ... + 0)@ to a numeral @n@
  -- statically. A more reliable way is to make the length a type-level @Nat@ and use @KnownNat@.
  memberIndex :: Int

instance {-# OVERLAPPING #-} Member eff (eff : effs) where
  {-# INLINE memberIndex #-}
  memberIndex = 0

  dispatchC (c :#$ _) = c

instance Member eff effs => Member eff (eff' : effs) where
  {-# INLINE memberIndex #-}
  memberIndex = 1 + (memberIndex @eff @effs)

  dispatchC (_ :#$ cs) = dispatchC @eff @effs cs

-- | @Member sigs sigs'@ holds when every @sig@ which is a 'Member' of in @sigs@
-- is also a 'Member' of @sigs'@.
type family Members (xsigs :: [Effect]) (xysigs :: [Effect]) :: Constraint where
  Members '[] xysigs       = ()
  Members (xsig ': xsigs) xysigs = (Member xsig xysigs, Members xsigs xysigs)

-- | An obvious isomorphism between two representations of an algebra for a single effect @eff@.
{-# INLINE singAlgIso #-}
singAlgIso :: forall eff m s. Sequence s =>
  Iso  (Algebra_ s '[eff] m) (forall x. eff m x -> m x)
singAlgIso = Iso dispatch singAlg

{-# INLINE singAlg #-}
singAlg :: Sequence s => (forall x. eff m x -> m x) -> Algebra_ s '[eff] m
singAlg alg = alg :# endAlg

-- | A variant of `call` for which the effect is on a given monad rather than the @Prog@ monad.
{-# INLINE callM #-}
callM :: forall eff effs a m s . (Member eff effs, Sequence s)
      => Algebra_ s effs m -> eff m a -> m a
callM oalg = dispatch oalg

callMC :: forall eff effs a m x. (Member eff effs)
       => AlgebraC effs m -> CodeQ (eff m x -> m x)
callMC oalg = [|| at $$(dispatchC oalg) ||]

-- | @unsafeCallM n oalg@ is the @n@-th component of @oalg@.
unsafeCallM :: forall eff effs a m s . Sequence s
            => Int -> Algebra_ s effs m -> eff m a -> m a
unsafeCallM n (Algebra (Case cs)) = unsafeCoerce @Any @(forall x. eff m x -> m x) (index cs n)

-- | A variant of @callJ@ for which the effect is on a given monad rather than the @Prog@ monad.
{-# INLINE callJM #-}
callJM :: forall eff effs a m s . (Monad m, Member eff effs, Sequence s)
      => Algebra_ s effs m -> eff m (m a) -> m a
callJM oalg x = callM oalg x >>= id

-- | A variant of @callK@ for which the effect is on a given monad rather than the @Prog@ monad.
{-# INLINE callKM #-}
callKM :: forall eff effs a b m s . (Monad m, Member eff effs, Sequence s)
      => Algebra_ s effs m -> eff m a -> (a -> m b) -> m b
callKM oalg x k = callM oalg x >>= k

-- * Concatenating cases and algebras
--------------------------------------------------------------------------------

class KnownEffs (xs :: [Effect]) where
  lengthEffs :: Int

instance KnownEffs '[] where
  {-# INLINE lengthEffs #-}
  lengthEffs = 0

instance KnownEffs effs => KnownEffs (eff : effs) where
  {-# INLINE lengthEffs #-}
  lengthEffs = 1 + lengthEffs @effs

{-# INLINE appendCases #-}
appendCases :: Sequence s => Case_ s xeffs m x y -> Case_ s yeffs m x y
          -> Case_ s (xeffs :++ yeffs) m x y
appendCases (Case xs) (Case ys) = Case (append xs ys)

{-# INLINE appendAlg #-}
appendAlg :: forall xeffs yeffs m s. Sequence s
        => Algebra_ s xeffs m -> Algebra_ s yeffs m
        -> Algebra_ s (xeffs :++ yeffs) m
appendAlg (Algebra as) (Algebra bs) = Algebra $ appendCases as bs

{-# INLINE splitCase #-}
splitCase :: forall xeffs yeffs f x y s. (Sequence s, KnownEffs xeffs)
          => Case_ s (xeffs :++ yeffs) f x y
          -> (Case_ s xeffs f x y, Case_ s yeffs f x y)
splitCase (Case s) = let (l, r) = split s (lengthEffs @xeffs)
                     in (Case l, Case r)

{-# INLINE splitAlg #-}
splitAlg :: forall xeffs yeffs m s. (Sequence s, KnownEffs xeffs)
         => Algebra_ s (xeffs :++ yeffs) m
         -> (Algebra_ s xeffs m, Algebra_ s yeffs m)
splitAlg (Algebra (Case s))
  = let (l, r) = split s (lengthEffs @xeffs)
    in (Algebra (Case l), Algebra (Case r))

infixr 6 #
-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall eff1 eff2 m s . Sequence s
  => Algebra_ s eff1 m
  -> Algebra_ s eff2 m
  -> Algebra_ s (eff1 :++ eff2) m
falg # galg = appendAlg falg galg

-- * Subeffects
--------------------------------------------------------------------------------

-- | This class expresses that every effect in @xeffs@ is a member of @xyeffs@.
class Injects (xeffs :: [Effect]) (xyeffs :: [Effect]) where
  -- | Weakens an algera that works on @xyeffs@ to work on @xeffs@ when
  -- every effect in @xeffs@ is in @xyeffs@.
  weakenAlg :: forall m s . Sequence s => Algebra_ s xyeffs m -> Algebra_ s xeffs m

  -- | Weakens an static algebra.
  weakenAlgC :: AlgebraC xyeffs m -> AlgebraC xeffs m

instance Injects '[] xyeffs where
  {-# INLINE weakenAlg #-}
  weakenAlg _ = endAlg

  weakenAlgC _ = EndAC

instance (Member xeff xyeffs, Injects xeffs xyeffs) => Injects (xeff : xeffs) (xyeffs) where
  {-# INLINE weakenAlg #-}
  weakenAlg xyAlg = dispatch xyAlg :# weakenAlg @xeffs @xyeffs xyAlg

  weakenAlgC cxys = dispatchC @xeff @xyeffs cxys :#$ weakenAlgC @xeffs @xyeffs cxys

instance {-# OVERLAPPING #-} Injects (xeff : xeffs) (xeff : xeffs) where
  {-# INLINE weakenAlg #-}
  weakenAlg xyAlg = xyAlg

  weakenAlgC cxys = cxys

-- | Constructs an algebra for the union containing @xeffs `Union` yeffs@
-- by using an algebra for the union @xeffs@ and aonther for the union @yeffs@.
-- If an effect is in both @xeffs@ and @yeffs@, the algebra for @xeffs@ is used.
{-# INLINE unionAlg #-}
unionAlg :: forall xeffs yeffs m s.
     (Injects (yeffs :\\ xeffs) yeffs, Sequence s)
  => Algebra_ s xeffs m -> Algebra_ s yeffs m
  -> Algebra_ s (xeffs `Union` yeffs) m
unionAlg xalg yalg = appendAlg @xeffs @(yeffs :\\ xeffs) xalg (weakenAlg yalg)

-- * | Definitions related to staged algebras
---------------------------------------------

-- | In current GHC, polymorphic functions and Template Haskell don't seem to work
-- seamlessly together. Newtype wrappers seem necessary in some cases.
newtype NatTrans f g = NT { at :: forall x. f x -> g x }
type (-.>) = NatTrans

infixr 5 :#$
data AlgebraC (effs :: [Effect]) (f :: Type -> Type) where
  EndAC :: AlgebraC '[] f
  (:#$) :: CodeQ (eff m -.> m) -> AlgebraC effs m -> AlgebraC (eff ': effs) m

data CaseC (effs :: [Effect]) (f :: Type -> Type) a b where
  EndCC :: CaseC '[] f a b
  (:#%) :: CodeQ (eff f a -> b) -> CaseC effs f a b -> CaseC (eff ': effs) f a b

infixr 6 #$
-- | @alg1 #$ alg2@ joins together code of algebras @alg1@ and @alg2@.
(#$), appendAlgC :: forall eff1 eff2 m .
     AlgebraC eff1 m
  -> AlgebraC eff2 m
  -> AlgebraC (eff1 :++ eff2) m
EndAC #$ galg = galg
(a :#$ as) #$ galg = a :#$ (as #$ galg)

appendAlgC = (#$)

infixr 5 :#.$
{- INLINE $:# -}
pattern (:#.$) :: CodeQ (eff m -.> m) -> CodeQ (eff' m -.> m) -> AlgebraC ([eff, eff']) m
pattern a :#.$ as = (a :#$ (as :#$ EndAC))

-- | Static version of `unionAlg`.
unionAlgC :: forall xeffs yeffs m a b
  .  ( Injects (yeffs :\\ xeffs) yeffs )
  => AlgebraC xeffs m -> AlgebraC yeffs m
  -> AlgebraC (xeffs `Union` yeffs) m
unionAlgC xalg yalg = (#$) @xeffs @(yeffs :\\ xeffs) xalg (weakenAlgC yalg)

-- | To split a static algebra we need to perform induction on |xs|, so
-- we need to create a typeclass.
class HasSplitAlgC (xs :: [Effect]) (ys :: [Effect]) where
  splitAlgC :: AlgebraC (xs :++ ys) m -> (AlgebraC xs m, AlgebraC ys m)

instance HasSplitAlgC '[] ys where
  splitAlgC :: AlgebraC ('[] :++ ys) m -> (AlgebraC '[] m, AlgebraC ys m)
  splitAlgC cbs = (EndAC, cbs)

instance HasSplitAlgC xs ys => HasSplitAlgC (x ': xs) ys where
  splitAlgC :: AlgebraC ((x : xs) :++ ys) m -> (AlgebraC (x : xs) m, AlgebraC ys m)
  splitAlgC (ca :#$ cabs) = let (cas, cbs) = splitAlgC cabs in ((ca :#$ cas), cbs)

-- | Generating a code of an algebra from a static algebra
genAlgebra :: AlgebraC effs f -> CodeQ (Algebra effs f)
genAlgebra EndAC = [|| endAlg ||]
genAlgebra (ac :#$ acs) = [|| at $$ac :# $$(genAlgebra acs) ||]