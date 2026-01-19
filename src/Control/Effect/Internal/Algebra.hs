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
import Data.HFunctor

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

-- * Simple functions manipulating cases and algebras.
--------------------------------------------------------------------------------

-- | Constructing an algebra from its components represented as the `Any` type.
{-# INLINE unsafeAlgebra #-}
unsafeAlgebra :: s Any -> Algebra_ s effs m
unsafeAlgebra cs = Algebra (Cases cs)

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

{-# INLINE htail #-}
htail :: forall eff effs f s. Sequence s => Algebra_ s (eff ': effs) f -> Algebra_ s effs f
htail (Algebra cs) = Algebra $ tailCases cs

{-# INLINE viewAlgebra #-}
viewAlgebra :: forall eff effs m s. Sequence s
            => Algebra_ s (eff : effs) m
            -> (forall x. eff m x -> m x, Algebra_ s effs m)
viewAlgebra (Algebra aas) = (headCases aas, Algebra $ tailCases aas)

{-# INLINE toAlgebraArray #-}
toAlgebraArray :: (Sequence s) => Algebra_ s effs m -> AlgebraArray effs m
toAlgebraArray (Algebra (Cases s)) = Algebra (Cases (seqToArray s))

{-# INLINE fromAlgebraArray #-}
fromAlgebraArray :: (Sequence s) => AlgebraArray effs m -> Algebra_ s effs m
fromAlgebraArray (Algebra (Cases s)) = Algebra (Cases (seqFromArray s))

{-# INLINE (:#) #-}
pattern (:#) :: Sequence s => (forall x. eff m x -> m x) -> Algebra_ s effs m -> Algebra_ s (eff : effs) m
pattern a :# as <- (viewAlgebra -> (a,as)) where
  a :# (Algebra as) = Algebra (consCases a as)


-- * Membership of an effect in effect rows
--------------------------------------------------------------------------------

class Member eff effs where
  {-# INLINE dispatch #-}
  dispatch :: Sequence s => Algebra_ s effs m -> (forall x. eff m x -> m x)
  dispatch (Algebra cases) = dispatchCases cases

  {-# INLINE dispatchCases #-}
  dispatchCases :: Sequence s => Cases s effs m x y -> (eff m x -> y)
  dispatchCases (Cases cs) = unsafeCoerce @Any (index cs (memberIndex @eff @effs))

  dispatchC :: AlgebraC effs f -> CodeQ (eff f -.> f)

  -- TODO (Zhixuan): We are relying on GHC to optimise @(1 + 1 + ... + 0)@ to a numeral @n@
  -- statically. A more reliable way is to make the length a type-level @Nat@ and use @KnownNat@.
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

-- | @unsafeCallM n oalg@ is the @n@-th component of @oalg@.
unsafeCallM :: forall eff effs a m s . Sequence s
            => Int -> Algebra_ s effs m -> eff m a -> m a
unsafeCallM n (Algebra (Cases cs)) = unsafeCoerce @Any @(forall x. eff m x -> m x) (index cs n)

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


-- * Functions that need to be defined by induction on effect rows
--------------------------------------------------------------------------------

{-
-- | TODO (Zhixuan): the whole interface below works by constructing and destructing
-- cases one by one, completely ignoring possible fast indexing. So it runs in quadratic
-- time or higher for all choices of @s@.
class KnownEffs (effs :: [Effect]) where
  -- | The length of @effs@.
  lengthEffs :: Int

  -- | @Cases s effs f x y@ is functorial in @g@ contra-variantly.
  hmapCases :: (Functor f, Functor g, Sequence s)
            => (forall x. f x -> g x) -> Cases s effs g x y -> Cases s effs f x y

  -- | @Cases s effs f x y@ is functorial in @x@ contra-variantly.
  fmapCases1 :: (Sequence s, Functor f)
            => (z -> x) -> Cases s effs f x y -> Cases s effs f z y

  -- | @Cases s effs f x y@ is functorial in @y@ co-variantly.
  fmapCases2 :: (Sequence s)
            => (y -> z) -> Cases s effs f x y -> Cases s effs f x z

  -- | Tabulate a table of cases from a function that handles all cases.
  makeCases :: Sequence s => (Effs s effs f x -> y) -> Cases s effs f x y

instance KnownEffs '[] where
  {-# INLINE lengthEffs #-}
  lengthEffs = 0

  {-# INLINE hmapCases #-}
  hmapCases _ _ = endCases

  {-# INLINE fmapCases1 #-}
  fmapCases1 _ _ = endCases

  {-# INLINE fmapCases2 #-}
  fmapCases2 _ _ = endCases

  {-# INLINE makeCases #-}
  makeCases _ = endCases

instance (HFunctor eff, KnownEffs effs) => KnownEffs (eff ': effs) where
  {-# INLINE lengthEffs #-}
  lengthEffs = 1 + lengthEffs @effs

  {-# INLINE hmapCases #-}
  hmapCases phi cs = consCases (\op -> headCases cs (hmap phi op)) (hmapCases @effs phi (tailCases cs))

  {-# INLINE fmapCases1 #-}
  fmapCases1 f cs = consCases (headCases cs . fmap f) (fmapCases1 @effs f (tailCases cs))

  {-# INLINE fmapCases2 #-}
  fmapCases2 f cs = consCases (f . headCases cs) (fmapCases2 @effs f (tailCases cs))

  {-# INLINE makeCases #-}
  makeCases f = consCases (f . hereEff) (makeCases @effs (f . thereEff))
-}

-- * Concatenating cases and algebras
--------------------------------------------------------------------------------

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

-- * | Definitions related to staged algebras
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

-- * Coproducts (aka open union) of effects
--------------------------------------------------------------------------------

-- | @Effs s [eff1, ..., eff_n]@ is the coproduct of @eff1@, ..., @eff_n@, represented
-- using Church encoding:
-- @
--   Effs s [eff1, ..., eff_n] f x
-- = eff1 f x + ... + eff_n f x
-- = forall y. (eff1 f x -> y, ... , eff_n f x -> y) -> y
-- = forall y. Cases f x y -> y
-- @

{-
newtype Effs
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  (x :: Type)
  = Effs { unEffs :: forall y. Cases s effs f x y -> y }

{-# INLINE absurdEffs #-}
absurdEffs :: forall f a b s. Sequence s => Effs s '[] f a -> b
absurdEffs (Effs k) = k endCases

-- This was called just @Eff@ previously
{-# INLINE hereEff #-}
hereEff :: Sequence s => eff f x -> Effs s (eff ': effs) f x
hereEff op = Effs $ \cs -> headCases cs op

-- This was called just @Effs@ previously
{-# INLINE thereEff #-}
thereEff :: Sequence s => Effs s effs f x -> Effs s (eff ': effs) f x
thereEff op = Effs $ \cs -> unEffs op (tailCases cs)

{-# INLINE tabulateAlgebra #-}
tabulateAlgebra :: (KnownEffs effs, Sequence s)
                => (forall x. Effs s effs m x -> m x) -> Algebra_ s effs m
tabulateAlgebra f = Algebra (makeCases f)

{-# INLINE applyAlgebra #-}
applyAlgebra :: Algebra_ s effs m -> (forall x. Effs s effs m x -> m x)
applyAlgebra (Algebra alg) f = unEffs f alg

instance (Sequence s, KnownEffs effs) => HFunctor (Effs s effs) where
  {-# INLINE hmap #-}
  hmap phi (Effs g) = Effs (g . hmapCases phi)

instance (Sequence s, Functor f, KnownEffs effs) => Functor (Effs s effs f) where
  {-# INLINE fmap #-}
  fmap h (Effs g) = Effs (g . fmapCases1 h)
-}