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
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Control.Effect.Internal.Effs.Sum
  ( module Control.Effect.Internal.Effs.Sum.Type
  , (#)
  , (#:)
  , Append (..)
  , hunion
  , hcons
  , hnil
  , Injects (..)
  , Member (..)
  , Members

  , (#$)
  , hunionC
  , GenAlgebra (..)
  )
  where

import Control.Effect.Internal.Effs.Sum.Type
import Data.List.Kind
import GHC.Exts
import Language.Haskell.TH hiding (Type)
import Type.Reflection (Typeable)
import LiftType

infixr 6 #
-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall eff1 eff2 m .
  (Monad m, Append eff1 eff2)
  => Algebra eff1 m
  -> Algebra eff2 m
  -> Algebra (eff1 :++ eff2) m
falg # galg = heither @eff1 @eff2 falg galg

infixr 6 #$
-- | @alg1 #$ alg2@ joins together code of algebras @alg1@ and @alg2@.
(#$) :: forall eff1 eff2 m .
    (Monad m, Append eff1 eff2)
  => AlgebraC eff1 m
  -> AlgebraC eff2 m
  -> AlgebraC (eff1 :++ eff2) m
falg #$ galg = heitherC @eff1 @eff2 falg galg

infixr 6 `hcons`, #:
{- INLINE hcons -}
hcons :: (x h a -> b) -> (Effs xs h a -> b) -> (Effs (x ': xs) h a -> b)
hcons alg algs (Eff x)   = alg x
hcons alg algs (Effs xs) = algs xs

{- INLINE #: -}
(#:) :: (x h a -> b) -> (Effs xs h a -> b) -> Effs (x : xs) h a -> b
(#:) = hcons

{- INLINE hnil -}
hnil :: Effs '[] h a -> b
hnil = absurdEffs


-- | This type class provides operations that support appending
-- two effect lists together.
type  Append :: [Effect] -> [Effect] -> Constraint
class Append xs ys where
  -- | Creates an alebra that can work with either signatures in @xeffs@
  -- or @yeffs@ by using the provided algebras as appropriate.
  heither :: (Effs xs h a -> b) -> (Effs ys h a -> b) -> (Effs (xs :++ ys) h a -> b)

  -- | Concatenating two algebras.
  heitherC :: AlgebraC xs m -> AlgebraC ys m -> AlgebraC (xs :++ ys) m

  -- | Weakens an an operation of type @Effs xeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
  hinl :: Effs xs f a -> Effs (xs :++ ys) f a

  -- | Weakens an an operation of type @Effs yeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
  hinr :: Effs ys f a -> Effs (xs :++ ys) f a

  -- | Attempts to project a value of type @Effs xeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
  houtl :: Effs (xs :++ ys) f a -> Maybe (Effs xs f a)

  -- | Attempts to project a value of type @Effs yeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
  houtr :: Effs (xs :++ ys) f a -> Maybe (Effs ys f a)

instance Append '[] ys where
  {-# INLINE heither #-}
  heither :: (Effs '[] f a -> b) -> (Effs ys f a -> b) -> (Effs ('[] :++ ys) f a -> b)
  heither xalg yalg = yalg

  heitherC :: AlgebraC '[] m -> AlgebraC ys m -> AlgebraC ('[] :++ ys) m
  heitherC EndAC cbs = cbs

  {-# INLINE hinl #-}
  hinl :: Effs '[] f a -> Effs ys f a
  hinl = undefined -- absurdEffs

  {-# INLINE hinr #-}
  hinr :: Effs ys f a -> Effs ys f a
  hinr = id

  {-# INLINE houtl #-}
  houtl :: Effs ys f a -> Maybe (Effs '[] f a)
  houtl = const Nothing

  {-# INLINE houtr #-}
  houtr :: Effs ys f a -> Maybe (Effs ys f a)
  houtr = Just

instance Append xs ys => Append (x ': xs) ys where
  {-# INLINE heither #-}
  heither :: (Effs (x : xs) f a -> b) -> (Effs ys f a -> b) -> Effs ((x : xs) :++ ys) f a -> b
  heither xalg yalg (Eff x)  = xalg (Eff x)
  heither xalg yalg (Effs x) = heither (xalg . Effs) yalg x

  heitherC :: AlgebraC (x : xs) m -> AlgebraC ys m -> AlgebraC ((x : xs) :++ ys) m
  heitherC (ca, cas) cbs = (ca, heitherC cas cbs)

  {-# INLINE hinl #-}
  hinl :: Effs (x : xs) f a -> Effs ((x : xs) :++ ys) f a
  hinl (Eff x)  = Eff x
  hinl (Effs x) = Effs (hinl @xs @ys x)

  {-# INLINE hinr #-}
  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  {-# INLINE houtl #-}
  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  {-# INLINE houtr #-}
  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x

-- | Constructs an algebra for the union containing @xeffs `Union` yeffs@
-- by using an algebra for the union @xeffs@ and aonther for the union @yeffs@.
-- If an effect is in both @xeffs@ and @yeffs@, the algebra for @xeffs@ is used.
{-# INLINE hunion #-}
hunion :: forall xeffs yeffs f a b
  .  ( Append xeffs (yeffs :\\ xeffs), Injects (yeffs :\\ xeffs) yeffs )
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b)
  -> (Effs (xeffs `Union` yeffs) f a -> b)
hunion xalg yalg = heither @xeffs @(yeffs :\\ xeffs) xalg (yalg . injs)

-- | Static version of `hunion`.
hunionC :: forall xeffs yeffs m a b
  .  ( Append xeffs (yeffs :\\ xeffs), Injects (yeffs :\\ xeffs) yeffs )
  => AlgebraC xeffs m -> AlgebraC yeffs m
  -> AlgebraC (xeffs `Union` yeffs) m
hunionC xalg yalg = heitherC @xeffs @(yeffs :\\ xeffs) xalg (weakenAlgC yalg)

-- | @Injects xs ys@ means that all of @xs@ is in @xys@.
-- Some other effects may be in @xys@, so @xs <= xys@.
type  Injects :: [Effect] -> [Effect] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

  -- | Weakens an algera that works on @xyeffs@ to work on @xeffs@ when
  -- every effect in @xeffs@ is in @xyeffs@.
  {-# INLINE weakenAlg #-}
  weakenAlg :: forall m x . (Effs xys m x -> m x) -> (Effs xs  m x -> m x)
  weakenAlg alg = alg . injs

  -- | Weakens an static algebra.
  weakenAlgC :: AlgebraC xys m -> AlgebraC xs m

instance Injects '[] xys where
  {-# INLINE injs #-}
  injs :: Effs '[] f a -> Effs xys f a
  injs = absurdEffs

  weakenAlgC _ = EndAC

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  {-# INLINE injs #-}
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

  weakenAlgC cxys = (lookupAlgC @x @xys cxys, weakenAlgC @xs @xys cxys)

-- | @Member' sig sigs n@ holds when @sig@ is contained in @sigs@ at index @n@.
class Member sig sigs where
  -- | Constructs an operation in the union @Effs sigs f a@ from a single
  -- operation @sig f a@, when @sig@ is in @sigs@.
  inj :: sig f a -> Effs sigs f a

  -- | Attempts to project an operation of type @eff f a@ from a the union @Effs effs f a@,
  -- when @eff@ is in @effs@.
  prj :: Effs sigs f a -> Maybe (sig f a)

  -- | Lookup the algebra code for @sig@ in @AlgebraC sigs f@.
  lookupAlgC :: AlgebraC sigs f -> CodeQ (sig f -.> f)

instance {-# OVERLAPPING #-} Member sig (sig ': sigs) where
  {-# INLINE inj #-}
  inj :: sig f a -> Effs (sig ': sigs) f a
  inj x = Eff x

  {-# INLINE prj #-}
  prj :: Effs (sig : sigs) f a -> Maybe (sig f a)
  prj (Eff x) = Just x
  prj _       = Nothing

  lookupAlgC (c, _) = c

instance (Member sig sigs) => Member sig (sig' : sigs) where
  {-# INLINE inj #-}
  inj x = Effs . inj $ x

  {-# INLINE prj #-}
  prj (Eff _)  = Nothing
  prj (Effs x) = prj x

  lookupAlgC (_, cs) = lookupAlgC @sig @sigs cs


-- | @Member sigs sigs'@ holds when every @sig@ which is a 'Member' of in @sigs@
-- is also a 'Member' of @sigs'@.
type family Members (xsigs :: [Effect]) (xysigs :: [Effect]) :: Constraint where
  Members '[] xysigs       = ()
  Members (xsig ': xsigs) xysigs = (Member xsig xysigs, Members xsigs xysigs)

-- Definitions related to staged algebras
-----------------------------------------

class Typeable effs => GenAlgebra effs where
-- Zhixuan: Somehow this function breaks Haskell Language Server...
  genAlgebra :: AlgebraC effs f -> CodeQ (Algebra effs f)
  genAlgebra acs = unsafeCodeCoerce (genAlgebra' acs)

  genAlgebra' :: AlgebraC effs f -> Q Exp
  genAlgebra' acs = [| \op -> $(unTypeCode $ genAlgebraAux acs (unsafeCodeCoerce [| op |])) |]

  genAlgebraAux :: AlgebraC effs f -> CodeQ (Effs effs f x) -> CodeQ (f x)

instance GenAlgebra '[] where
  genAlgebraAux :: AlgebraC '[] f -> CodeQ (Effs '[] f x) -> CodeQ (f x)
  genAlgebraAux EndAC cx = [|| case $$cx of {} ||]

instance (Typeable (eff ': effs), Typeable eff, GenAlgebra effs) => GenAlgebra (eff ': effs) where
  genAlgebraAux :: AlgebraC (eff : effs) f -> CodeQ (Effs (eff ': effs) f x) -> CodeQ (f x)
  genAlgebraAux (ac, acs) cop = unsafeCodeCoerce $ [|
    case $(unTypeCode cop) of
       Eff (op :: $(liftTypeQ @eff) _ _)  -> $(unTypeCode ac) `at` op
       Effs (op' :: Effs $(liftTypeQ @effs) _ _) -> $(unTypeCode $ genAlgebraAux acs (unsafeCodeCoerce [|op'|]))
   |]