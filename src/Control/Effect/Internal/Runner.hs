{-|
Module      : Control.Effect.Internal.Runner
Description :
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures, MagicHash #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Effect.Internal.Runner where

import Data.List.Kind
import Data.Kind


import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Forward


-- * The primitive types for modular effect handlers

-- | Running a computation @ts m a@, resulting in a value @m b@
type Runner
  :: [Effect]                             -- ^ osigs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : carrier transformer
  -> Type                                 -- ^ a     : input type
  -> Type                                 -- ^ b     : output type
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
newtype Runner osigs ts a b cs = Runner {
  getR :: forall m . cs m => Algebra osigs m -> Apply ts m a -> m b }


-- * Building runners

-- | Runners that don't need any output effects.
{-# INLINE runner' #-}
runner' :: (forall m x . cs m => Apply ts m a -> m b)
        -> Runner osigs ts a b cs
runner' run = Runner (\(_ :: Algebra _ m) -> run @m)

{-# INLINE idRunner #-}
idRunner :: forall sigs cs a.
            Runner sigs '[] a a cs
idRunner = Runner \_ x -> x


type CompRunner# ts1 ts2 =
   ( forall m. Assoc ts1 ts2 m :: Constraint )

{-# INLINE compRunner #-}
compRunner :: forall sigs1 sigs2 ts1 ts2 a1 a2 a3 cs1 cs2.
              CompRunner# ts1 ts2
           => AlgTrans sigs1 sigs2 ts2 cs2
           -> Runner sigs1 ts1 a1 a2 cs1
           -> Runner sigs2 ts2 a2 a3 cs2
           -> Runner sigs2 (ts1 :++ ts2)
                           a1 a3
                           (CompC ts2 cs1 cs2)
compRunner at r1 r2 = Runner \(oalg :: Algebra _ m) ->
    getR r2 oalg .  getR r1 (getAT at @m oalg)

type FuseR# sigs2 osigs1 osigs2 ts1 ts2 =
  ( Injects (osigs1 :\\ sigs2) ((osigs1 :\\ sigs2) `Union` osigs2)
  , Injects osigs2 ((osigs1 :\\ sigs2) `Union` osigs2)
  , Injects osigs1 ((osigs1 :\\ sigs2) :++ sigs2)
  , Append (osigs1 :\\ sigs2) sigs2
  , CompRunner# ts1 ts2 )

{-# INLINE fuseR #-}
fuseR :: forall sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3 cs1 cs2.
          ( ForwardsC cs2 (osigs1 :\\ sigs2) ts2
          , FuseR# sigs2 osigs1 osigs2 ts1 ts2 )
       => AlgTrans sigs2 osigs2 ts2 cs2
       -> Runner osigs1 ts1 a1 a2 cs1
       -> Runner osigs2 ts2 a2 a3 cs2
       -> Runner ((osigs1 :\\ sigs2) `Union` osigs2)
                 (ts1 :++ ts2)
                 a1 a3
                 (CompC ts2 cs1 cs2)
fuseR at2 r1 r2 = Runner \(oalg :: Algebra _ m)  ->
      getR r2 (oalg . injs)
    . getR r1 (weakenAlg @osigs1 @((osigs1 :\\ sigs2) :++ sigs2) $
        heither @(osigs1 :\\ sigs2) @sigs2
          (getAT (fwds @(osigs1 :\\ sigs2) @(ts2))
            (weakenAlg @(osigs1 :\\ sigs2) @_ oalg))
          (getAT at2 (weakenAlg @osigs2 @_ oalg)))

type PassR# sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3 =
   ( Injects osigs1 (osigs1 `Union` osigs2)
   , Injects osigs2 (osigs1 `Union` osigs2)
   , CompRunner# ts1 ts2)

{-# INLINE passR #-}
passR :: forall sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3 cs1 cs2.
      ( ForwardsC cs2 osigs1 ts2
      , PassR# sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3)
      => AlgTrans sigs2 osigs2 ts2 cs2
      -> Runner osigs1 ts1 a1 a2 cs1
      -> Runner osigs2 ts2 a2 a3 cs2
      -> Runner (osigs1 `Union` osigs2)
                (ts1 :++ ts2)
                a1 a3
                (CompC ts2 cs1 cs2)
passR at2 r1 r2 = Runner \(oalg :: Algebra _ m)  ->
      getR r2 (oalg . injs)
    . getR r1 (getAT (fwds @osigs1 @ts2) (oalg . injs))

{-# INLINE weakenR #-}
weakenR :: forall cs' sigs' cs sigs ts a b.
           (forall m. cs' m => cs m, Injects sigs sigs')
        => Runner sigs ts a b cs
        -> Runner sigs' ts  a b cs'
weakenR r1 = Runner \oalg -> getR r1 (oalg . injs)

{-# INLINE weakenREffs #-}
weakenREffs :: forall sigs' cs sigs ts a b.
           (Injects sigs sigs')
        => Runner sigs ts a b cs
        -> Runner sigs' ts a b cs
weakenREffs r1 = Runner \oalg -> getR r1 (oalg . injs)

{-# INLINE weakenRC #-}
weakenRC :: forall cs' cs sigs ts a b.
           (forall m. cs' m => cs m)
        => Runner sigs ts a b cs
        -> Runner sigs ts a b cs'
weakenRC r1 = Runner \oalg -> getR r1 oalg
