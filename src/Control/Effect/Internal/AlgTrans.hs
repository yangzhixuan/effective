{-|
Module      : Control.Effect.Internal.AlgTrans
Description : Transforming effectful operations along carrier transformers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module contains combinators of /algebra transformers/, the core data type
of this library.
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances, AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures, MagicHash, PartialTypeSignatures #-}

module Control.Effect.Internal.AlgTrans where

import Data.List.Kind
import Data.HFunctor ( HFunctor )
import Data.Proxy

import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Prog ( Prog, eval )
import Control.Effect.Internal.Forward

-- * Using algebra transformers and runners

-- | Evaluating a program with an algebra transformer.
{-# INLINE evalAT #-}
evalAT :: forall sigs osigs xsigs ts cs m a.
       ( HFunctor (Effs sigs)
       , cs m
       , Injects osigs xsigs
       , Monad (Apply ts m) )
       => Algebra xsigs m
       -> AlgTrans sigs osigs ts cs
       -> Prog sigs a
       -> Apply ts m a
evalAT oalg alg = eval (getAT alg (oalg . injs))

-- | Evaluating a program with an algebra transformer that outputs no effects.
{-# INLINE evalAT' #-}
evalAT' :: forall m sigs ts cs a.
        ( HFunctor (Effs sigs)
        , cs m
        , Monad (Apply ts m) )
        => AlgTrans sigs '[] ts cs
        -> Prog sigs a
        -> Apply ts m a
evalAT' alg = eval (getAT alg (absurdEffs @m))

-- * Building algebra transformers

-- ** Primitive combinators

-- | Treating an algebra on @m@ as a trivial algebra transformer that only works
-- when the carrier is exactly @m@.
{-# INLINE asAT #-}
asAT :: forall sigs m. Algebra sigs m -> AlgTrans sigs '[] '[] ((~) m)
asAT alg = AlgTrans \_ -> alg

-- | The identity algebra transformer.
{-# INLINE idAT #-}
idAT :: forall sigs cs. AlgTrans sigs sigs '[] cs
idAT = AlgTrans \alg -> alg

-- In this library, constraints with names ending with a hash will always be
-- satisfied matically when the parameters are substituted by concrete values.
-- Users don't need to care about them.

type CompAT# ts1 ts2 sigs1 cs2 = ( forall m . Assoc ts1 ts2 m )

-- | Composing two algebra transformers.
{-# INLINE compAT #-}
compAT :: forall sigs1 sigs2 sigs3 ts1 ts2 cs1 cs2.
          ( CompAT# ts1 ts2 sigs1 cs2 )
       => AlgTrans sigs1 sigs2 ts1 cs1
       -> AlgTrans sigs2 sigs3 ts2 cs2
       -> AlgTrans sigs1 sigs3 (ts1 :++ ts2) (CompC ts2 cs1 cs2)
compAT alg1 alg2 = AlgTrans \(oalg :: Algebra sigs3 m) -> getAT alg1 (getAT alg2 oalg)

-- | Every algebra transformer can be used as one that processes fewer input effects,
-- generating more output effects, and/or with stronger carrier constraints.
{-# INLINE weakenAT #-}
weakenAT :: forall sigs' osigs' cs' sigs osigs cs ts.
            (Injects sigs' sigs, Injects osigs osigs', forall m. cs' m => cs m)
         => AlgTrans sigs  osigs  ts cs
         -> AlgTrans sigs' osigs' ts cs'
weakenAT at = AlgTrans \oalg x -> getAT at (oalg . injs) (injs x)

type CaseTrans# sigs1 sigs2 =
  ( Append sigs1 (sigs2 :\\ sigs1)
  , Injects (sigs2 :\\ sigs1) sigs2 )

-- | Case splitting on the union of two effect rows. Note that `Union` is defined
-- two be @sigs1 ++ (sigs2 :\\ sigs1)@, so if an effect @e@ is both a member of @sigs1@
-- and @sigs2@, it is consumed by the first algebra transformer.
{-# INLINE caseAT #-}
caseAT :: forall sigs1 sigs2 cs1 cs2 osigs ts.
          CaseTrans# sigs1 sigs2
       => AlgTrans sigs1 osigs ts cs1
       -> AlgTrans sigs2 osigs ts cs2
       -> AlgTrans (sigs1 `Union` sigs2) osigs ts (AndC cs1 cs2)
caseAT at1 at2 = AlgTrans \oalg -> hunion (getAT at1 oalg) (getAT at2 oalg)

type CaseTrans'# sigs1 sigs2 = (Append sigs1 sigs2)

-- | Case splitting on the concatenation of two effect rows.
{-# INLINE caseAT' #-}
caseAT' :: forall sigs1 sigs2 cs1 cs2 osigs ts.
          (CaseTrans'# sigs1 sigs2)
        => AlgTrans sigs1 osigs ts cs1
        -> AlgTrans sigs2 osigs ts cs2
        -> AlgTrans (sigs1 :++ sigs2) osigs ts (AndC cs1 cs2)
caseAT' at1 at2 = AlgTrans \oalg -> heither (getAT at1 oalg) (getAT at2 oalg)


-- ** Derived combinators of algebra transformers

-- | Algebra transformer for a single effect.
{-# INLINE algTrans1 #-}
algTrans1 :: forall sig osigs ts cs
          .  (forall m. cs m => Algebra osigs m -> Algebra1 sig (Apply ts m))
          -> AlgTrans '[sig] osigs ts cs
algTrans1 at = AlgTrans \(oalg :: Algebra osigs m) (o :: Effs '[sig] (Apply ts m) x) ->
   case prj @sig o of Just o' -> at oalg o'

-- | Algebra transformer that doesn't need an output effect.
{-# INLINE algTrans' #-}
algTrans' :: forall sigs osigs ts cs
          . (forall m . cs m => Algebra sigs (Apply ts m))
          -> AlgTrans sigs osigs ts cs
algTrans' alg = AlgTrans (\(_ :: Algebra osigs m) -> alg @m)

-- | Replace the carrier constraint of an algebra transformer with a strong one.
{-# INLINE weakenC #-}
weakenC :: forall cs' cs sigs osigs ts.
          (forall m. cs' m => cs m)
       => AlgTrans sigs osigs ts cs
       -> AlgTrans sigs osigs ts cs'
weakenC at = AlgTrans \oalg x -> getAT at oalg x

{-# INLINE weakenCMonad #-}
-- | Drop a @'CompC' ts2 Monad Monad@ carrier constraint down to plain @Monad@.
--
-- The algebra-transformer counterpart of 'Control.Effect.Internal.Runner.weakenRCMonad':
-- the @cs = 'CompC' ts2 Monad Monad@, @cs' = Monad@ specialisation of 'weakenC'.
-- See that function for why this wrapper is needed on GHC 9.14.
weakenCMonad
  :: forall ts2 sigs osigs ts
   . (forall m. Monad m => MonadApply ts2 m)
  => AlgTrans sigs osigs ts (CompC ts2 Monad Monad)
  -> AlgTrans sigs osigs ts Monad
weakenCMonad = weakenC

-- | Replace the carrier constraint @cs@ of an algebra transformer with the conjunction
-- of @cs@ and another constraint @cs'@.
{-# INLINE weakenCAnd #-}
weakenCAnd :: forall cs' cs sigs osigs ts.
          AlgTrans sigs osigs ts cs
       -> AlgTrans sigs osigs ts (AndC cs cs')
weakenCAnd at = AlgTrans \oalg x -> getAT at oalg x

-- | Forget some input effects and add some unused output effects.
{-# INLINE weakenEffs #-}
weakenEffs
       :: (Injects sigs' sigs, Injects osigs osigs')
       => AlgTrans sigs  osigs  ts cs
       -> AlgTrans sigs' osigs' ts cs
weakenEffs = weakenAT

-- | Add some unused output effects.
{-# INLINE weakenOEffs #-}
weakenOEffs :: forall osigs' osigs sigs ts cs.
          Injects osigs osigs'
       => AlgTrans sigs osigs  ts cs
       -> AlgTrans sigs osigs' ts cs
weakenOEffs at = AlgTrans \ oalg x -> getAT at (oalg . injs) x

-- | Forget some input effects of an algebra transformer.
{-# INLINE weakenIEffs #-}
weakenIEffs :: forall sigs' sigs osigs ts cs.
          Injects sigs' sigs
       => AlgTrans sigs  osigs ts cs
       -> AlgTrans sigs' osigs ts cs
weakenIEffs at = AlgTrans \ oalg x -> getAT at oalg (injs x)

type HideAT# sigs sigs' = (Injects (sigs :\\ sigs') sigs)

-- | Forget some input effects @sigs'@.
{-# INLINE hideAT #-}
hideAT :: forall sigs' sigs osigs ts cs.
          HideAT# sigs sigs'
       => AlgTrans sigs  osigs ts cs
       -> AlgTrans (sigs :\\ sigs') osigs ts cs
hideAT at = AlgTrans \ oalg x -> getAT at oalg (injs x)

-- | Case splitting with the same carrier constraint.
{-# INLINE caseATSameC #-}
caseATSameC
       :: forall sigs1 sigs2 cs osigs ts.
          CaseTrans# sigs1 sigs2
       => AlgTrans sigs1 osigs ts cs
       -> AlgTrans sigs2 osigs ts cs
       -> AlgTrans (sigs1 `Union` sigs2) osigs ts cs
caseATSameC at1 at2 = weakenC (caseAT at1 at2)

-- | Case splitting with the same carrier constraint.
{-# INLINE caseATSameC' #-}
caseATSameC'
       :: forall sigs1 sigs2 cs osigs ts.
           CaseTrans'# sigs1 sigs2
        => AlgTrans sigs1 osigs ts cs
        -> AlgTrans sigs2 osigs ts cs
        -> AlgTrans (sigs1 :++ sigs2) osigs ts cs
caseATSameC' at1 at2 = weakenC (caseAT' at1 at2)

type UnionAT# sigs1 sigs2 osigs1 osigs2 =
  ( Injects sigs1 sigs1, Injects sigs2 sigs2
  , Injects osigs1 (osigs1 `Union` osigs2)
  , Injects osigs2 (osigs1 `Union` osigs2)
  , CaseTrans# sigs1 sigs2)

-- | The most general form of case splitting on the union of input effects.
unionAT :: forall sigs1 sigs2 osigs1 osigs2 cs1 cs2 ts.
           UnionAT# sigs1 sigs2 osigs1 osigs2
        => AlgTrans sigs1 osigs1 ts cs1
        -> AlgTrans sigs2 osigs2 ts cs2
        -> AlgTrans (sigs1 `Union` sigs2) (osigs1 `Union` osigs2) ts (AndC cs1 cs2)
unionAT at1 at2 = caseAT (weakenAT @sigs1 at1) (weakenAT @sigs2 at2)

type AppendAT# sigs1 sigs2 osigs1 osigs2 =
  ( Injects sigs1 sigs1, Injects sigs2 sigs2
  , Injects osigs1 (osigs1 :++ osigs2)
  , Injects osigs2 (osigs1 :++ osigs2)
  , CaseTrans'# sigs1 sigs2)

-- | The most general form of case splitting on the concatenation of input effects.
appendAT :: forall sigs1 sigs2 osigs1 osigs2 cs1 cs2 ts.
            AppendAT# sigs1 sigs2 osigs1 osigs2
         => AlgTrans sigs1 osigs1 ts cs1
         -> AlgTrans sigs2 osigs2 ts cs2
         -> AlgTrans (sigs1 :++ sigs2) (osigs1 :++ osigs2) ts (AndC cs1 cs2)
appendAT at1 at2 = caseAT' (weakenAT @sigs1 at1) (weakenAT @sigs2 at2)

type WithFwds# sigs osigs xsigs =
  ( CaseTrans# sigs xsigs
  , Injects xsigs xsigs
  , Injects sigs sigs
  , Injects osigs (osigs `Union` xsigs)
  , Injects xsigs (osigs `Union` xsigs) )

-- | Bypassing some forwardable effects @xsigs@ along an algebra transformer.
-- Members of @xsigs@ that are already in @sigs@ or @xsigs@ are ignored.
{-# INLINE withFwds #-}
withFwds :: forall xsigs sigs osigs ts cs.
            ( ForwardsC cs xsigs ts
            , WithFwds# sigs osigs xsigs )
         => Proxy xsigs
         -> AlgTrans sigs osigs ts cs
         -> AlgTrans (sigs `Union` xsigs) (osigs `Union` xsigs) ts cs
withFwds _ at = weakenC (unionAT at (fwds @xsigs))

type WithFwds'# sigs osigs xsigs =
  ( Append sigs xsigs
  , Injects xsigs xsigs
  , Injects sigs sigs
  , Injects osigs (osigs :++ xsigs)
  , Injects xsigs (osigs :++ xsigs) )

-- | Bypassing a forwardable effect along an algebra transformer.
{-# INLINE withFwds' #-}
withFwds' :: forall xsigs sigs osigs ts cs.
            ( ForwardsC cs xsigs ts
            , WithFwds'# sigs osigs xsigs )
         => Proxy xsigs
         -> AlgTrans sigs osigs ts cs
         -> AlgTrans (sigs :++ xsigs) (osigs :++ xsigs)ts cs
withFwds' _ at = weakenC (appendAT at (fwds @xsigs))

-- ** Fusion-based combinators
type FuseAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2 =
   ( GeneralFuseAT# sigs2 sigs2 sigs1 sigs2 osigs1 osigs2 ts1 ts2
   , Injects sigs2 sigs2 )

infixr 9 `fuseAT`, `fuseAT'`

-- | @fuseAT at1 at2@ composes @at1@ and @at2@ in a way that uses @at2@ maximally:
--    1. all the input effects @sigs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @osigs1@ of @at1@ are intercepted by @sigs2@ as much as possible.
{-# INLINE fuseAT #-}
fuseAT :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs1 cs2.
          FuseAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2
       => (ForwardsC cs1 sigs2 ts1, ForwardsC cs2 (osigs1 :\\ sigs2) ts2)
       => AlgTrans sigs1 osigs1 ts1 cs1
       -> AlgTrans sigs2 osigs2 ts2 cs2
       -> AlgTrans (sigs1 `Union` sigs2)
                   ((osigs1 :\\ sigs2) `Union` osigs2)
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
fuseAT at1 at2 = generalFuseAT (Proxy @sigs2) (Proxy @sigs2) at1 at2

-- | A variant of `fuseAT` that demands the carrier constraint @cs1@ of the
-- first algebra transformer is always satisfied by @Apply ts2 m@ whenever @cs2 m@
-- holds. This is useful for keeping the constraints simple.
{-# INLINE fuseAT' #-}
fuseAT' :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs1 cs2.
          FuseAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2
       => (ForwardsC cs1 sigs2 ts1, ForwardsC cs2 (osigs1 :\\ sigs2) ts2,
           forall m. cs2 m => cs1 (Apply ts2 m))
       => AlgTrans sigs1 osigs1 ts1 cs1
       -> AlgTrans sigs2 osigs2 ts2 cs2
       -> AlgTrans (sigs1 `Union` sigs2)
                   ((osigs1 :\\ sigs2) `Union` osigs2)
                   (ts1 :++ ts2)
                   cs2
fuseAT' at1 at2 = weakenC (fuseAT at1 at2)


infixr 9 `pipeAT`

type PipeAT# sigs2 osigs1 osigs2 ts1 ts2 =
   ( Injects (osigs1 :\\ sigs2) ((osigs1 :\\ sigs2) `Union` osigs2)
   , Injects osigs2 ((osigs1 :\\ sigs2) `Union` osigs2)
   , Injects osigs1 ((osigs1 :\\ sigs2) :++ sigs2)
   , Append (osigs1 :\\ sigs2) sigs2
   , forall m . Assoc ts1 ts2 m )

-- | @pipeAT at1 at2@ composes @at1@ and @at2@ in a way that
--    1. the input effects @sigs2@ of @at2@ are /not/ visible in the input effects of the final result, and
--    2. the output effects @osigs1@ of @at1@ are intercepted by @sigs2@ as much as possible.
{-# INLINE pipeAT #-}
pipeAT :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs2 (osigs1 :\\ sigs2) ts2
          , PipeAT# sigs2 osigs1 osigs2 ts1 ts2 )
       => AlgTrans sigs1 osigs1 ts1 cs1
       -> AlgTrans sigs2 osigs2 ts2 cs2
       -> AlgTrans sigs1
                   ((osigs1 :\\ sigs2) `Union` osigs2)
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)

-- We can define pipeAT as:
--
-- > pipeAT at1 at2 = generalFuse (Proxy @'[]) (Proxy @sigs2) at1 at2
--
-- But this would result in some always true but complex constraints, so let's
-- give a direct definition:

pipeAT at1 at2 = AlgTrans $ \oalg ->
  getAT at1 (weakenAlg $
    heither @(osigs1 :\\ sigs2) @sigs2
      (getAT (fwds @(osigs1 :\\ sigs2) @ts2) (weakenAlg oalg))
      (getAT at2 (weakenAlg oalg)))


infixr 9 `passAT`

type PassAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs2 =
   ( Injects (sigs2 :\\ sigs1) sigs2
   , Injects osigs2 (osigs1 `Union` osigs2)
   , Injects osigs1 (osigs1 `Union` osigs2)
   , Append sigs1 (sigs2 :\\ sigs1)
   , forall m. Assoc ts1 ts2 m )

-- | @passAT at1 at2@ composes @at1@ and @at2@ in a way that
--    1. all the input effects @sigs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @osigs1@ of @at1@ are /not/ intercepted by @sigs2@ at all.
-- If an effect is in the intersection of @sigs1@ and @sigs2@, it is handled by @at1@.
{-# INLINE passAT #-}
passAT :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs1 sigs2 ts1
          , ForwardsC cs2 osigs1 ts2
          , PassAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs2 )
       => AlgTrans sigs1 osigs1 ts1 cs1
       -> AlgTrans sigs2 osigs2 ts2 cs2
       -> AlgTrans (sigs1 `Union` sigs2)
                   (osigs1 `Union` osigs2)
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
passAT at1 at2 = AlgTrans $ \(oalg :: Algebra (osigs1 `Union` osigs2) m) ->
  hunion @sigs1 @sigs2
    (getAT at1 @(Apply ts2 m) (getAT (fwds @osigs1 @ts2) @m (oalg . injs)))
    (getAT (fwds @sigs2 @ts1) (getAT at2 (oalg . injs)))


type PassAT'# sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs2 =
   (  Injects (sigs1 :\\ sigs2) sigs1
    , Injects osigs2 (osigs1 `Union` osigs2)
    , Injects osigs1 (osigs1 `Union` osigs2)
    , Injects (sigs1 `Union` sigs2) (sigs2 `Union` sigs1)
    , Append sigs2 (sigs1 :\\ sigs2)
    , forall m . Assoc ts1 ts2 m )

infixr 9 `passAT'`

-- | @passAT' at1 at2@ is the same as `passAT` except that if an effect is in the
-- intersection of @sigs1@ and @sigs2@, it is handled by @at2@.
{-# INLINE passAT' #-}
passAT' :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs1 cs2.
        ( ForwardsC cs1 sigs2 ts1
        , ForwardsC cs2 osigs1 ts2
        , PassAT'# sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs2 )
        => AlgTrans sigs1 osigs1 ts1 cs1
        -> AlgTrans sigs2 osigs2 ts2 cs2
        -> AlgTrans (sigs1 `Union` sigs2)
                    (osigs1 `Union` osigs2)
                    (ts1 :++ ts2)
                    (CompC ts2 cs1 cs2)
passAT' at1 at2 = AlgTrans $ \(oalg :: Algebra (osigs1 `Union` osigs2) m) ->
  hunion @sigs2 @sigs1
      (getAT (fwds @sigs2 @ts1) (getAT at2 (oalg . injs)))
      (getAT at1 (getAT (fwds @osigs1 @ts2) (oalg . injs)))
  . injs

type GeneralFuseAT# fsigs isigs sigs1 sigs2 osigs1 osigs2 ts1 ts2 =
   ( Append sigs1 (fsigs :\\ sigs1)
   , Injects (fsigs :\\ sigs1) fsigs
   , forall m . Assoc ts1 ts2 m
   , Append (osigs1 :\\ isigs) isigs
   , Injects osigs1 ((osigs1 :\\ isigs) :++ isigs)
   , Injects osigs2             ((osigs1 :\\ isigs) :++ (osigs2 :\\ (osigs1 :\\ isigs)))
   , Injects (osigs1 :\\ isigs) ((osigs1 :\\ isigs) :++ (osigs2 :\\ (osigs1 :\\ isigs)))
   )

{-# INLINE generalFuseAT #-}
-- | `generalFuseAT` subsumes @fuseAT@, @passAT@, and @pipeAT@ by having two type arguments
-- @fsigs@ and @isigs@ such that
--   1. @fsigs@ is a subset of @sigs2@ and it specifies the effects that we want to be
--      forwarded along @ts1@ and exposed by the resulting handler;
--   2. @isigs@ is a subset of @sigs2@ and it specifies the effects that we want to
--      use to intercept the effects produced by @h1@.
-- Therefore @generalFuseAT@ instantiates to
--   1. `fuseAT` with @fsigs ~ sigs2@ and @isigs ~ sigs2@,
--   2. `pipeAT` with @fsigs ~ []@    and @isigs ~ sigs2@,
--   3. `passAT` with @fsigs ~ sigs2@ and @isigs ~ []@.
-- (When both @fsigs@ and @isigs@ are empty, @generalFuse@ becomes useless so there
-- isn't this case defined specially.)
generalFuseAT
  :: forall fsigs isigs sigs1 sigs2 osigs1 osigs2 ts1 ts2 cs1 cs2.
     ( Injects fsigs sigs2
     , Injects isigs sigs2
     , ForwardsC cs1 fsigs ts1
     , ForwardsC cs2 (osigs1 :\\ isigs) ts2
     , GeneralFuseAT# fsigs isigs sigs1 sigs2 osigs1 osigs2 ts1 ts2 )
  => Proxy fsigs
  -> Proxy isigs
  -> AlgTrans sigs1 osigs1 ts1 cs1
  -> AlgTrans sigs2 osigs2 ts2 cs2
  -> AlgTrans (sigs1 `Union` fsigs)
              ((osigs1 :\\ isigs) `Union` osigs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
generalFuseAT _ _ at1 at2 = AlgTrans $ \oalg ->
   hunion @sigs1 @fsigs
     (getAT at1 (weakenAlg $
       heither @(osigs1 :\\ isigs) @isigs
         (getAT (fwds @(osigs1 :\\ isigs) @ts2) (weakenAlg oalg))
         (weakenAlg (getAT at2 (weakenAlg oalg)))))
     (getAT (fwds @fsigs @ts1) (weakenAlg (getAT at2 (weakenAlg oalg))))
