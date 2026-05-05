{-|
Module      : Control.Effect.Internal.Handler
Description : Handlers and handler combinators
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Internal.Handler where

import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.AlgTrans as LL hiding (weaken)
import Control.Effect.Internal.Runner as LL
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Effs.Sum
import Control.Effect.Internal.Forward

import Data.Kind
import Data.List.Kind
import Data.Functor.Identity
import Data.HFunctor
import Data.Proxy

-- $namingConvention
--
-- Type-variable names for effect signatures follow a consistent convention.
-- A /signature/ (@sig@) is one effect type (e.g. @State Int@); @sigs@ is a
-- list of signatures (e.g. @\'[State Int, Reader String]@).
--
-- Singular and plural forms:
--
-- * @sig@                 — one signature (e.g. in @Member sig sigs@).
-- * @sigs@                — a list of signatures, the input to a handler (default).
-- * @osig@ \/ @osigs@     — single \/ list of /output/ signatures from a handler.
-- * @xsigs@               — e/x/ternal signatures supplied by an outside algebra,
--                          monad, or residual program (e.g. @handleM@, @evalAT@).
-- * @sigs1@, @sigs2@      — operands of a binary type operation (e.g. 'Union', ':\\'),
--                          numbered handlers in compositions (e.g. @generalFuse@),
--                          or paired rows where the old names were @xeffs@ and @yeffs@.
--
-- Combinator-specific prefixes appear only in the signature of the one
-- function they name, distinguishing that function's parameter from the
-- surrounding @sigs@\/@osigs@:
--
-- * @hsigs@ — signatures to /h/ide       ('hide').
-- * @bsigs@ — signatures to /b/ypass     ('bypass').
-- * @fsigs@ — signatures to /f/use       ('generalFuse').
-- * @isigs@ — signatures to /i/nsert     ('generalFuse', paired with @fsigs@).
-- * @rsigs@ — signatures to /r/aise      ('raise').

-- | A t'Handler' will process input effects @sigs@ and produce output effects
-- @osigs@, while working with a list of monad transformers @ts@. The final value
-- will be wrapped with @fs@.

type Handler
  :: [Effect]                             -- ^ sigs  : input effects
  -> [Effect]                             -- ^ osigs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : a list of carrier transformers
  -> Type                                 -- ^ a     : input type
  -> Type                                 -- ^ b     : output type
  -> Type

data Handler sigs osigs ts a b =
  Handler
  { -- | Given @osigs@-effects on any monad @m@, running the monad transformer stack
    -- @ts m x@ into @m (fs x)@.
    hrun :: Runner osigs ts a b Monad

    -- | Transforming @osigs@-effects on any monad @m@ to @sigs@-effects on @ts m@.
  , halg :: AlgTrans sigs osigs ts Monad
  }

-- * Building handlers

-- | A wrapper of the @Handler@ constructor.
{-# INLINE handler #-}
handler
  :: forall sigs osigs ts a b .
     (forall m . Monad m => Algebra osigs m -> Apply ts m a -> m b)
  -> (forall m . Monad m => Algebra osigs m -> Algebra sigs (Apply ts m))
  -> Handler sigs osigs ts a b
handler run alg = Handler (Runner run) (AlgTrans alg)

-- | Given @hrun@ and @halg@ will construct a @Handler sigs osigs ts fs@. This
-- is a simplified version of the @Handler@ constructor where @run@ does
-- not need to be a modular runner.
{-# INLINE handler' #-}
handler'
  :: (forall m . Monad m => Apply ts m a -> m b)
  -> (forall m . Monad m => Algebra osigs m -> Algebra sigs (Apply ts m))
  -> Handler sigs osigs ts a b
handler' run alg = Handler (Runner (\_ -> run)) (AlgTrans (\oalg -> alg oalg))

runner
  :: forall ts a b. (forall m . Monad m => Apply ts m a -> m b)
  -> Handler '[] '[] ts a b
runner run = Handler (Runner (\_ -> run)) (AlgTrans (const absurdEffs))

infixr #:

(#:) :: forall sigs osigs sigs' osigs' ts a b . UnionAT# sigs sigs' osigs osigs'
      => AlgTrans sigs osigs ts Monad
      -> Handler sigs' osigs' ts a b -> Handler (sigs `Union` sigs') (osigs `Union` osigs') ts a b
algs #: Handler hrun halg = Handler (weakenREffs hrun) (weakenC (algs `unionAT` halg))

-- | The identity handler that doesn't transform the effects.
{-# INLINE identity #-}
identity :: Handler sigs sigs '[] a a
identity = Handler LL.idRunner LL.idAT

type Comp# sigs1 ts1 ts2 =
  ( CompRunner# ts1 ts2
  , CompAT# ts1 ts2 sigs1 Monad)

-- | Composing two handlers.
{-# INLINE comp #-}
comp :: ( forall m. Monad m => MonadApply ts1 m
        , forall m. Monad m => MonadApply ts2 m
        , Comp# sigs1 ts1 ts2 )
     => Handler sigs1 sigs2 ts1 a1 a2
     -> Handler sigs2 sigs3 ts2 a2 a3
     -> Handler sigs1 sigs3 (ts1 :++ ts2) a1 a3
comp (Handler r1 a1) (Handler r2 a2) =
  Handler (weakenRC (compRunner a2 r1 r2)) (weakenC (compAT a1 a2))

-- | Weakens a handler from @Handler sigs osigs ts fs@ to @Handler sigs' osigs' ts fs@,
-- when @sigs'@ injects into @sigs@ and @osigs@ injects into @osigs'@.
{-# INLINE weaken #-}
weaken
  :: forall sigs sigs' osigs osigs' ts a b
  . ( Injects sigs' sigs , Injects osigs osigs')
  => Handler sigs  osigs  ts a b
  -> Handler sigs' osigs' ts a b
weaken (Handler run halg)
  = Handler (weakenR @_ @osigs' run) (weakenEffs halg)

type Hide# hsigs sigs osigs = (Injects (sigs :\\ hsigs) sigs, Injects osigs osigs)

-- | Hides the effects in @hsigs@ from the handler. The type argument @hsigs@
-- must be given explicitly since it is only mentioned inside a non-injective
-- type family `:\\`.
{-# INLINE hide #-}
hide
  :: forall hsigs sigs osigs ts a b
  . Hide# hsigs sigs osigs
  => Proxy hsigs
  -> Handler sigs osigs ts a b
  -> Handler (sigs :\\ hsigs) osigs ts a b
hide _ h = weaken h

type Bypass# bsigs sigs osigs =
  ( Append sigs (bsigs :\\ sigs)
  , Injects (bsigs :\\ sigs) bsigs
  , Injects bsigs bsigs
  , Injects sigs sigs
  , Injects osigs (osigs `Union` bsigs)
  , Injects bsigs (osigs `Union` bsigs) )

-- | Operations from the output effect @osigs@ of a handler can be added
-- to the input effect if the handler can forward it.
{-# INLINE bypass #-}
bypass
  :: forall bsigs sigs osigs ts a b
  . ( ForwardsM bsigs ts
    , Bypass# bsigs sigs osigs )
  => Proxy bsigs
  -> Handler sigs osigs ts a b
  -> Handler (sigs `Union` bsigs) (osigs `Union` bsigs) ts a b
bypass _ (Handler run alg) = Handler (weakenR run) (LL.withFwds (Proxy @bsigs) alg)

-- | An algebra transformer that doesn't transform the carrier can be
-- regarded as a handler trivially.
{-# INLINE fromAT #-}
fromAT :: AlgTrans sigs osigs '[] Monad -> Handler sigs osigs '[] a a
fromAT at = handler (\_ -> id) (getAT at)

-- | Interpret @sigs@-effects using @osigs@-effects without transforming the carrier.
-- This is done by using the supplied @rephrase :: Effs sigs m x -> Prog osigs x@
-- parameter to translate @sigs@ into a program that uses @osigs@.
--
-- The function `interpret` is most useful for algebraic operations. For other families
-- of operations, `interpretM` is more useful.
{-# INLINE interpret #-}
interpret
  :: forall sigs osigs a
  .  ( HFunctor (Effs sigs), HFunctor (Effs osigs) )
  => (forall m x . Effs sigs m x -> Prog osigs x)   -- ^ @rephrase@
  -> Handler sigs osigs '[] a a
interpret = fromAT . interpretAT

-- | Interpret @sigs@-effects using @osigs@-effects without transforming the carrier.
-- This is done by using the supplied @rephrase :: Effs sigs m x -> Prog osigs x@
-- parameter to translate @sigs@ into a program that uses @osigs@.
{-# INLINE interpretAT #-}
interpretAT
  :: forall sigs osigs
  .  ( HFunctor (Effs sigs), HFunctor (Effs osigs) )
  => (forall m x . Effs sigs m x -> Prog osigs x)   -- ^ @rephrase@
  -> AlgTrans sigs osigs '[] Monad
interpretAT rephrase = AlgTrans (\oalg op -> eval oalg (rephrase op))

{-# INLINE interpret1 #-}
-- | A special case of `interpret` for one effect @sig@.
interpret1
  :: forall sig osigs a
  .  ( HFunctor sig, HFunctor (Effs osigs) )
  => (forall m x . sig m x -> Prog osigs x)
  -> Handler '[sig] osigs '[] a a
interpret1 rephrase = interpret (\(Eff e) -> rephrase e)

{-# INLINE interpretAT1 #-}
-- | A special case of `interpretAT` for one effect @sig@.
interpretAT1
  :: forall sig osigs
  .  ( HFunctor sig, HFunctor (Effs osigs) )
  => (forall m x . sig m x -> Prog osigs x)
  -> AlgTrans '[sig] osigs '[] Monad
interpretAT1 rephrase = interpretAT (\(Eff e) -> rephrase e)

{-# INLINE interpretM #-}
-- | A generalisation of `interpret` for non-algebraic operations.
-- The result of @interpretM mrephrase@ is a new @Handler sigs osigs '[] '[]@.
-- This is created by using the supplied @mrephrase :: Algebra osigs m -> Algebra sigs m@ parameter.
-- to rephrase @sigs@ into an arbitrary monad @m@.
-- When @mrephrase@ is used, it is given an @oalg :: Algebra osigs m@
-- parameter that makes it possible to create a value in @m@.
interpretM
  :: forall sigs osigs a .
     (forall m . Monad m => Algebra osigs m -> Algebra sigs m)   -- ^ @mrephrase@
  -> Handler sigs osigs '[] a a
interpretM mrephrase
  = handler @sigs @osigs @'[] (const id) mrephrase

{-# INLINE interpretM1 #-}
interpretM1
  :: forall sig osigs a.
     (forall m . Monad m => Algebra osigs m
                         -> Algebra1 sig m)   -- ^ @mrephrase@
  -> Handler '[sig] osigs '[] a a
interpretM1 mrephrase
  = handler @'[sig] @osigs @'[] (const id) (\oalg (Eff op) -> mrephrase oalg op)

-- | Case splitting on the union of two effect rows. Note that `Union` is defined
-- two be @sigs1 ++ (sigs2 :\\ sigs1)@, so if an effect @e@ is both a member of @sigs1@
-- and @sigs2@, it is consumed by the first handler.
{-# INLINE caseHdl #-}
caseHdl :: forall sigs1 sigs2 osigs ts a1 a2 a3 a4.
          CaseTrans# sigs1 sigs2
       =>  Handler sigs1 osigs ts a1 a2
       ->  Handler sigs2 osigs ts a3 a4
       -> Handler (sigs1 `Union` sigs2) osigs ts a1 a2
caseHdl (Handler r1 a1) (Handler _ a2) = Handler r1 (caseATSameC a1 a2)

{-# INLINE unionHdl #-}
-- | Case splitting on the union of two effect rows, and the two handlers may output
-- different effects.
unionHdl :: forall sigs1 sigs2 osigs1 osigs2 ts a1 a2 a3 a4.
          UnionAT# sigs1 sigs2 osigs1 osigs2
       =>  Handler sigs1 osigs1 ts a1 a2
       ->  Handler sigs2 osigs2 ts a3 a4
       -> Handler (sigs1 `Union` sigs2) (osigs1 `Union` osigs2) ts a1 a2
unionHdl (Handler r1 a1) (Handler _ a2) = Handler (weakenR r1) (weakenC (unionAT a1 a2))

{-# INLINE appendHdl #-}
-- | Case splitting on the append of two effect rows, and the two handlers may output
-- different effects.
appendHdl :: forall sigs1 sigs2 osigs1 osigs2 ts a1 a2 a3 a4.
          AppendAT# sigs1 sigs2 osigs1 osigs2
       =>  Handler sigs1 osigs1 ts a1 a2
       ->  Handler sigs2 osigs2 ts a3 a4
       -> Handler (sigs1 :++ sigs2) (osigs1 :++ osigs2) ts a1 a2
appendHdl (Handler r1 a1) (Handler _ a2) = Handler (weakenR r1) (weakenC (appendAT a1 a2))

-- * Fusion-based handler combinators

infixr 9 `fuse`, |>

{-# INLINE fuse #-}
{-# INLINE (|>) #-}
fuse, (|>)
  :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3
  . ( forall m . Monad m => MonadApply ts1 m
    , forall m . Monad m => MonadApply ts2 m
    , ForwardsM sigs2 ts1
    , ForwardsM (osigs1 :\\ sigs2) ts2
    , LL.FuseAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2
    , LL.FuseR# sigs2 osigs1 osigs2 ts1 ts2
    )
  => Handler sigs1 osigs1 ts1 a1 a2   -- ^ @h1@
  -> Handler sigs2 osigs2 ts2 a2 a3   -- ^ @h2@
  -> Handler (sigs1 `Union` sigs2)
             ((osigs1 :\\ sigs2) `Union` osigs2)
             (ts1 :++ ts2)
             a1 a3
-- | Fusing handlers `h1 :: Handler sigs1 osigs1 ts1 fs1` and `h2 :: Handler sigs2
-- osigs2 ts2 fs2` results in a handler with the composed transformer stack @ts1 :++ ts2@
-- that can deal with the effects of `sigs1` and those of `sigs2`, as well as deal
-- with the effects @osigs1@ produced by @h1@ using @h2@ appropriately. More
-- precisely, if a member of @osigs1@ is in `sigs2`, then it is consumed by `h2`;
-- if it is not in `sigs2`, it can only be re-produced by the fused handler and in
-- this case they have to be forwardable by @ts2@.
--
-- Moreover, the effects @sigs2@ are handled by @h2@ so they must be forwardable by @ts1@.
fuse (Handler run1 malg1) (Handler run2 malg2)
  = Handler (weakenRC (LL.fuseR malg2 run1 run2)) (weakenC (LL.fuseAT malg1 malg2))

-- | A synonym for `fuse`.
(|>) = fuse


infixr 9 `pipe`, ||>

{-# INLINE pipe #-}
{-# INLINE (||>) #-}

pipe, (||>)
  :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3
  . ( forall m . Monad m => MonadApply ts1 m
    , forall m . Monad m => MonadApply ts2 m
    , LL.PipeAT# sigs2 osigs1 osigs2 ts1 ts2
    , LL.FuseR# sigs2 osigs1 osigs2 ts1 ts2
    , ForwardsM (osigs1 :\\ sigs2) ts2
    )
  => Handler sigs1 osigs1 ts1 a1 a2 -- ^ Handler @h1@
  -> Handler sigs2 osigs2 ts2 a2 a3    -- ^ Handler @h2@
  -> Handler sigs1
             ((osigs1 :\\ sigs2) `Union` osigs2)
             (ts1 :++ ts2)
             a1 a3
-- Piping two handlers @h1@ and @h2@ is a relaxed version of composing two
-- handlers (`comp`). The output effects of @h1@ doesn't have to exactly match the
-- input effects of @h2@ (as required by `comp`). Instead, if an output effect
-- produced by @h1@ is not handled by @h2@, it will be re-produced by @pipe h1 h2@.
pipe (Handler run1 malg1)  (Handler run2 malg2)
  = Handler (LL.weakenRC (LL.fuseR malg2 run1 run2)) (LL.weakenC (LL.pipeAT malg1 malg2))

-- | A synonym for 'pipe'
(||>) = pipe


type Pass# sigs1 sigs2 osigs1 osigs2 ts1 ts2 =
  ( PassAT# sigs1 sigs2 osigs1 osigs2 ts1 ts2 Monad
  , FuseR# sigs2 osigs1 osigs2 ts1 ts2
  , Injects (osigs1 `Union` osigs2) (osigs1 `Union` osigs2))

-- | @pass h1 h2@ results in a handler that recognises all the effects recognised by
-- @h1@ and @h2@, but unlike @fuse h1 h2@, @pass@ doesn't use @h2@ to intercept the
-- effects produced by @h1@.
pass :: forall sigs1 sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3.
        ( forall m. Monad m => MonadApply ts2 m
        , ForwardsM  sigs2 ts1
        , ForwardsM osigs1 ts2
        , Pass# sigs1 sigs2 osigs1 osigs2 ts1 ts2)
     => Handler sigs1 osigs1 ts1 a1 a2         -- ^ Handler @h1@
     -> Handler sigs2 osigs2 ts2 a2 a3         -- ^ Handler @h2@
     -> Handler (sigs1 `Union` sigs2)
                (osigs1 `Union` osigs2)
                (ts1 :++ ts2)
                a1 a3
pass (Handler r1 a1) (Handler r2 a2)
  = Handler (LL.weakenR (LL.passR a2 r1 r2)) (LL.weakenC (LL.passAT a1 a2))

{-# INLINE generalFuse #-}
-- | `generalFuse` subsumes @fuse@, @pass@, and @pipe@ by having two type arguments
-- @fsigs@ and @isigs@ such that
--   1. @fsigs@ is a subset of @sigs2@ and it specifies the effects that we want to be
--      forwarded along @ts1@ and exposed by the resulting handler;
--   2. @isigs@ is a subset of @sigs2@ and it specifies the effects that we want to
--      use to intercept the effects produced by @h1@.
-- Therefore @generalFuse@ instantiates to
--   1. `fuse` with @fsigs ~ sigs2@ and @isigs ~ sigs2@,
--   2. `pipe` with @fsigs ~ []@    and @isigs ~ sigs2@,
--   3. `pass` with @fsigs ~ sigs2@ and @isigs ~ []@.
-- (When both @fsigs@ and @isigs@ are empty, @generalFuse@ becomes useless so there
-- isn't this case defined specially.)
generalFuse
  :: forall fsigs isigs sigs1 sigs2 osigs1 osigs2 ts1 ts2 a1 a2 a3.
     ( forall m . Monad m => MonadApply ts1 m
     , forall m . Monad m => MonadApply ts2 m
     , Injects fsigs sigs2
     , Injects isigs sigs2
     , ForwardsM fsigs ts1
     , ForwardsM (osigs1 :\\ isigs) ts2
     , GeneralFuseAT# fsigs isigs sigs1 sigs2 osigs1 osigs2 ts1 ts2
     , LL.FuseR# sigs2 osigs1 osigs2 ts1 ts2
     , Injects osigs2 osigs2
     )
  => Proxy fsigs -> Proxy isigs
  -> Handler sigs1 osigs1 ts1 a1 a2
  -> Handler sigs2 osigs2 ts2 a2 a3
  -> Handler (sigs1 `Union` fsigs)
             ((osigs1 :\\ isigs) `Union` osigs2)
             (ts1 :++ ts2)
             a1 a3
generalFuse p1 p2 (Handler r1 a1) (Handler r2 a2)
  = Handler (LL.weakenRC (LL.fuseR (weakenIEffs @isigs a2) r1 r2))
            (LL.weakenC (LL.generalFuseAT p1 p2 a1 a2))

recall
  :: forall rsigs sigs osigs ts a b .
     ( Append rsigs (sigs :\\ rsigs)
     , Injects osigs (rsigs `Union` osigs)
     , Injects rsigs (rsigs `Union` osigs)
     , Injects rsigs sigs
     , Injects (sigs :\\ rsigs) sigs
     , ForwardsM rsigs ts
     , forall m . Monad m => MonadApply ts m
     )
  => Proxy rsigs -> Handler sigs osigs ts a b
  -> Handler (rsigs `Union` sigs) (rsigs `Union` osigs) ts a b
recall _ (Handler run halg) =
  Handler (weakenR @_ @(rsigs `Union` osigs) run)
          (AlgTrans $ \(oalg :: Algebra (rsigs `Union` osigs) m) ->
              heither @rsigs @(sigs :\\ rsigs)
                -- sticky branch: consume via h, then recall downstream
                (\opR -> do
                    r <- getAT halg (weakenAlg @osigs oalg) (injs @rsigs @sigs opR)
                    _ <- getAT (fwds @rsigs @ts) (weakenAlg @rsigs oalg) opR
                    pure r)
                -- non-sticky: just delegate to h
                (\opE -> getAT halg (weakenAlg @osigs oalg)
                                 (injs @(sigs :\\ rsigs) @sigs opE)))


-- * Using handlers

-- | @handle h p@ uses the handler @h@ to evaluate the program @p@. All of the
-- effects @sigs@ in the program must be recognised by the handler,
-- and the handler must produce no effects.

{-# INLINE handle #-}
handle :: forall sigs ts fs a b .
  (Monad (Apply ts Identity), HFunctor (Effs sigs))
  => Handler sigs '[] ts a b      -- ^ Handler @h@ with no output effects
  -> Prog sigs a                  -- ^ Program @p@ with effects @sigs@
  -> b
handle (Handler run halg)
  = runIdentity . LL.getR run absurdEffs . eval (getAT halg (absurdEffs @Identity))
  -- = runIdentity . LL.getR run absurdEffs . evalAT' @Identity halg

type HandleM# sigs xsigs =
  ( Injects (xsigs :\\ sigs) xsigs
  , Append sigs (xsigs :\\ sigs)
  , HFunctor (Effs (sigs `Union` xsigs)))

-- | @handleM xalg h p@ uses the handler @h@ to evaluate the program @p@ into some
-- monad @m@ (e.g. the @IO@ monad). The monad @m@ may come with some effects @xsigs@
-- and the program can make use of these effects, in addition to the effects @sigs@
-- handled by the handler @h@. The effects @xsigs@ on @m@ must be forwardable by
-- the transformer stack @ts@.
-- (When an effect is both in @sigs@ and @xsigs@, it is handled by @h@).
handleM :: forall sigs osigs xsigs m ts fs a b .
  ( Monad m
  , Monad (Apply ts m)
  , ForwardsM xsigs ts
  , Injects osigs xsigs
  , HandleM# sigs xsigs
  )
  => Algebra xsigs m                 -- ^ Algebra @xalg@ for external effects @xsigs@
  -> Handler sigs osigs ts a b       -- ^ Handler @h@
  -> Prog (sigs `Union` xsigs) a     -- ^ Program @p@ that contains @xsigs@
  -> m b
handleM xalg (Handler run halg)
  = getR run @m (xalg . injs)
  . eval (hunion @sigs @xsigs (getAT halg (xalg . injs)) (getAT (fwds @_ @ts) xalg))

-- | A variant of @handleM@ where the program doesn't explicitly use the effect
-- @xsigs@ on the monad @m@, but may output some effects @osigs@ ⊆ @xsigs@. Therefore
-- the transformer stack @ts@ doesn't have to forward the effects @xsigs@.
handleM' :: forall sigs osigs xsigs m ts a b .
  ( Monad m
  , Monad (Apply ts m)
  , Injects osigs xsigs
  , HFunctor (Effs sigs) )
  => Algebra xsigs m                 -- ^ Algebra @xalg@ for external effects @xsigs@
  -> Handler sigs osigs ts a b       -- ^ Handler @h@
  -> Prog sigs a
  -> m b
handleM' xalg (Handler run halg)
  = getR run @m (xalg . injs) . eval (getAT halg (xalg . injs))

-- | `handleMFwds` is a middle ground between `handleM` and `handleM'`: a type argument
-- @sigs2@ is given explicitly to specify the subset of @sigs1@ that the program really
-- needs (and must be forwardable by @ts@).
handleMFwds :: forall sigs2 sigs osigs sigs1 m ts a b .
  ( Monad m
  , Monad (Apply ts m)
  , Injects osigs sigs1
  , Injects sigs2 sigs1
  , ForwardsM sigs2 ts
  , HandleM# sigs sigs2 )
  => Proxy sigs2                     -- ^ @sigs2@ can't be inferred so must be given explicitly
  -> Algebra sigs1 m                 -- ^ Algebra @xalg@ for external effects @sigs1@
  -> Handler sigs osigs ts a b        -- ^ Handler @h@
  -> Prog (sigs `Union` sigs2) a
  -> m b
handleMFwds _ xalg (Handler run halg)
  = getR run @m (xalg . injs)
  . eval (hunion @sigs @sigs2 (getAT halg (xalg . injs))
                              (getAT (fwds @_ @ts) (xalg . injs)))

type HandleP# sigs xsigs =
  ( HandleM# sigs xsigs
  , HFunctor (Effs xsigs)
  , Monad (Prog xsigs) )

-- | @handleP h p@ uses the handler @h@ to evaluate the program @p@, resulting
-- in a program with effects @xsigs@ that are not recognised by @h@.
-- If an effect is both in @sigs@ and @xsigs@, it is handled by @h@.
handleP :: forall sigs osigs xsigs ts fs a b .
  ( Monad (Apply ts (Prog xsigs))
  , ForwardsM xsigs ts
  , Injects osigs xsigs
  , HandleP# sigs xsigs )
  => Handler sigs osigs ts a b        -- ^ Handler @h@
  -> Prog (sigs `Union` xsigs) a     -- ^ Program @p@ that contains @xsigs@
  -> Prog xsigs b
handleP = handleM progAlg

-- | A variant of @handleP'@ where the program only uses the effects provided
-- by the handler @h@.
handleP' :: forall sigs osigs xsigs ts fs a b .
  ( Monad (Apply ts (Prog xsigs))
  , Forwards xsigs ts
  , Injects osigs xsigs
  , HFunctor (Effs sigs)
  , HFunctor (Effs xsigs) )
  => Handler sigs osigs ts a b       -- ^ Handler @h@
  -> Prog sigs a                     -- ^ Program @p@ handled by @h@
  -> Prog xsigs b

handleP' = handleM' progAlg


type HandleMApp# sigs xsigs =
  ( HFunctor (Effs (sigs :++ xsigs))
  , Append sigs xsigs )

-- | @handleMApp xalg h p@ is a variant of `handleM` where @sigs `Union` xsigs@ is replaced
-- by '(:++)'.
-- In most cases, you should just use `handleM` but sometimes limitations regarding class
-- constraints in GHC necessitate the use of @handleMApp@ (for example, in `Control.Effect.HOStore.Safe.handleHSM`.)

handleMApp :: forall sigs osigs xsigs m ts fs a b .
  ( Monad m
  , Monad (Apply ts m)
  , ForwardsM xsigs ts
  , Injects osigs xsigs
  , HandleMApp# sigs xsigs )
  => Algebra xsigs m                -- ^ Algebra @xalg@ for external effects @xsigs@
  -> Handler sigs osigs ts a b       -- ^ Handler @h@
  -> Prog (sigs :++ xsigs) a        -- ^ Program @p@ that contains @xsigs@
  -> m b
handleMApp xalg (Handler run halg)
  = getR run @m (xalg . injs)
  . eval (heither @sigs @xsigs (getAT halg (xalg . injs)) (getAT (fwds @_ @ts) xalg))

-- | @handlePApp h p@ is a variant of `handleP` where @sigs `Union` xsigs@ is replaced
-- by simply '(:++)'.
-- In most cases, you should just use `handleP` but sometimes limitations regarding class
-- constraints in GHC necessitate the use of @handlePApp@ (for example, in `Control.Effect.HOStore.Safe.handleHSM`.)
handlePApp :: forall sigs osigs xsigs ts fs a b .
  ( ForwardsM xsigs ts
  , Monad (Apply ts (Prog xsigs))
  , Injects osigs xsigs
  , HandleMApp# sigs xsigs
  , HFunctor (Effs xsigs)
  ) => Handler sigs osigs ts a b        -- ^ Handler @h@
  -> Prog (sigs :++ xsigs) a           -- ^ Program @p@ that contains @xsigs@
  -> Prog xsigs b
handlePApp = handleMApp progAlg
