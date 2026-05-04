{-|
Module      : Control.Effect.CodeGen.Eval
Description : Evaluating meta-programs into object-level code
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains functions for evaluating meta-programs into object-level
programs. The function `stage` is probably the most useful one.
-}

{-# LANGUAGE TemplateHaskell, MonoLocalBinds, MagicHash #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.Effect.CodeGen.Eval where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Down

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Family.Algebraic
import Data.Functor.Identity
import Data.Iso
import Data.HFunctor
import Data.List.Kind

-- | The effects supported by the monad `Gen`.
type GenEffects = [CodeGen, UpOp Identity]

-- | The algebra of `Gen`.
genAlg :: Algebra GenEffects Gen
genAlg o
  | Just (Alg o) <- prj @CodeGen o    = o
  | Just up <- prj @(UpOp Identity) o = bwd upIso (\cm -> return [||runIdentity $$cm||]) up

-- | The effects supported by the monad `GenM m`.
type GenMEffects m = [CodeGenM m, CodeGen, UpOp m]

-- | The algebra on `GenM`.
genMAlg :: forall m. Monad m => Algebra (GenMEffects m) (GenM m)
genMAlg o
  | Just (Alg o) <- prj @(CodeGenM _) o = o
  | Just (Alg o) <- prj @CodeGen      o = specialise o
  | Just up      <- prj @(UpOp m) o     = bwd upIso genDo_ up


type EvalGen# sigs osigs =
  ( HFunctor (Effs (sigs `Union` GenEffects))
  , WithFwds# sigs osigs GenEffects )

-- | Evaluate a program with an algebra transformer, with `Gen` at the bottom
-- of monad transformer stack.
evalGen :: forall sigs osigs ts cs a.
           ( cs Gen
           , Monad (Apply ts Gen)
           , ForwardsC ((~) Gen) GenEffects ts
           , Injects (osigs `Union` GenEffects) GenEffects
           , EvalGen# sigs osigs )
        => AlgTrans sigs osigs ts cs
        -> Prog (sigs `Union` GenEffects) a -> Apply ts Gen a
evalGen at = evalAT genAlg (withFwds (Proxy @GenEffects) (weakenC @((~) Gen) at))

-- | Stage a meta-level program into an object-level monadic computation via `Gen`.
stage :: forall m sigs osigs ts cs a.
         ( cs Gen
         , Monad (Apply ts Gen)
         , ForwardsC ((~) Gen) GenEffects ts
         , Injects (osigs `Union` GenEffects) GenEffects
         , Apply ts Gen $~> m
         , EvalGen# sigs osigs )
      => AlgTrans sigs osigs ts cs
      -> Prog (sigs `Union` GenEffects) (Up a)
      -> Up (m a)
stage alg = down . evalGen alg

type EvalGenM# sigs osigs m =
  ( HFunctor (Effs (sigs `Union` GenMEffects m))
  , WithFwds# sigs osigs (GenMEffects m) )

-- | Evaluate a program with an algebra transformer, with `GenM m` at the bottom
-- of monad transformer stack.
evalGenM :: forall m sigs osigs ts cs a.
            ( cs (GenM m), Monad m
            , Monad (Apply ts (GenM m))
            , ForwardsC ((~) (GenM m)) (GenMEffects m) ts
            , Injects (osigs `Union` GenMEffects m) (GenMEffects m)
            , EvalGenM# sigs osigs m )
         => AlgTrans sigs osigs ts cs
         -> Prog (sigs `Union` GenMEffects m) a -> Apply ts (GenM m) a
evalGenM at = evalAT genMAlg (withFwds (Proxy @(GenMEffects m)) (weakenC @((~) (GenM m)) at))

-- | Stage a meta-level program into an object-level monadic computation via `GenM`.
stageM :: forall m m' sigs osigs ts cs a.
            ( cs (GenM m), Monad m
            , Monad (Apply ts (GenM m))
            , ForwardsC ((~) (GenM m)) (GenMEffects m) ts
            , Injects (osigs `Union` GenMEffects m) (GenMEffects m)
            , Apply ts (GenM m) $~> m'
            , EvalGenM# sigs osigs m )
         => Proxy m
         -> AlgTrans sigs osigs ts cs
         -> Prog (sigs `Union` GenMEffects m) (Up a)
         -> Up (m' a)
stageM _ at = down . evalGenM @m at