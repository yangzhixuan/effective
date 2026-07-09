{-|
Module      : Control.Effect.Nondet.Type
Description : Effects for nondeterministic computations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects and handlers for nondeterministic computations,
including choice and failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.Nondet.Type where

import Control.Effect

$(makeAlg [e| NondetOr :: 2 |])

infixl 6 <+>
{-# INLINE (<+>) #-}
(<+>) :: Member NondetOr effs => Prog effs x -> Prog effs x -> Prog effs x
p <+> q = nondetOr p q

$(makeScp [e| once :: 1 |])

$(makeScp [e| search :: 1 |])
