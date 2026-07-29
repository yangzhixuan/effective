{-|
Module      : Control.Effect.Nondet
Description : Effects for nondeterminism
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides access to nondeterministic operations and handlers.  The
implementation uses @ListT@ by default, offered by "Control.Effect.Nondet.List".
For an implementation based on @LogicT@, import "Control.Effect.Nondet.Logic"
instead.

In this library there are two different modules providing operations for nondeterminism,
this one and "Control.Effect.Alternative".

  1. "Control.Effect.Alternative" provides two operations t`Choose` and t`Empty`. These
     two operations are supposed to directly correspond to the good old `Alternative`
     typeclass of GHC, and there is an instance

     @
       instance (Member Empty effs, Member Choose effs) => Alternative (Prog effs) where ...
     @

     Moreover, t`Choose` is binary scoped operation because `Alternative` does not require
     distributivity of @>>=@ over t`Choose`.

     There is a handler "Control.Effect.Alternative.alternative" that implements t`Choose` and t`Empty`
     using carriries that implement the `Alternative` typeclass.

  2. This module ("Control.Effect.Nondet") provides some additional operations: an algebraic
     nondeterministic choice operation `NondetOr` and a scoped operation `Once`.

The rule of thumb is to use `Control.Effect.Alternative` unless you know that you need t`Once`
or t`NondetOr`. Even if you change your mind later, you can use the handlers `chooseByNondet`
and `nondetByChoose` to convert between `NondetOr` and t`Choose`.
-}

module Control.Effect.Nondet
  ( module Control.Effect.Nondet.Type
  , ListT (..)
  , nondet, nondetC
  , nondet'
  , list, listC
  , backtrack
  , backtrack'
  , nondetAT
  , chooseByNondet
  , nondetByChoose
  , Control.Applicative.Alternative(..)
  ) where

import Prelude hiding (or)

import Control.Applicative
import Control.Effect
import Control.Effect.Nondet.Type
import Control.Effect.Nondet.Alternative
import Control.Effect.Nondet.List

-- | Translate (scoped) `Choose` operations to (algebraic) `Nondet` operations.
-- The scopes delimited by `Choose` is ignored.
chooseByNondet :: Handler '[Choose] '[NondetOr] '[] a a
chooseByNondet = interpretM1 (\oalg (Choose p q) -> nondetOrM oalg p q)

-- | Translate (algebraic) `Nondet` operations to (scoped) `Choose` operations.
nondetByChoose :: Handler '[NondetOr] '[Choose] '[] a a
nondetByChoose = interpretM1 (\oalg (NondetOr p q) -> chooseM oalg (return p) (return q))