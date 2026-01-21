{-|
Module      : Control.Effect.Nondet
Description : Effects for the nondeterminism
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides access to nondeterministic operations and handlers.
The implementation uses @ListT@ by default, offered by "Control.Effect.Nondet.List".
For an implementation based on @LogicT@, import "Control.Effect.Nondet.Logic" instead.
-}

module Control.Effect.Nondet
  ( module Control.Effect.Nondet.Type
  , Choose, Choose_(..), pattern Choose
  , Empty, Empty_(..), pattern Empty

  , ListT (..)
  , list, listC
  , nondet, nondetAT
  , nondetC
  , nondet'
  , backtrack
  , backtrack'
  , chooseByNondet
  , Control.Applicative.Alternative(..)
  ) where

import Prelude hiding (or)

import Control.Effect.Nondet.Type

import Control.Effect.Alternative
import Control.Applicative
import Control.Monad.Trans.List
import Control.Effect.Alternative
import Control.Effect

-- import Control.Effect.Nondet.Logic
import Control.Effect.Nondet.List

chooseByNondet :: Handler '[Choose] '[NondetOr] '[] a a
chooseByNondet = interpretM1 (\oalg (Choose' p q) -> oalg (NondetOr p q) >>= id )