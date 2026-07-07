{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-|
Module      : Control.Effect.Internal.Prog
Description : The datatype for effectful programs
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module exports the type of effectful programs. The library ships with more than one underlying
representations (that provide the same interface) and are controlled by some CPP flags.
Currently the default is the impredicative encoding in "Control.Effect.Internal.Prog.ProgImp".
-}


module Control.Effect.Internal.Prog
  (
    -- * Program datatypes
    Prog,
    Progs,
    type (!),

    -- * Program constructors
    call,
    callJ,
    callK,
    progAlg, ProgAlg#,
    weakenProg,

    -- * Program eliminator
    eval, eval'
  )
  where


import Control.Effect.Internal.Prog.ProgImp
import Control.Effect.Internal.Algebra

-- | A family of programs that may contain at least the effects in @sigs@ in any
-- order, and that returns an @a@
type a ! sigs = Progs sigs a

-- | A family of programs that may contain at least the effects in @sigs@ in any
-- order, and that returns an @a@
type Progs sigs -- ^ A list of effects the program may use
           a    -- ^ The return value of the program
  = forall sigs' . Members sigs sigs' => Prog sigs' a