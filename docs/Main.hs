module Main where

import Hedgehog
import Hedgehog.Main

import Error
import Nondet
import State
import Parser
import Handlers
import TeletypePure
import ScopedOperations
import Profiling
import Members
import qualified Operations
-- import Graded ()

main :: IO ()
main = defaultMain $ fmap checkParallel
  [ Error.examples
  , Nondet.examples
  , State.examples
  , Parser.examples
  , Handlers.examples
  , TeletypePure.examples
  , ScopedOperations.examples
  , Profiling.examples
  , Members.examples
  , Operations.examples
  ]
