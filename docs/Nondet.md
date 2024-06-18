```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Nondet where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Cut
import Control.Effect.Nondet
import Control.Monad (guard)


import Hedgehog

knapsack
  :: Int -> [Int] -> Prog' '[Stop, Or] [Int]
knapsack w vs
  | w <  0    = stop
  | w == 0    = return []
  | otherwise = do v <- select vs
                   vs' <- knapsack (w - v) vs
                   return (v : vs')


-- `list` is not a modular handler and uses `eval` directly
example_Nondet1 :: Property
example_Nondet1 = property $ (list $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- `nondet` is a modular handler but does not
-- handle `once`. Here it is immaterial because `once`
-- does not appear in the program
example_Nondet2 :: Property
example_Nondet2 = property $ (handle nondetT $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- `backtrack` is modular, and is furthermore simply
-- the joining of the nondet algebra with an algebra
-- for once
example_backtrack1 :: Property
example_backtrack1 = property $ (handle backtrackT $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- onceEx :: (Member Or sig, Member Once sig) => Prog sig I
example_backtrack2 :: Property
example_backtrack2 = property $ handle backtrackT p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))
-- ghci> exampleOnce
-- [1,2]

example_Once' :: Property
example_Once' = property $ handle onceNondet' p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))
-- ghci> exampleOnce'
-- [1,2]

example_Once'' :: Property
example_Once'' = property $ handle onceNondet' p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))

example_Once''' :: Property
example_Once''' = property $ handle onceNondet' p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))

-- queens n = [c_1, c_2, ... , c_n] where
--   (i, c_i) is the (row, column) of a queen
queens :: Int -> Prog' '[Stop, Or] [Int]
queens n = go [1 .. n] []
  where
    -- `go cs qs` searches the rows `cs` for queens that do
    -- not threaten the queens in `qs`
    go :: [Int] -> [Int] -> Prog' [Stop, Or] [Int]
    go [] qs =  return qs
    go cs qs =  do (c, cs') <- selects cs
                   guard (noThreat qs c 1)
                   go cs' (c:qs)

    -- `noThreat qs r c` returns `True` if there is no threat
    -- from a queen in `qs` to the square given by `(r, c)`.
    noThreat :: [Int] -> Int -> Int -> Bool
    noThreat []      c r  = True
    noThreat (q:qs)  c r  = abs (q - c) /= r && noThreat qs c (r+1)

example_queens = property $
  length (list (queens 8)) === 92

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
