<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Profiling where

import Prelude hiding (getLine, putStrLn)

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.IO
import Control.Effect.Writer

import Data.HFunctor
import System.CPUTime (getCPUTime)

import Handlers

import Hedgehog (Group(..))
```
-->

Timestamps
----------

Timestamps are often used in conjunction with logging so that the time a message
is logged can be recorded. The traditional way of doing this might be to make
a bespoke `logger` that ensures that there is a timestamp integrated into each
occurence of the log:
```haskell
logger :: String -> () ! [Tell [(Integer, String)], Alg IO]
logger str = do time <- io getCPUTime
                tell [(time, str)]
```
However, this is a case where a reinterpretation might be better where all
instances of `tell` are augmented with the appropriate timestamp.
```haskell
telltime :: forall w a . Monoid w => Handler '[Tell w] '[Tell [(Integer, w)], Alg IO ] '[] a a
telltime = interpret $ \(Tell (w :: w) k) ->
  do time <- io getCPUTime
     tell [(time, w)]
     return k
```
Now a timestamp is added to the start of messages emitted by `tell`:
```console
ghci> handleIO (telltime @[String] |> censors backwards |> writer @[(Integer, [String])] |> censorsPutStrLn id |> teletype ["Hello"]) logShoutEcho
(["Hello"],([(8073080000000,["Entering shouty echo"])],()))
```

A different interface is to use a scoped operation that marks
part of the program as of interest for profiling.
```haskell
type Profile = Scp Profile'
data Profile' k where
  Profile :: String -> k -> Profile' k
  deriving Functor

profile :: Member Profile sigs => String -> Prog sigs a -> Prog sigs a
profile name p = call (Scp (Profile name p))
```

For example, to profile some code `p`, we need to mark it as a code of interest
by writing `profile name p`, where `name` is some identifier that we wish to see
in the log. Then, we must decide which instrument we want to use to measure
what happens to `p`. An instrument measures some quantity of interest, such as
time memory, energy, or bandwidth.

For example, the `timer` handler can be invoked to measure time. This injects
`getCPUTime` operations to measure the time `t` before and `t'` after `p`
is executed. Then `ask` emits a pair consisting of `(name, t' - t)`,
thus showing how much time was spent in `p`.

```haskell
timer :: Handler '[Profile] '[Tell [(String, Integer)], Alg IO] '[] a a
timer = interpretM $ \oalg (Eff (Scp (Profile name p))) ->
  do t  <- eval oalg (io getCPUTime)
     k  <- p
     eval oalg $ do
        t' <- io getCPUTime
        tell [(name, t' - t)]
     return k
```
How exactly `getCPUTime` is measured, and what is done with the `ask` is left
to another handler. This easily allows, for instance, different ways of measuring time
to be implemented, or for logs to be enabled and disabled.

More generally, there may be other instruments that could be used, and indeed
the `timer` handler can alternatively be defined by using `profiler`:
```haskell
timer' :: Handler '[Profile] '[Tell [(String, Integer)], Alg IO] '[] a a
timer' = profiler (flip (-)) (io getCPUTime)
```
A new `profiler f instrument p` will inject the `instrument` before and after
`p` and collect two measurements: one before `p` and another after `p` is
executed. These are then combined by the given function `f` and emitted using
`ask`.
```haskell
profiler :: (HFunctor (Effs osigs), Injects osigs (Tell [(String, b)] ': osigs))
  => (a -> a -> b) -> Prog osigs a -> Handler '[Profile] (Tell [(String, b)] ': osigs) '[] c c
profiler f instrument = interpretM $ \oalg (Eff (Scp (Profile name p))) ->
  do t  <- eval oalg (weakenProg instrument)
     k  <- p
     eval oalg $ do
        t' <- weakenProg instrument
        tell [(name, f t t')]
     return k
```

For our teletype example, we can instrument all of the `getLine` operations
with a profiler as follows:
```haskell
getLineProfile :: Handler '[GetLine] '[Profile, GetLine] '[] a a
getLineProfile = interpret $ \(GetLine k) ->
  profile "getLine" (getLine >>= return . k)
```

<!--
```haskell
examples :: Group
examples = Group "Profiling" []
```
-->

