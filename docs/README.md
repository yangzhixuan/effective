Documentation
=============

The main tutorial path is:

1. [README](../README.md): the core idea, using one `echo` program with
   different handlers.
2. [Handlers](Handlers.md): defining operations and composing handlers.
3. [Pure Teletype](TeletypePure.md): redirecting input and output into pure
   handlers.
4. [Scoped Operations](ScopedOperations.md): scoped effects, censoring, and
   hiding operations.
5. [Profiling](Profiling.md): adding timestamps and profiling scopes.
6. [Members](Members.md): how program and handler signatures line up.

Other checked examples are more topical:

* [Operations](Operations.md): generated operation boilerplate.
* [IO](IO.md): interpreting operations into `Alg IO` and using `ConstIO`.
* [State](State.md), [Error](Error.md), [Nondet](Nondet.md), and
  [Parser](Parser.md): smaller examples for individual effects and handler
  interactions.
* [Graded](Graded.md): graded-effect experiments.

Most files are checked literate Haskell: each `.md` file with executable code
has a matching `.lhs` symlink and is compiled by `cabal test docs`.
