<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Operations where

import Prelude hiding (getLine, putStrLn)

import Control.Effect
import Hedgehog
```
-->

Defining Operations
===================

The operation generators in `effective` turn a compact operation signature into
boilerplate that includes an effect signature, a pattern synonym, and
a smart constructor for programs.

For example, the operations for [teletype](../README.md) are generated like this:
```haskell
$(makeGen [e| getLine  :: String |])
$(makeGen [e| putStrLn :: String -> () |])
```
The quoted type is not the full type of the generated smart constructor. It is
an algebraic signature of the operation, which is broken down into a
parameter and an arity. The result type is the arity that says what value the
operation returns to the program; the parameters, if any, come before the arity
are data stored in the operation.

Thus `getLine :: String` says that `getLine` has no parameters and returns a
`String`, which is its arity, while `putStrLn :: String -> ()` says that
`putStrLn` stores a `String` parameter and returns `()` as its arity.

These operations have corresponding type signatures, where `GetLine` and `PutStrLn`
are effect types that which annotate the effect signature `sigs` of a `Prog
sigs` type that has the appropriate arity:
```haskell ignore
getLine  :: Member GetLine sigs  => Prog sigs String
putStrLn :: Member PutStrLn sigs => String -> Prog sigs ()
```

The quoted types also generate pattern synonyms that can be used when writing
handlers:
```haskell
teletypePure :: String -> Handler '[GetLine, PutStrLn] '[] '[] a a
teletypePure input =
  interpret
    (\case GetLine k     -> return (k input)
           PutStrLn _ k  -> return k)
```


Under the Hood
---------------

Ignoring the extra named-operation variants, the first splice is equivalent to:
```haskell ignore
type GetLine = Alg GetLine_

data GetLine_ k = GetLine_ (String -> k)
  deriving Functor

pattern GetLine :: Member GetLine sigs => (String -> k) -> Effs sigs m k
pattern GetLine k <- (prj -> Just (Alg (GetLine_ k)))
  where GetLine k = inj (Alg (GetLine_ k))

getLine :: Member GetLine sigs => Prog sigs String
getLine = call (Alg (GetLine_ id))
```

The second splice is equivalent to:
```haskell ignore
type PutStrLn = Alg PutStrLn_

data PutStrLn_ k = PutStrLn_ String k
  deriving Functor

pattern PutStrLn :: Member PutStrLn sigs => String -> k -> Effs sigs m k
pattern PutStrLn str k <- (prj -> Just (Alg (PutStrLn_ str k)))
  where PutStrLn str k = inj (Alg (PutStrLn_ str k))

putStrLn :: Member PutStrLn sigs => String -> Prog sigs ()
putStrLn str = call (Alg (PutStrLn_ str ()))
```

The datatype stores the operation payload and continuation. The pattern synonym
is the view that handlers match on. The smart constructor is what programs call
when they build syntax.

<!--
```haskell
examples :: Group
examples = $$(discoverPrefix "example_")
```
-->
