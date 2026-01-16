{-|
Module      : Control.Effect.CodeGen.Type
Description : Types for the code-generation effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains some basic definitions for type `CodeQ` of code.
-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Type
  ( module Control.Effect.CodeGen.Type
  , CodeQ (..)
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Effect.State ( get, put, Get, Put )
import Control.Effect.Reader
import Control.Effect.Except
import Control.Effect ( Member, Prog )

-- | Print a piece of code.
printCodeQ :: CodeQ a -> IO ()
printCodeQ a = do
  x <- unType <$> runQ (examineCode a)
  print $ ppr x

-- | In Andras Kovacs's original paper, intensional pattern matching on code
-- is not allowed, but it is allowed in Template Haskell and can be used
-- for example to implement this @codeApp@ such that @codeApp xs [|| [] ||]@
-- equals @xs@ (rather than @[|| $$xs ++ [] ||]@). We don't essentially rely on
-- this but it is handy in a few places for generating better-looking code.
codeApp :: CodeQ [a] -> CodeQ [a] -> CodeQ [a]
codeApp cql@(Code ql) cqr@(Code qr) = Code $
  do r <- qr
     if isEmptyListExp r
       then ql
       else examineCode [|| $$cql ++ $$cqr ||]
  where
    isEmptyListExp :: TExp [a] -> Bool
    isEmptyListExp (TExp (ConE e))
      | e == '[]     =  True
    isEmptyListExp _ = False

-- * Operations specialised for `CodeQ`.
--
-- Sometimes GHC has a hard time of inferring the type of operations like
-- @put [|| ... ||]@ because the quotation by default has type @Code m@.
-- So having some specialised operations is sometimes handy.

putC :: Member (Put (CodeQ c)) sig => CodeQ c -> Prog sig ()
putC = put

getC :: Member (Get (CodeQ c)) sig => Prog sig (CodeQ c)
getC = get

askC :: Member (Ask (CodeQ c)) sig => Prog sig (CodeQ c)
askC = ask

localC :: Member (Local (CodeQ c)) sig => (CodeQ c -> CodeQ c) -> Prog sig (CodeQ c) -> Prog sig (CodeQ c)
localC = local

throwC :: Member (Throw (CodeQ c)) sig => CodeQ c -> Prog sig a
throwC = throw

catchC :: Member (Catch (CodeQ c)) sig => Prog sig a -> (CodeQ c -> Prog sig a) -> Prog sig a
catchC = catch