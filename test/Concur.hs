{-# LANGUAGE PartialTypeSignatures #-}
module Main where

import Prelude hiding (log )
import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer
import Control.Effect.Concurrency
import Control.Effect.Except
import Control.Effect.Family.Algebraic
import Control.Monad
import Control.Effect.WithName
import Control.Effect.Yield
import Control.Effect.Reader
import System.Process
import System.Random

import Data.Proxy
import qualified Control.Concurrent.QSem as QSem

type IOPar = '[Alg IO, Par, JPar]

ioPar :: Algebra IOPar IO
ioPar = ioAlg # parIOAlg # jparIOAlg

main :: IO ()
main = return ()

data ActNames = Handshake | Raisehand deriving (Show, Eq, Ord)
type HR = CCSAction ActNames

handshake :: Member (Act HR) sig => Prog sig ()
handshake = act (Action Handshake)

shakehand :: Member (Act HR) sig => Prog sig ()
shakehand = act (CoAction Handshake)

resHS :: Member (Res HR) sig => Prog sig x -> Prog sig x
resHS x = res (Action Handshake) (res (CoAction Handshake) x)

prog :: Members '[Par, Act HR, Res HR, Tell String] sig => Prog sig ()
prog = resHS (par (do tell "A"; handshake; tell "C")
                  (do tell "B"; shakehand; tell "D"))

test1 :: (String, ListActs HR ())
test1 = handle (resump |> writer @String) prog

test2 :: ListActs HR (String, ())
test2 = handle (writer @String |> resump) prog

-- ABCD
test31 :: (String, ActsMb HR ())
test31 = handle (fuse (resumpWith (False : True : True : True : [])) (writer @String)) prog

-- ABDC
test32 :: (String, ActsMb HR ())
test32 = handle (fuse (resumpWith (False : True : True : False : [])) (writer @String)) prog

-- BADC
test33 :: (String, ActsMb HR ())
test33 = handle (fuse (resumpWith (False : False : True : True : [])) (writer @String)) prog

-- BACD
test34 :: (String, ActsMb HR ())
test34 = handle (fuse (resumpWith (False : False : True : False : [])) (writer @String)) prog

prog2 :: Members '[Par, Alg IO] sig => Prog sig ()
prog2 =
  do p <- io (QSem.newQSem 0)
     q <- io (QSem.newQSem 0)
     par (do replicateM_ 5 (io (putStr "A"))
             io (QSem.waitQSem p)
             io (QSem.signalQSem q)
             replicateM_ 5 (io (putStr "C")))
         (do replicateM_ 5 (io (putStr "B"))
             io (QSem.signalQSem p)
             io (QSem.waitQSem q)
             replicateM_ 5 (io (putStr "D")))

test4 :: IO ()
test4 = handleIO' (Proxy @IOPar) ioPar (identity @'[]) prog2

tell' :: forall w sig. (Member ("t2" :@ (Tell w)) sig, Monoid w) => w -> Prog sig ()
tell' w = callPAlg (Proxy @"t2") (Tell_ w ())

prog3 :: Members '[Par, Act HR, Res HR, Tell String, "t2" :@ (Tell String)] sig => Prog sig ()
prog3 = resHS (par (do tell "A"; handshake; tell' "C")
                   (do tell "B"; shakehand; tell' "D"))

-- The cloned `tell` operations are handled before `par` so they behave
-- like thread-local writers while the original `tell`s are global.
test5 :: (String, ListActs HR (String, ()))
test5 = handle (renameEffs (Proxy @"t2") writer |> resump |> writer) prog3

prog4 :: Member (Alg IO) sig => Prog sig ()
prog4 = io (putChar 'x')

test6 :: IO ()
test6 = handleIO (identity @'[]) prog4

test7 :: IO (Either String ())
test7 = handleIO' (Proxy @IOPar) ioPar (ccsByQSem @ActNames |> writerIO) (prog >> io (putStrLn ""))


prog5 :: Members '[JPar, Act HR, Res HR, Tell String] sig => Prog sig (Int, Int)
prog5 = resHS (jpar (do tell "A"; handshake; tell "C"; return 0)
                    (do tell "B"; shakehand; tell "D"; return 1))

test8 :: (String, ListActs HR (Int, Int))
test8 = handle (jresump |> writer @String) prog5

test9 :: IO (Either String (Int, Int))
test9 = handleIO' (Proxy @IOPar) ioPar (ccsByQSem @ActNames |> writerIO) prog5

prog6 :: Members '[Yield Int Int, Alg IO] sig => Int -> Prog sig Int
prog6 n = do io (putStrLn ("Ping " ++ show n))
             n' <- yield (n + 1)
             prog6 n'

prog6' :: Members '[Yield Int Int, Alg IO] sig => Int -> Prog sig Int
prog6' n
  | n > 100   = do io (putStrLn "Too big"); return n
  | otherwise = do io (putStrLn ("Pong " ++ show n))
                   n' <- yield (2 * n)
                   prog6' n'

test10 :: IO (Either Int Int)
test10 = handleIO' (Proxy @'[Alg IO]) ioPar
            (pingpongWith (prog6' @'[Yield Int Int, MapYield Int Int, Alg IO]))
            (prog6 0)


-- ((threadId >> printWithId) \\ reader)  >> (ccsByQSem \\ State SemMap)

-- Give a local thread ID to every process
threadId :: Handler '[Par] '[Par, Local String] '[] a a
threadId = interpretM1 $ \alg (Par a b) ->
  parM alg (localM alg (++ "L") a) (localM alg (++ "R") b)

-- Prepend every output operation with a thread ID
tellWithId :: Handler '[Tell String] '[Tell String, Ask String] '[] a a
tellWithId= interpret1 $ \(Tell s k) ->
  do id <- ask
     tell (id ++ ": " ++ s ++ ". ")
     return k

tellWithLock :: Handler '[Tell String] '[Tell String, Act HR, Par, Res HR] '[] a a
tellWithLock = Handler
  (Runner $ \oalg p ->
    let daemon =
          do callM oalg (Act (CoAction Raisehand) ())
             callM oalg (Act (Action Raisehand) ())
             daemon
    in do resM oalg (Action Raisehand) $
            parM oalg p daemon)
  (interpretAT1 $ \(Tell s k) ->
    do act (Action Raisehand)
       tell s
       act (CoAction Raisehand)
       return k)

-- Processes can tell strings and their output is tagged with their ID
ccsWithTell :: Handler [Par, Tell String, Act HR, Res HR]
                 [Par, Alg IO]
                 _
                 a
                 (Either String a)
ccsWithTell =
  ((threadId |> tellWithId) \\ reader "")
    |> tellWithLock
    |> ccsByQSem @ActNames
    |> writerIO

bohem :: () ! [Act HR, Res HR, Par, Tell String]
bohem = par (resHS $ par (do tell "I am just a poor boy"; handshake)
                         (do shakehand; tell "I need no sympathy"))
            (tell "Oh poor boy")

intro1 :: IO (Either String ())
intro1 = handleIO' (Proxy @'[Par]) ioPar (ccsByQSem @ActNames |> writerIO) bohem

intro2 :: IO (Either String ())
intro2 = handleIO' (Proxy @'[Par]) ioPar (tellWithLock |> ccsByQSem @ActNames |> writerIO) bohem

intro3 :: IO (Either String ())
intro3 = handleIO' (Proxy @'[Par]) ioPar
  (((threadId |> tellWithId) \\ reader "")
    |> tellWithLock
    |> ccsByQSem @ActNames
    |> writerIO)
  bohem

intro4 :: IO (Either String ())
intro4 = handleIO' (Proxy @'[Par]) ioPar
  (ccsByQSem @ActNames |> say)
  bohem

say :: Handler '[Tell String] '[Alg IO] '[] a a
say = interpret1 $
  \(Tell w k) -> do io (sayStr w)
                    return k
  where
    voices = ["Daniel", "Eddy", "Karen", "Samantha"]
    len = length voices

    sayStr :: String -> IO ()
    sayStr s =
      do v <- (randomIO :: IO Int)
         let cmd = "say -v " ++ (voices !! (v `mod` len)) ++ " '" ++ s ++ "'"
         callCommand cmd