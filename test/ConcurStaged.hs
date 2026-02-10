module ConcurStaged where

import Prelude hiding (log )
import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer
import Control.Effect.Concurrency
import Control.Effect.Reader
import qualified Control.Concurrent.QSem as QSem

type IOPar = '[Alg IO, Par, JPar]

data ActNames = Handshake | Raisehand deriving (Show, Eq, Ord)
type HR = CCSAction ActNames

ioParC :: AlgebraC IOPar IO
ioParC = ioAlgC $# parIOAlgC $# jparIOAlgC

tellWithLockC :: HandlerC '[Tell String] '[Tell String, Act HR, Par, Res HR] '[] a a
tellWithLockC = HandlerC
  (RunnerC $ \oalg -> [|| \p ->
    let daemon =
          do $$(callMC oalg) (Act (CoAction Raisehand) ())
             $$(callMC oalg) (Act (Action Raisehand) ())
             daemon
    in do $$(callMC oalg) (Res (Action Raisehand) $
            $$(callMC oalg) (Par p daemon))
  ||])
  (algTrans1C $ \oalg -> [|| NT $ \(Tell s k) ->
    do $$(callMC oalg) (Act (Action Raisehand) ())
       -- I don't know why in GHC 9.8.4 and 9.10.1 the following causes an error of
       -- overlapping instances.
       -- $$(callMC oalg) (Tell s ())
       at $$(fst oalg) (Tell s ())
       $$(callMC oalg) (Act (CoAction Raisehand) ())
       return k
  ||])


askMC :: Ask s `Member` effs => AlgebraC effs m -> CodeQ (m s)
askMC alg = [|| $$(dispatchC alg) `at` (Ask id) ||]

tellMC :: Tell w `Member` effs => AlgebraC effs m -> CodeQ (w -> m ())
tellMC alg = [|| \w -> $$(dispatchC alg) `at` (Tell w ()) ||]

tellWithIdC :: HandlerC '[Tell String] '[Tell String, Ask String] '[] a a
tellWithIdC= interpretM1C $ \alg -> [|| NT $ \(Tell s k) ->
  do id <- $$(askMC alg)
     $$(tellMC alg) (id ++ ": " ++ s ++ ". ")
     return k
  ||]


parMC :: Member Par effs => AlgebraC effs m -> CodeQ (m x) -> CodeQ (m x) -> CodeQ (m x)
parMC alg p q = [|| $$(callMC alg) (Par $$p $$q) ||]

localMC :: Member (Local s) effs => AlgebraC effs m -> CodeQ (s -> s) -> CodeQ (m x) -> CodeQ (m x)
localMC alg f p = [|| $$(callMC alg) (Local $$f $$p) ||]

threadIdC :: HandlerC '[Par] '[Par, Local String] '[] a a
threadIdC = interpretM1C $ \alg -> [|| NT $ \(Par a b) ->
  $$(parMC alg (localMC alg [|| (++ "L")||] [||a||])
               (localMC alg [|| (++ "R")||] [||b||])) ||]
