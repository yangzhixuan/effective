{-# LANGUAGE DataKinds, MonoLocalBinds, CPP #-}

module Control.Effect.Yield where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Monad.Trans.YRes
import Data.HFunctor
import Data.Functor.Unary
import Data.List.Kind
import qualified Control.Monad.Trans.YRes as Y
#ifdef INDEXED
import GHC.TypeNats
import Data.List.Kind
#endif

type Yield a b = Alg (Yield_ a b)
data Yield_ a b x = Yield a (b -> x) deriving Functor

type MapYield a b = Scp (MapYield_ a b)
data MapYield_ a b x = MapYield (a -> a) (b -> b) x deriving Functor

instance Unary (MapYield_ a b) where
  get (MapYield a b x) = x

{-# INLINE yield #-}
yield :: Member (Yield a b) sig => a -> Prog sig b
yield a = call (Alg (Yield a id))

mapYield :: Member (MapYield a b) sig => (a -> a) -> (b -> b) -> Prog sig x -> Prog sig x
mapYield f g p = call (Scp (MapYield f g p))

yieldAlg :: Monad m => Algebra '[Yield a b, MapYield a b] (YResT a b m)
yieldAlg eff
  | Just (Alg (Yield a k)) <- prj eff = Y.yield a (fmap return k)
  | Just (Scp (MapYield f g k)) <- prj eff = Y.mapYield f g k

yieldAT :: AlgTrans '[Yield a b, MapYield a b] '[] '[YResT a b] Monad
yieldAT = AlgTrans (\_ -> yieldAlg)

pingpongWith :: forall oeffs a b y .
                ( HFunctor (Effs oeffs)
#ifdef INDEXED
                , KnownNat (Length oeffs) , KnownNat (1 + Length oeffs)
#endif
                , ForwardsM oeffs '[YResT b a] )
             => (a -> Prog ('[Yield b a, MapYield b a] :++ oeffs) y)
             -> Handler '[Yield a b, MapYield a b] oeffs '[YResT a b] '[Either y]

pingpongWith q = handler run (\_ -> yieldAlg) where
  run :: forall m . Monad m => Algebra oeffs m
      -> (forall x. YResT a b m x -> m (Either y x))
  run oalg p = pingpong p (eval (yieldAlg # getAT (fwds @_ @'[YResT b a]) oalg) . q)