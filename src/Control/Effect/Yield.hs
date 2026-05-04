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

$(makeGen [e| yield :: forall a b. a -> b |])

$(makeScp [e| mapYield :: forall a b. (a -> a) -> (b -> b) -> 1 |])

instance Unary (MapYield_ a b) where
  get (MapYield_ a b x) = x

yieldAlg :: Monad m => Algebra '[Yield a b, MapYield a b] (YResT a b m)
yieldAlg (Yield a k)      = Y.yield a (fmap return k)
yieldAlg (MapYield f g k) = Y.mapYield f g k

yieldAT :: AlgTrans '[Yield a b, MapYield a b] '[] '[YResT a b] Monad
yieldAT = AlgTrans (\_ -> yieldAlg)

pingpongWith :: forall osigs a b c y .
                ( HFunctor (Effs osigs)
#ifdef INDEXED
                , KnownNat (Length osigs) , KnownNat (1 + Length osigs)
#endif
                , ForwardsM osigs '[YResT b a] )
             => (a -> Prog ('[Yield b a, MapYield b a] :++ osigs) y)
             -> Handler '[Yield a b, MapYield a b] osigs '[YResT a b] c (Either y c)

pingpongWith q = handler run (\_ -> yieldAlg) where
  run :: forall m . Monad m => Algebra osigs m
      -> (YResT a b m c -> m (Either y c))
  run oalg p = pingpong p (eval (yieldAlg # getAT (fwds @osigs @'[YResT b a]) oalg) . q)