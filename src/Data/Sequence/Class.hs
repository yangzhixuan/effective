module Data.Sequence.Class where

import Data.Kind (Type)

import qualified Data.Sequence as S
import qualified Data.Primitive.SmallArray as A
import Data.Foldable

class Sequence (l :: Type -> Type) where
  nil :: l a
  cons :: a -> l a -> l a
  append :: l a -> l a -> l a
  index :: l a -> Int -> a
  view :: l a -> Maybe (a, l a)

-- Lists are fast for accessing the head.
instance Sequence [] where
  nil = []
  cons = (:)
  append = (++)
  index = (!!)
  view [] = Nothing
  view (a:as) = Just (a, as)

-- Finger trees are reasonably fast for all operations.
instance Sequence S.Seq where
  nil = S.empty
  cons = (S.<|)
  append = (S.><)
  index = S.index
  view x = case S.viewl x of
    S.EmptyL -> Nothing
    a S.:< as -> Just (a, as)

-- Arrays are very fast for indexing and destruction but very slow for construction.
instance Sequence A.SmallArray where
  nil = A.emptySmallArray
  cons a as = A.smallArrayFromList (a : toList as)
  append as bs = A.smallArrayFromList (toList as ++ toList bs)
  index as n = A.indexSmallArray as n
  view as = case length as of
    0 -> Nothing
    n -> Just (A.indexSmallArray as 0, A.cloneSmallArray as 1 (n-1))