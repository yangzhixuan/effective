module Data.Sequence.Class where

import Data.Kind (Type)

import qualified Data.Sequence as S
import qualified Data.Primitive.SmallArray as A
import Data.Foldable

class Functor l => Sequence (l :: Type -> Type) where
  nil :: l a
  cons :: a -> l a -> l a
  append :: l a -> l a -> l a
  index :: l a -> Int -> a
  view :: l a -> Maybe (a, l a)
  seqToArray :: l a -> A.SmallArray a
  seqFromArray :: A.SmallArray a -> l a
  seqToList :: l a -> [a]
  seqFromList :: [a] -> l a

-- Lists are fast for accessing the head.
instance Sequence [] where
  {-# INLINE nil#-}
  nil = []
  {-# INLINE cons #-}
  cons = (:)
  {-# INLINE append #-}
  append = (++)
  {-# INLINE index #-}
  index = (!!)
  {-# INLINE view #-}
  view [] = Nothing
  view (a:as) = Just (a, as)
  {-# INLINE seqToArray #-}
  seqToArray = A.smallArrayFromList
  {-# INLINE seqFromArray #-}
  seqFromArray = toList
  {-# INLINE seqToList #-}
  seqToList = id
  {-# INLINE seqFromList #-}
  seqFromList = id

-- Finger trees are reasonably fast for all operations.
instance Sequence S.Seq where
  {-# INLINE nil#-}
  nil = S.empty
  {-# INLINE cons #-}
  cons = (S.<|)
  {-# INLINE append #-}
  append = (S.><)
  {-# INLINE index #-}
  index = S.index
  {-# INLINE view #-}
  view x = case S.viewl x of
    S.EmptyL -> Nothing
    a S.:< as -> Just (a, as)
  {-# INLINE seqToArray #-}
  seqToArray = A.smallArrayFromList . toList
  {-# INLINE seqFromArray #-}
  seqFromArray = S.fromList . toList
  {-# INLINE seqToList #-}
  seqToList = toList
  {-# INLINE seqFromList #-}
  seqFromList = S.fromList

-- Arrays are very fast for indexing and destruction but very slow for construction.
instance Sequence A.SmallArray where
  {-# INLINE nil#-}
  nil = A.emptySmallArray
  {-# INLINE cons #-}
  cons a as = A.smallArrayFromList (a : toList as)
  {-# INLINE append #-}
  append as bs = A.smallArrayFromList (toList as ++ toList bs)
  {-# INLINE index #-}
  index as n = A.indexSmallArray as n
  {-# INLINE view #-}
  view as = case length as of
    0 -> Nothing
    n -> Just (A.indexSmallArray as 0, A.cloneSmallArray as 1 (n-1))
  {-# INLINE seqToArray #-}
  seqToArray = id
  {-# INLINE seqFromArray #-}
  seqFromArray = id
  {-# INLINE seqToList #-}
  seqToList = toList
  {-# INLINE seqFromList #-}
  seqFromList = A.smallArrayFromList