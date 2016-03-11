{-# LANGUAGE BangPatterns #-}
module Util.Vec where

import Data.STRef
import Data.Vector.Unboxed.Mutable as MU
import Control.Monad.ST as ST
import Control.Monad.Primitive (PrimState)

type MVI s  = MVector (PrimState (ST s)) Int
data Vec s = Vec (STRef s Int) (MVI s)

vecPushBack :: Vec s -> Int -> ST s ()
vecPushBack (Vec k v) x = do
  numElems <- readSTRef k
  if numElems < MU.length v then MU.unsafeWrite v numElems x >> writeSTRef k (numElems + 1)
    else MU.unsafeGrow v (MU.length v) >>= (\y -> MU.unsafeWrite y numElems x >> writeSTRef k (numElems + 1))

vecNew :: Int -> ST s (Vec s)
vecNew capacity = do
  v <- MU.new capacity
  k <- newSTRef 0
  return (Vec k v)

vecWrite :: Vec s -> Int -> Int -> ST s ()
vecWrite (Vec k v) i x = MU.unsafeWrite v i x >> modifySTRef k (+1)

vecRead :: Vec s -> Int -> ST s Int
vecRead (Vec k v) i = MU.unsafeRead v i

vecLength :: Vec s -> ST s Int
vecLength (Vec k v) = return (MU.length v)

someFunc :: IO ()
someFunc = print $ runST $ do
  v <- vecNew 10
  vecPushBack v 11
  vecPushBack v 12
  vecWrite v 0 111
  l <- vecLength v
  x11 <- vecRead v 0
  x12 <- vecRead v 1
  return (l, x11, x12)
