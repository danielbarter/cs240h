{-|
Module      : Kernel.DeqCache.Internal
Description : Union-find for caching isDefEq
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Union-find for caching isDefEq
-}
{-# LANGUAGE TemplateHaskell #-}
module Kernel.DeqCache.Internal where

import qualified Data.IntDisjointSet as DS
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Expr

import Lens.Simple (makeLenses, over, view, use, (.=), (%=), (<~), (%%=))

type NodeRef = Int
data DeqCache = DeqCache {
  _deqCacheDS :: DS.IntDisjointSet,
  _deqCacheMap :: Map Expr NodeRef
  }

makeLenses ''DeqCache

mkDeqCache = DeqCache DS.empty Map.empty

isEquiv :: Expr -> Expr -> DeqCache -> (Bool, DeqCache)
isEquiv e1 e2 deqCache = flip runState deqCache $ do
  n1 <- toNode e1
  n2 <- toNode e2
  deqCacheDS %%= DS.equivalent n1 n2

addEquiv :: Expr -> Expr -> DeqCache -> DeqCache
addEquiv e1 e2 deqCache = flip execState deqCache $ do
  n1 <- toNode e1
  n2 <- toNode e2
  deqCacheDS %= DS.union n1 n2

toNode :: Expr -> State DeqCache NodeRef
toNode e = do
  m <- use deqCacheMap
  case Map.lookup e m of
    Just n -> return n
    Nothing -> do
      n <- liftM DS.size $ use deqCacheDS
      deqCacheDS %= DS.insert n
      deqCacheMap %= Map.insert e n
      return n
