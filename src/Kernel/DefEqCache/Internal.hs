{-|
Module      : Kernel.DefEqCache.Internal
Description : Union-find for caching is_def_eq
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Union-find for caching is_def_eq
-}
{-# LANGUAGE TemplateHaskell #-}
module Kernel.DefEqCache.Internal where

import qualified Data.IntDisjointSet as DS
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Expr

import Lens.Simple (makeLenses, over, view, use, (.=), (%=), (<~))

type NodeRef = Int
data DefEqCache = DefEqCache {
  _defEqCacheDS :: DS.IntDisjointSet,
  _defEqCacheMap :: Map Expr NodeRef
  }

makeLenses ''DefEqCache

mkDefEqCache = DefEqCache DS.empty Map.empty

isEquiv :: Expr -> Expr -> DefEqCache -> (Bool, DefEqCache)
isEquiv e1 e2 defEqCache = flip runState defEqCache $ do
  n1 <- toNode e1
  n2 <- toNode e2
  (result, newDS) <- liftM (DS.equivalent n1 n2) $ use defEqCacheDS
  defEqCacheDS .= newDS
  return result

addEquiv :: Expr -> Expr -> DefEqCache -> DefEqCache
addEquiv e1 e2 defEqCache = flip execState defEqCache $ do
  n1 <- toNode e1
  n2 <- toNode e2
  defEqCacheDS <~ (liftM (DS.union n1 n2) $ use defEqCacheDS)

toNode :: Expr -> State DefEqCache NodeRef
toNode e = do
  m <- use defEqCacheMap
  case Map.lookup e m of
    Just n -> return n
    Nothing -> do
      n <- liftM DS.size $ use defEqCacheDS
      defEqCacheDS %= DS.insert n
      defEqCacheMap %= Map.insert e n
      return n
