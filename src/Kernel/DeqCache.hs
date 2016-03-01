{-|
Module      : Kernel.DeqCache
Description : Union-find for caching isDefEq
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Union-find for caching isDefEq
-}

module Kernel.DeqCache (DeqCache, isEquiv, addEquiv, mkDeqCache) where
import Kernel.DeqCache.Internal
