{-|
Module      : Kernel.DefEqCache
Description : Union-find for caching is_def_eq
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Union-find for caching is_def_eq
-}

module Kernel.DefEqCache (DefEqCache, isEquiv, addEquiv, emptyDefEqCache) where
import Kernel.DefEqCache.Internal
