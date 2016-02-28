{-|
Module      : Kernel.Level
Description : Universe levels
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for universe levels
-}
module Kernel.Level (
  Level
  , mkZero, mkSucc, mkMax, mkIMax, mkParam, mkGlobal
  , hasParam
  , instantiate
  , getUndefParam, getUndefGlobal
  , notBiggerThan
  ) where
import Kernel.Level.Internal
