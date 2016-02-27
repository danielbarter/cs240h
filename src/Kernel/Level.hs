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
  , mk_zero, mk_succ, mk_max, mk_imax, mk_level_param, mk_global_level
  , level_has_param
  , instantiate_level
  , get_undef_params, get_undef_globals
  , level_not_bigger_than
  ) where
import Kernel.Level.Internal
