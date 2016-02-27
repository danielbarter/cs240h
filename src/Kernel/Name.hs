{-|
Module      : Kernel.Name
Description : Hierarchical names
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for hierarchical names
-}
module Kernel.Name (
  Name
  , no_name
  , mk_name, mk_sysname_i, mk_sysname_s
  , name_rcons_i, name_rcons_s
  ) where
import Kernel.Name.Internal
