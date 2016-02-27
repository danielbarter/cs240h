{-|
Module      : Kernel.Name.Internal
Description : Hierarchical names
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of hierarchical names
-}
module Kernel.Name.Internal where

data Name = NoName | RConsString Name String | RConsInteger Name Integer deriving (Eq,Ord)

show_name :: Name -> String
show_name NoName = ""
show_name (RConsString n s) = show_name n ++ "." ++ s
show_name (RConsInteger n i) = show_name n ++ "." ++ show(i)

instance Show Name where show n = show_name n

mk_name :: [String] -> Name
mk_name ns = mk_name_core (reverse ns) where
  mk_name_core [] = NoName
  mk_name_core (n:ns) = RConsString (mk_name ns) n

system_prefix = mk_name ["#_system"]

mk_sysname_i i = RConsInteger system_prefix i
mk_sysname_s s = RConsString system_prefix s

no_name = NoName

name_rcons_i = RConsString
name_rcons_s = RConsInteger
