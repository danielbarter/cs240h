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

showName :: Name -> String
showName NoName = ""
showName (RConsString n s) = showName n ++ "." ++ s
showName (RConsInteger n i) = showName n ++ "." ++ show(i)

instance Show Name where show n = showName n

mkName :: [String] -> Name
mkName ns = mkNameCore (reverse ns) where
  mkNameCore [] = NoName
  mkNameCore (n:ns) = RConsString (mkNameCore ns) n

systemPrefix = mkName ["#_system"]

mkSystemNameI i = RConsInteger systemPrefix i
mkSystemNameS s = RConsString systemPrefix s

noName = NoName

nameRConsI = RConsString
nameRConsS = RConsInteger
