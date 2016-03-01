{-|
Module      : Kernel.Name.Internal
Description : Hierarchical names
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of hierarchical names
-}
module Kernel.Name.Internal where

data Name = NoName | RConsString Name String | RConsInt Name Int deriving (Eq,Ord)

showName :: Name -> String
showName NoName = ""
showName (RConsString n s) = showName n ++ "." ++ s
showName (RConsInt n i) = showName n ++ "." ++ show(i)

instance Show Name where show n = showName n

mkName :: [String] -> Name
mkName ns = mkNameCore (reverse ns) where
  mkNameCore [] = NoName
  mkNameCore (n:ns) = RConsString (mkNameCore ns) n

systemPrefix :: Name
systemPrefix = mkName ["#_system"]

mkSystemNameI :: Int -> Name
mkSystemNameI i = RConsInt systemPrefix i

mkSystemNameS :: String -> Name
mkSystemNameS s = RConsString systemPrefix s

noName :: Name
noName = NoName

nameRConsS :: Name -> String -> Name
nameRConsS = RConsString

nameRConsI :: Name -> Int -> Name
nameRConsI = RConsInt
