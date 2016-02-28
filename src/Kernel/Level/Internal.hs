{-|
Module      : Kernel.Level.Internal
Description : Universe levels
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of universe levels
-}
module Kernel.Level.Internal where

import Kernel.Name
import Lens.Simple
import Data.List as List
import Control.Monad

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

data Level = Zero
           | Succ Level
           | Max (Map Level Int)
           | IMax Level Level
           | LevelParam Name
           | GlobalLevel Name
           deriving (Eq, Ord, Show)

{- Constructors -}

mkZero :: Level
mkZero = Zero

mkSucc :: Level -> Level
mkSucc pred = Succ pred

{-
Max invariants:
--------------
1. the keys of the Max have unique base levels
2. there are at least two keys
3. the constructors of the keys are different from Max and Succ
4. if Zero is a key, it maps to k > 0
-}
mkMax :: Level -> Level -> Level
mkMax lhs rhs = mkMaxCore lhs rhs where
  mkMaxCore (Max args1) (Max args2) = Max $ Map.unionWith max args1 args2
  mkMaxCore (Max args1) rhs = Max $ uncurry (Map.insertWith max) (toLevelOffset rhs) args1
  mkMaxCore lhs (Max args2) = Max $ uncurry (Map.insertWith max) (toLevelOffset lhs) args2
  mkMaxCore Zero rhs = rhs
  mkMaxCore lhs Zero = lhs
  mkMaxCore lhs rhs =
    let (lhs', k1) = toLevelOffset lhs
        (rhs', k2) = toLevelOffset rhs in
     if lhs' == rhs' then (if k1 < k2 then lhs else rhs) else
       Max . Map.fromList $ map toLevelOffset [lhs, rhs]

{-
IMax invariant:
---------------
We only create an IMax if:
1. the RHS is a LevelParam or GlobalLevel
2. the LHS is not zero
3. the LHS and RHS are not the same
-}

mkIMax :: Level -> Level -> Level
mkIMax lhs rhs
  | isDefinitelyNotZero rhs = mkMax lhs rhs
  | isZero rhs = mkZero
  | isZero lhs = rhs
  | lhs == rhs = lhs
  | otherwise = IMax lhs rhs

mkParam :: Name -> Level
mkParam = LevelParam

mkGlobal :: Name -> Level
mkGlobal = GlobalLevel

{- Getters / checkers -}

maxArgsToLevels :: Map Level Int -> [Level]
maxArgsToLevels m = map (uncurry mkIteratedSucc) $ Map.toList m

hasParam :: Level -> Bool
hasParam l = case l of
  LevelParam _ -> True
  Succ pred -> hasParam pred
  Max args -> any hasParam $ Map.keys args
  IMax lhs rhs -> hasParam lhs || hasParam rhs
  _ -> False

getUndefParam :: Level -> [Name] -> Maybe Name
getUndefParam l ns = case l of
  Succ pred -> getUndefParam pred ns
  Max args -> msum . map (flip getUndefParam ns) $ Map.keys args
  IMax lhs rhs -> getUndefParam lhs ns `mplus` getUndefParam rhs ns
  LevelParam n -> if elem n ns then Nothing else Just n
  _ -> Nothing

getUndefGlobal :: Level -> Set Name -> Maybe Name
getUndefGlobal l ns = case l of
  Succ pred -> getUndefGlobal pred ns
  Max args -> msum . map (flip getUndefGlobal ns) $ Map.keys args
  IMax lhs rhs -> getUndefGlobal lhs ns `mplus` getUndefGlobal rhs ns
  GlobalLevel n -> if Set.member n ns then Nothing else Just n
  _ -> Nothing

isExplicit :: Level -> Bool
isExplicit l = case l of
  Zero -> True
  Succ pred -> isExplicit pred
  _ -> False

getExplicitDepth :: Level -> Int
getExplicitDepth l = case l of
  Zero -> 0
  Succ pred -> 1 + getExplicitDepth pred

toLevelOffset :: Level -> (Level, Int)
toLevelOffset l = case l of
  Succ pred -> over _2 (+1) $ toLevelOffset pred
  _ -> (l,0)

isZero :: Level -> Bool
isZero l = case l of
  Zero -> True
  _ -> False

mkIteratedSucc :: Level -> Int -> Level
mkIteratedSucc l k
  | k == 0 = l
  | k > 0 = Succ $ mkIteratedSucc l (k-1)

isDefinitelyNotZero :: Level -> Bool
isDefinitelyNotZero l = case l of
  Zero -> False
  LevelParam _ -> False
  GlobalLevel _ -> False
  Succ _ -> True
  Max args -> any isDefinitelyNotZero $ maxArgsToLevels args
  IMax lhs rhs -> isDefinitelyNotZero rhs

{- Traversals -}

type LevelReplaceFn = (Level -> Maybe Level)

replaceInLevel :: LevelReplaceFn -> Level -> Level
replaceInLevel f l =
  case f l of
    Just l0 -> l0
    Nothing ->
      case l of
        Zero -> l
        Succ pred -> mkSucc $ replaceInLevel f pred
        Max args -> Max . Map.fromList $ map (toLevelOffset . replaceInLevel f) $ maxArgsToLevels args
        IMax lhs rhs -> mkIMax (replaceInLevel f lhs) (replaceInLevel f rhs)
        LevelParam _ -> l
        GlobalLevel _ -> l


instantiate :: [Name] -> [Level] -> Level -> Level
instantiate levelParamNames levels level =
  replaceInLevel (instantiateLevel_fn levelParamNames levels) level
  where
    instantiateLevel_fn :: [Name] -> [Level] -> LevelReplaceFn
    instantiateLevel_fn levelParamNames levels level
      | not (length levelParamNames == length levels) = error "Wrong number of level params"
      | not (hasParam level) = Just level

    instantiateLevel_fn levelParamNames levels (LevelParam name) =
      case List.elemIndex name levelParamNames of
        Nothing -> Nothing
        Just idx -> Just (levels!!idx)

    instantiateLevel_fn _ _ _ = Nothing

notBiggerThan :: Level -> Level -> Bool
notBiggerThan l1 l2 = go l1 l2 where
  go l1 l2
    | isZero l1 = True
    | l1 == l2 = True

  go (Max args1) l2 = all (flip go l2) $ maxArgsToLevels args1
  -- go l1 (Max args2) | any (go l1) $ maxArgsToLevels args2 = True
  -- TODO(dhs): not sure why we need can't decide at this point
  -- (once this fails and I figure it out, put a comment)
  go l1 (Max args2) = any (go l1) $ maxArgsToLevels args2

  go (IMax lhs rhs) l2 = go lhs l2 && go rhs l2
  go l1 (IMax lhs rhs) = go l1 rhs

  go l1 l2 =
    let (l1', k1) = toLevelOffset l1
        (l2', k2) = toLevelOffset l2 in
     if isZero l1' || l1' == l2' then k1 <= k2 else
       if k1 == k2 && k1 > 0 then go l1' l2' else
         False
