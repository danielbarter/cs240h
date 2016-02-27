{-|
Module      : Kernel.Level.Internal
Description : Universe levels
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of universe levels
-}
module Kernel.Level.Internal where

import Control.Monad
import Kernel.Name
import Lens.Simple
import Data.List as List

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

data Level = Zero
           | Succ Level
           | Max (Map Level Integer)
           | IMax Level Level
           | LevelParam Name
           | GlobalLevel Name
           deriving (Eq, Ord, Show)

{- Constructors -}

mk_zero :: Level
mk_zero = Zero

mk_succ :: Level -> Level
mk_succ pred = Succ pred

{-
Max invariant:
--------------
The keys of the Max have unique base levels whose constructor is different from Max and Succ.
-}
mk_max :: Level -> Level -> Level
mk_max lhs rhs = mk_max_core lhs rhs where
  mk_max_core (Max args1) (Max args2) = Max (Map.unionWith max args1 args2)
  mk_max_core (Max args1) rhs = Max (uncurry (Map.insertWith max) (to_level_offset rhs) args1)
  mk_max_core lhs (Max args2) = Max (uncurry (Map.insertWith max) (to_level_offset lhs) args2)
  mk_max_core lhs rhs = Max . Map.fromList $ map to_level_offset [lhs, rhs]

{-
IMax invariant:
---------------
We only create an IMax if:
1. the RHS is a LevelParam or GlobalLevel
2. the LHS is not zero
3. the LHS and RHS are not the same
-}

mk_imax :: Level -> Level -> Level
mk_imax lhs rhs
  | is_definitely_not_zero rhs = mk_max lhs rhs
  | is_zero rhs = mk_zero
  | is_zero lhs = rhs
  | lhs == rhs = lhs
  | otherwise = IMax lhs rhs

mk_level_param :: Name -> Level
mk_level_param = LevelParam

mk_global_level :: Name -> Level
mk_global_level = GlobalLevel

{- Getters / checkers -}

max_args_to_levels :: Map Level Integer -> [Level]
max_args_to_levels m = map (uncurry mk_iterated_succ) $ Map.toList m

has_param :: Level -> Bool
has_param l = case l of
  LevelParam _ -> True
  Succ pred -> has_param pred
  Max args -> any has_param $ Map.keys args
  IMax lhs rhs -> has_param lhs || has_param rhs
  _ -> False

get_undef_params :: Level -> [Name] -> [Name]
get_undef_params l ns = case l of
  Succ pred -> get_undef_params pred ns
  Max args -> concatMap (flip get_undef_params ns) $ Map.keys args
  IMax lhs rhs -> get_undef_params lhs ns ++ get_undef_params rhs ns
  LevelParam n -> if elem n ns then [] else [n]
  _ -> []

get_undef_globals :: Level -> Set Name -> [Name]
get_undef_globals l ns = case l of
  Succ pred -> get_undef_globals pred ns
  Max args -> concatMap (flip get_undef_globals ns) $ Map.keys args
  IMax lhs rhs -> get_undef_globals lhs ns ++ get_undef_globals rhs ns
  GlobalLevel n -> if Set.member n ns then [] else [n]
  _ -> []

is_explicit :: Level -> Bool
is_explicit l = case l of
  Zero -> True
  Succ pred -> is_explicit pred
  _ -> False

get_explicit_depth :: Level -> Integer
get_explicit_depth l = case l of
  Zero -> 0
  Succ pred -> 1 + get_explicit_depth pred

to_level_offset :: Level -> (Level, Integer)
to_level_offset l = case l of
  Succ pred -> over _2 (+1) $ to_level_offset pred
  _ -> (l,0)

is_zero :: Level -> Bool
is_zero l = case l of
  Zero -> True
  _ -> False

mk_iterated_succ :: Level -> Integer -> Level
mk_iterated_succ l k
  | k == 0 = l
  | k > 0 = Succ $ mk_iterated_succ l (k-1)

is_definitely_not_zero :: Level -> Bool
is_definitely_not_zero l = case l of
  Zero -> False
  LevelParam _ -> False
  GlobalLevel _ -> False
  Succ _ -> True
  Max args -> any is_definitely_not_zero $ max_args_to_levels args
  IMax lhs rhs -> is_definitely_not_zero rhs

{- Traversals -}

type LevelReplaceFn = (Level -> Maybe Level)

replace_in_level :: LevelReplaceFn -> Level -> Level
replace_in_level f l =
  case f l of
    Just l0 -> l0
    Nothing ->
      case l of
        Zero -> l
        Succ pred -> mk_succ $ replace_in_level f pred
        Max args -> Max . Map.fromList $ map (to_level_offset . replace_in_level f) $ max_args_to_levels args
        IMax lhs rhs -> mk_imax (replace_in_level f lhs) (replace_in_level f rhs)
        LevelParam _ -> l
        GlobalLevel _ -> l


instantiate_level :: [Name] -> [Level] -> Level -> Level
instantiate_level level_param_names levels level =
  replace_in_level (instantiate_level_fn level_param_names levels) level
  where
    instantiate_level_fn :: [Name] -> [Level] -> LevelReplaceFn
    instantiate_level_fn level_param_names levels level
      | not (length level_param_names == length levels) = error "Wrong number of level params"
      | not (has_param level) = Just level

    instantiate_level_fn level_param_names levels (LevelParam name) =
      case List.elemIndex name level_param_names of
        Nothing -> Nothing
        Just idx -> Just (levels!!idx)

    instantiate_level_fn _ _ _ = Nothing

level_not_bigger_than :: Level -> Level -> Bool
level_not_bigger_than l1 l2 = go l1 l2 where
  go l1 l2
    | is_zero l1 = True
    | l1 == l2 = True

  go (Max args1) l2 = all (flip go l2) $ max_args_to_levels args1
  -- go l1 (Max args2) | any (go l1) $ max_args_to_levels args2 = True
  -- TODO(dhs): not sure why we need can't decide at this point
  -- (once this fails and I figure it out, put a comment)
  go l1 (Max args2) = any (go l1) $ max_args_to_levels args2

  go (IMax lhs rhs) l2 = go lhs l2 && go rhs l2
  go l1 (IMax lhs rhs) = go l1 rhs

  go l1 l2 =
    let (l1', k1) = to_level_offset l1
        (l2', k2) = to_level_offset l2 in
     if is_zero l1' || l1' == l2' then k1 <= k2 else
       if k1 == k2 && k1 > 0 then go l1' l2' else
         False
