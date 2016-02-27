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
import Data.List (elemIndex,sortBy,genericLength)

import qualified Data.Set as Set
import Data.Set (Set)

{- We maintain the invariant that all `Max` constructions are in normal form. -}
data Level = Zero
           | Succ Level
           | Max [Level]
           | IMax Level Level
           | LevelParam Name
           | GlobalLevel Name
           deriving (Eq, Ord, Show)

has_param :: Level -> Bool
has_param l = case l of
  LevelParam _ -> True
  Succ pred -> has_param pred
  Max args -> any has_param args
  IMax rhs rhs -> has_param lhs || has_param rhs
  _ -> False

get_undef_params :: Level -> [Name] -> [Name]
get_undef_params l ns = case l of
  Succ pred -> get_undef_params pred ns
  Max any -> concatMap get_undef_params args
  IMax lhs rhs -> get_undef_params lhs ns ++ get_undef_params rhs ns
  LevelParam n -> if elem n ns then [] else [n]
  _ -> []

get_undef_globals :: Level -> Set Name -> [Name]
get_undef_globals l ns = case l of
  Succ pred -> get_undef_globals pred ns
  Max args -> concatMap get_undef_globals args
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
  Succ pred -> 1 + get_depth pred

to_level_offset :: Level -> (Level, Integer)
to_level_offset l = case l of
  Succ pred -> over _2 (+1) $ to_offset pred
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
  Max args -> any is_definitely_not_zero args
  IMax lhs rhs -> is_definitely_not_zero rhs


{- Makers -}
mk_zero :: Level
mk_zero = Zero

mk_succ :: Level -> Level
mk_succ pred = Succ pred

{-
Max invariant:
--------------
The arguments of a Max have unique base levels in (level, offset) form, and are sorted
by these base levels.
TODO(dhs): flesh out and make "correct"
-}


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

{-


mk_level_one = mk_succ mk_zero
mk_level_two = mk_succ $ mk_succ mk_zero


mk_max l1 l2
  | is_explicit l1 && is_explicit l2 = if get_depth l1 >= get_depth l2 then l1 else l2
  | l1 == l2 = l1
  | is_zero l1 = l2
  | is_zero l2 = l1
  | otherwise =
    case l1 of
      Max max | max_lhs max == l2 || max_rhs max == l2 -> l1
      otherwise ->
        case l2 of
          Max max | max_lhs max == l1 || max_rhs max == l1 -> l2
          otherwise ->
            let (l1',k1) = to_offset l1
                (l2',k2) = to_offset l2
            in
             if l1' == l2' then (if k1 >= k2 then l1 else l2) else Max (MaxCoreData False l1 l2)





level_kind_rank l = case l of
  Zero -> 0
  Succ _ -> 1
  Max _ -> 2
  IMax _ -> 3
  LevelParam _ -> 4
  GlobalLevel _ -> 5

level_norm_cmp l1 l2 = if l1 == l2 then EQ else level_norm_cmp_core (to_offset l1) (to_offset l2)

level_norm_cmp_core (l1,k1) (l2,k2)
  | l1 == l2 = compare k1 k2
  | level_kind_rank l1 /= level_kind_rank l2 = compare (level_kind_rank l1) (level_kind_rank l2)
  | otherwise =
    case (l1,l2) of
      (LevelParam n1,LevelParam n2) -> compare n1 n2
      (GlobalLevel n1,GlobalLevel n2) -> compare n1 n2
      (Max max1,Max max2) -> level_norm_cmp_max_core max1 max2
      (IMax max1,IMax max2) -> level_norm_cmp_max_core max1 max2

level_norm_cmp_max_core (MaxCoreData _ l1a l2a) (MaxCoreData _ l1b l2b)
  | l1a /= l1b = level_norm_cmp l1a l1b
  | otherwise = level_norm_cmp l2a l2b

collect_max_args (Max (MaxCoreData False l1 l2)) = collect_max_args l1 ++ collect_max_args l2
collect_max_args l = [l]

-- called on sorted explicits
remove_small_explicits [] = Nothing
remove_small_explicits [l] = Just l
remove_small_explicits (l:ls) = remove_small_explicits ls

normalize_level l = let p = to_offset l in case fst p of
  Zero -> l
  LevelParam _ -> l
  GlobalLevel _ -> l
  IMax (MaxCoreData True l1 l2) ->
    let l1_n = normalize_level l1
        l2_n = normalize_level l2
    in
     if l1 /= l1_n || l2 /= l2_n then mk_iterated_succ (mk_imax l1_n l2_n) (snd p) else l
  Max max ->
    let max_args = (sortBy level_norm_cmp) . concat . (map (collect_max_args . normalize_level)) $ collect_max_args (Max max)
        explicit = remove_small_explicits $ filter is_explicit max_args
        non_explicits = let rest = filter (not . is_explicit) max_args
                            (but_last,last) = foldl (\ (keep,prev) curr ->
                                                      if fst (to_offset prev) == fst (to_offset curr)
                                                      then (keep,curr)
                                                      else (keep ++ [prev],curr))
                                              ([],head rest)
                                              (tail rest)
                        in but_last ++ [last]
        explicits = case explicit of
          Nothing -> []
          Just x -> if snd (to_offset x) <= maximum (map (snd . to_offset) non_explicits) then [] else [x]
        all_args = explicits ++ non_explicits
        lifted_args = map (flip mk_iterated_succ (snd p)) all_args
    in
     mk_big_max lifted_args

mk_big_max [] = mk_zero
mk_big_max [l] = l
mk_big_max (x:xs) = mk_max x (mk_big_max xs)

-- | Check whether two levels are equivalent (modulo normalizing 'max')
--
-- >>> let lp = mk_level_param (mk_name ["l1"])
-- >>> level_equiv (mk_max (mk_max mk_level_one lp) mk_zero) (mk_max lp mk_level_one)
-- True
level_equiv l1 l2 = l1 == l2 || normalize_level l1 == normalize_level l2


-- Replace

type LevelReplaceFn = (Level -> Maybe Level)

replace_in_level :: LevelReplaceFn -> Level -> Level
replace_in_level f l =
  case f l of
    Just l0 -> l0
    Nothing ->
      case l of
        Zero -> l
        Succ succ -> mk_succ (replace_in_level f $ succ_of succ)
        Max max -> mk_max (replace_in_level f $ max_lhs max) (replace_in_level f $ max_rhs max)
        IMax imax -> mk_imax (replace_in_level f $ max_lhs imax) (replace_in_level f $ max_rhs imax)
        LevelParam param -> l
        GlobalLevel global -> l


instantiate_level :: [Name] -> [Level] -> Level -> Level
instantiate_level level_param_names levels level =
  replace_in_level (instantiate_level_fn level_param_names levels) level
  where
    instantiate_level_fn :: [Name] -> [Level] -> LevelReplaceFn
    instantiate_level_fn level_param_names levels level
      | not (genericLength level_param_names == genericLength levels) = error "Wrong number of level params"
      | not (has_param level) = Just level

    instantiate_level_fn level_param_names levels (LevelParam name) =
      case elemIndex name level_param_names of
        Nothing -> Nothing
        Just idx -> Just (levels!!idx)

    instantiate_level_fn _ _ _ = Nothing


-- Order

level_leq l1 l2 = level_leq_core (normalize_level l1) (normalize_level l2) where
  level_leq_core l1 l2
    | l1 == l2 || is_zero l1 = True

  level_leq_core (Max max) l2 = level_leq (max_lhs max) l2 && level_leq (max_rhs max) l2
  level_leq_core l1 (Max max)
    | level_leq l1 (max_lhs max) || level_leq l1 (max_rhs max) = True

  level_leq_core (IMax imax) l2 = level_leq (max_lhs imax) l2 && level_leq (max_rhs imax) l2
  level_leq_core l1 (IMax imax) = level_leq l1 (max_rhs imax)

  level_leq_core l1 l2 =
    let (l1',k1) = to_offset l1
        (l2',k2) = to_offset l2
    in
     if l1' == l2' || is_zero l1' then k1 <= k2 else
       if k1 == k2 && k1 > 0 then level_leq l1' l2' else
         False
-}
