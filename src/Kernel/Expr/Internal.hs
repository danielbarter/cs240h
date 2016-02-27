{-|
Module      : Expr
Description : Expressions
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation for expressions
-}
module Kernel.Expr.Internal where

import Kernel.Name
import Kernel.Level
import qualified Data.Maybe as Maybe
import qualified Data.List as List
import Control.Monad (mplus)

data BinderInfo = BinderDefault | BinderImplicit | BinderStrict | BinderClass deriving (Eq,Show,Ord)
data ExprCache = ExprCache { cache_has_local :: Bool,
                             cache_has_level_param :: Bool,
                             cache_free_var_range :: Int } deriving (Eq,Show,Ord)

data VarData = VarData { var_idx :: Int } deriving (Eq,Show,Ord)

data LocalData = LocalData { local_name :: Name ,
                             local_pp_name :: Name,
                             local_type :: Expr,
                             local_info :: BinderInfo,
                             local_cache :: ExprCache } deriving (Eq,Show,Ord)

data SortData = SortData { sort_level :: Level } deriving (Eq,Show,Ord)

data ConstantData = ConstantData { const_name :: Name , const_levels :: [Level] } deriving (Eq,Show,Ord)

data AppData = AppData { app_fn :: Expr, app_arg :: Expr, app_cache :: ExprCache  } deriving (Eq,Show,Ord)

data BindingData = BindingData { binding_name :: Name,
                                 binding_domain :: Expr,
                                 binding_body :: Expr,
                                 binding_info :: BinderInfo,
                                 binding_cache :: ExprCache } deriving (Eq,Show,Ord)

data Expr = Var VarData
                | Local LocalData
                | Sort SortData
                | Constant ConstantData
                | Lambda BindingData
                | Pi BindingData
                | App AppData
                deriving (Eq,Show,Ord)

{- Free variables -}

get_free_var_range :: Expr -> Int
get_free_var_range e = case e of
  Var var -> 1 + var_idx var
  Local local -> cache_free_var_range $ local_cache local
  Constant _ -> 0
  Sort _ -> 0
  Lambda lam -> cache_free_var_range $ binding_cache lam
  Pi pi -> cache_free_var_range $ binding_cache pi
  App app -> cache_free_var_range $ app_cache app

has_free_vars :: Expr -> Bool
has_free_vars e = get_free_var_range e > 0

closed :: Expr -> Bool
closed e = not $ has_free_vars e

{- `has` functions -}

expr_has_local :: Expr -> Bool
expr_has_local e = case e of
  Var _ -> False
  Local _ -> True
  Sort _ -> False
  Constant _ -> False
  Lambda lam -> cache_has_local $ binding_cache lam
  Pi pi -> cache_has_local $ binding_cache pi
  App app -> cache_has_local $ app_cache app

expr_has_level_param :: Expr -> Bool
expr_has_level_param e = case e of
  Var var -> False
  Local local -> cache_has_level_param $ local_cache local
  Constant const -> any (==True) (map level_has_param (const_levels const))
  Sort sort -> level_has_param (sort_level sort)
  Lambda lam -> cache_has_level_param $ binding_cache lam
  Pi pi -> cache_has_level_param $ binding_cache pi
  App app -> cache_has_level_param $ app_cache app

{- N-ary applications -}

get_operator :: Expr -> Expr
get_operator e = case e of
  App app -> get_operator (app_fn app)
  _ -> e

get_app_args :: Expr -> [Expr]
get_app_args e = reverse (get_app_args_rev e) where
  get_app_args_rev (App app) = app_arg app : get_app_args_rev (app_fn app)
  get_app_args_rev _ = []

get_app_op_args :: Expr -> (Expr, [Expr])
get_app_op_args e = (get_operator e,get_app_args e)

{- Constructors -}

mk_var :: Int -> Expr
mk_var v_idx = Var (VarData v_idx)

mk_local :: Name -> Name -> Expr -> BinderInfo -> Expr
mk_local name pp_name ty binfo = Local $ mk_local_data name pp_name ty binfo

mk_local_default :: Name -> Expr -> Expr
mk_local_default name ty = Local $ mk_local_data name name ty BinderDefault

mk_local_data :: Name -> Name -> Expr -> BinderInfo -> LocalData
mk_local_data name pp_name ty binfo = LocalData name pp_name ty binfo
                                      (ExprCache True (expr_has_level_param ty) (get_free_var_range ty))

mk_sort :: Level -> Expr
mk_sort l = Sort (SortData l)

mk_constant :: Name -> [Level] -> Expr
mk_constant name levels = Constant (ConstantData name levels)

mk_app :: Expr -> Expr -> Expr
mk_app fn arg = App (AppData fn arg (ExprCache
                                     (expr_has_local fn || expr_has_local arg)
                                     (expr_has_level_param fn || expr_has_level_param arg)
                                     (max (get_free_var_range fn) (get_free_var_range arg))))

mk_app_seq :: Expr -> [Expr] -> Expr
mk_app_seq fn [] = fn
mk_app_seq fn (arg:args) = mk_app_seq (mk_app fn arg) args

mk_binding :: Bool -> Name -> Expr -> Expr -> BinderInfo -> Expr
mk_binding is_pi name domain body binfo =
  let ecache = (ExprCache
                (expr_has_local domain || expr_has_local body)
                (expr_has_level_param domain || expr_has_level_param body)
                (max (get_free_var_range domain) (get_free_var_range body - 1))) in
  case is_pi of
    True -> Pi (BindingData name domain body binfo ecache)
    False -> Lambda (BindingData name domain body binfo ecache)

mk_pi :: Name -> Expr -> Expr -> BinderInfo -> Expr
mk_pi = mk_binding True

mk_pi_default :: Expr -> Expr -> Expr
mk_pi_default domain body = mk_pi no_name domain body BinderDefault

mk_lambda :: Name -> Expr -> Expr -> BinderInfo -> Expr
mk_lambda = mk_binding False

mk_lambda_default :: Expr -> Expr -> Expr
mk_lambda_default domain body = mk_lambda no_name domain body BinderDefault

{- Updaters -}

update_local :: LocalData -> Expr -> Expr
update_local local new_type = mk_local (local_name local) (local_pp_name local) new_type (local_info local)

update_binding :: Bool -> BindingData -> Expr -> Expr -> Expr
update_binding is_pi bind new_domain new_body =
  mk_binding is_pi (binding_name bind) new_domain new_body (binding_info bind)

update_pi :: BindingData -> Expr -> Expr -> Expr
update_pi = update_binding True

update_lambda :: BindingData -> Expr -> Expr -> Expr
update_lambda = update_binding False

update_app :: AppData -> Expr -> Expr -> Expr
update_app app new_fn new_arg = mk_app new_fn new_arg

update_constant const levels = mk_constant (const_name const) levels
update_sort sort level = mk_sort level

{- Traversals -}

-- Replace
type Offset = Int
type ReplaceFn = (Expr -> Offset -> Maybe Expr)

replace_in_expr :: ReplaceFn -> Expr -> Expr
replace_in_expr f t = replace_in_expr_core f t 0
  where
    replace_in_expr_core :: ReplaceFn -> Expr -> Offset -> Expr
    replace_in_expr_core f t offset =
      case f t offset of
        Just t0 -> t0
        Nothing ->
          case t of
            Local local -> update_local local (replace_in_expr_core f (local_type local) offset)
            App app -> update_app app (replace_in_expr_core f (app_fn app) offset)
                       (replace_in_expr_core f (app_arg app) offset)
            Lambda lam -> update_lambda lam (replace_in_expr_core f (binding_domain lam) offset)
                          (replace_in_expr_core f (binding_body lam) (1+offset))
            Pi pi -> update_pi pi (replace_in_expr_core f (binding_domain pi) offset)
                     (replace_in_expr_core f (binding_body pi) (1+offset))
            _ -> t


-- Find
type FindFn = (Expr -> Offset -> Bool)
find_in_expr :: FindFn -> Expr -> Maybe Expr
find_in_expr f t = find_in_expr_core f t 0
  where
    find_in_expr_core :: FindFn -> Expr -> Offset -> Maybe Expr
    find_in_expr_core f t offset =
      if f t offset then Just t else
        case t of
          Local local -> find_in_expr_core f (local_type local) offset
          App app -> find_in_expr_core f (app_fn app) offset `mplus` find_in_expr_core f (app_arg app) offset
          Lambda lam -> find_in_expr_core f (binding_domain lam) offset `mplus` find_in_expr_core f (binding_body lam) (offset+1)
          Pi pi -> find_in_expr_core f (binding_domain pi) offset `mplus` find_in_expr_core f (binding_body pi) (offset+1)
          _ -> Nothing

-- Instantiate
instantiate_seq :: Expr -> [Expr] -> Expr
instantiate_seq e substs = replace_in_expr (instantiate_fn substs) e
  where
    instantiate_fn :: [Expr] -> ReplaceFn
    instantiate_fn substs e offset
      | offset >= get_free_var_range e = Just e

    instantiate_fn substs (Var var) offset
      | var_idx var >= offset && var_idx var < offset + length substs =
          Just $ lift_free_vars (substs !! (var_idx var - offset)) offset
      | var_idx var > offset = Just $ mk_var (var_idx var - length substs)

    instantiate_fn _ _ _ = Nothing

instantiate :: Expr -> Expr -> Expr
instantiate e subst = instantiate_seq e [subst]

-- Lift free vars
lift_free_vars :: Expr -> Int -> Expr
lift_free_vars e shift = replace_in_expr (lift_free_vars_fn shift) e
  where
    lift_free_vars_fn :: Offset -> ReplaceFn
    lift_free_vars_fn shift e offset
      | offset >= get_free_var_range e = Just e

    lift_free_vars_fn shift (Var var) offset
      | var_idx var >= offset = Just $ mk_var (var_idx var + shift)

    lift_free_vars_fn _ _ _ = Nothing


-- Instantiate universe params
instantiate_univ_params :: Expr -> [Name] -> [Level] -> Expr
instantiate_univ_params e level_names levels =
  replace_in_expr (instantiate_univ_params_fn level_names levels) e
  where
    instantiate_univ_params_fn :: [Name] -> [Level] -> ReplaceFn
    instantiate_univ_params_fn level_param_names levels e _
      | not (expr_has_level_param e) = Just e

    instantiate_univ_params_fn level_param_names levels (Constant const) _ =
      Just $ update_constant const (map (instantiate_level level_param_names levels) (const_levels const))

    instantiate_univ_params_fn level_param_names levels (Sort sort) _ =
      Just $ update_sort sort (instantiate_level level_param_names levels (sort_level sort))

    instantiate_univ_params_fn _ _ _ _ = Nothing

-- Abstract locals

abstract_pi local body = abstract_binding_seq True [local] body
abstract_lambda local body = abstract_binding_seq False [local] body

abstract_pi_seq locals body = abstract_binding_seq True locals body
abstract_lambda_seq locals body = abstract_binding_seq False locals body

abstract_binding_seq is_pi locals body =
  let abstract_body = abstract_locals locals body
      abstract_types = map (\(local,i) -> abstract_locals (List.take i locals) (local_type local)) (zip locals [0..])
  in
   foldr (\(abstract_type,local) new_body -> mk_binding is_pi (local_name local) abstract_type new_body (local_info local))
   abstract_body (zip abstract_types locals)

abstract_locals locals body = replace_in_expr (abstract_locals_fn locals) body
  where
    abstract_locals_fn :: [LocalData] -> ReplaceFn
    abstract_locals_fn locals e offset
      | not (expr_has_local e) = Just e

    abstract_locals_fn locals e@(Local l) offset =
      case List.findIndex (\local -> local_name local == local_name l) locals of
        Nothing -> Just e
        Just idx -> Just (mk_var $ offset + (length locals - 1 - idx))

    abstract_locals_fn _ _  _ = Nothing

-- Misc

body_of_lambda e = case e of
  Lambda lam -> body_of_lambda (binding_body lam)
  _ -> e

is_constant (Constant _) = True
is_constant _ = False

maybe_constant (Constant c) = Just c
maybe_constant _ = Nothing
