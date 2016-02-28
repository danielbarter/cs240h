{-|
Module      : Kernel.Env.Internal
Description : Environments
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of environments
-}
{-# LANGUAGE TemplateHaskell #-}
module Kernel.Env.Internal where

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Expr
import Kernel.InductiveExt

import Lens.Simple

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Maybe as Maybe

data Decl = Decl {
  declName :: Name,
  declLevelParamNames :: [Name],
  declType :: Expr,
  declVal :: Maybe Expr,
  declWeight :: Int
  } deriving (Eq,Show)

data Env = Env {
  _envDeclarations :: Map Name Decl,
  _envGlobalNames :: Set Name,
  _envInductiveExt :: InductiveExt,
  _envQuotEnabled :: Bool,
  _envPropProofIrrel :: Bool,
  _envPropImpredicative :: Bool
  } deriving (Show)

makeLenses ''Env

{-
envAddInductiveDecl :: InductiveDecl -> Env -> Env
envAddInductiveDecl idecl env = over (

                                              data InductiveDecl = InductiveDecl {
  indDeclLevelParamNames :: [Name],
  indDeclNumParams :: Integer,
  indDeclName :: Name,
  indDeclType :: Expr,
  indDeclIntroRules :: [IntroRule]
  } deriving (Show)

ind_ext_add_inductive_info level_param_names num_params idecls env =
  let old_env_ind_ext = env_ind_ext env
      old_iext_ind_infos = iext_ind_infos old_env_ind_ext
      new_iext_ind_infos =
        foldl (\ind_infos idecl@(InductiveDecl name ty intro_rules) ->
                Map.insert name (MutualInductiveDecl level_param_names num_params idecls) ind_infos) old_iext_ind_infos idecls
      new_env_ind_ext = old_env_ind_ext { iext_ind_infos = new_iext_ind_infos }
  in
   env { env_ind_ext = new_env_ind_ext }

ind_ext_add_intro_info :: Name -> Name -> Env -> Env
ind_ext_add_intro_info ir_name ind_name env =
  let old_env_ind_ext = env_ind_ext env
      old_m = iext_ir_name_to_ind_name old_env_ind_ext
  in
   env { env_ind_ext = old_env_ind_ext { iext_ir_name_to_ind_name = Map.insert ir_name ind_name old_m } }

ind_ext_add_elim :: Name -> Name -> [Name] -> Int -> Int -> Int -> Bool -> Bool -> Env -> Env
ind_ext_add_elim elim_name ind_name level_param_names num_params num_ACe num_indices is_K_target dep_elim env =
  let old_env_ind_ext = env_ind_ext env
      old_m = iext_elim_infos old_env_ind_ext
      new_elim_info = ExtElimInfo ind_name level_param_names num_params num_ACe num_indices is_K_target dep_elim
  in
   env { env_ind_ext = old_env_ind_ext { iext_elim_infos = Map.insert elim_name new_elim_info old_m } }

ind_ext_add_comp_rhs :: Name -> Name  ir_name elim_name num_rec_args_nonrec_args rhs env =
ind_ext_add_comp_rhs ir_name elim_name num_rec_args_nonrec_args rhs env =
  let old_env_ind_ext = env_ind_ext env
      old_m = iext_comp_rules old_env_ind_ext
      new_comp_rule = CompRule elim_name num_rec_args_nonrec_args rhs
  in
   env { env_ind_ext = old_env_ind_ext { iext_comp_rules = Map.insert ir_name new_comp_rule old_m } }

---------------

mkDefinition :: Env -> Name -> [Name] -> Expr -> Expr -> Declaration
mkDefinition env name level_param_names t v =
  Declaration name level_param_names t (Just v) (1 + get_max_decl_weight env v)

mk_axiom name level_param_names t =
  Declaration name level_param_names t Nothing 0

is_definition decl = Maybe.isJust (decl_mb_val decl)

get_max_decl_weight env e = case e of
  Var var -> 0
  Local local -> get_max_decl_weight env (local_type local)
  Constant const -> maybe 0 decl_weight (lookup_declaration env (const_name const))
  Sort _ -> 0
  Lambda lam -> get_max_decl_weight env (binding_domain lam) `max` get_max_decl_weight env (binding_body lam)
  Pi pi -> get_max_decl_weight env (binding_domain pi) `max` get_max_decl_weight env (binding_body pi)
  App app -> get_max_decl_weight env (app_fn app) `max` get_max_decl_weight env (app_arg app)

-- Environments

is_impredicative :: Environment -> Bool
is_impredicative env = True -- TODO

is_prop_proof_irrel :: Environment -> Bool
is_prop_proof_irrel env = True -- TODO

lookup_declaration :: Environment -> Name -> Maybe Declaration
lookup_declaration env name = Map.lookup name (env_declarations env)

empty_environment = Environment { env_declarations = Map.empty,
                                  env_global_names = Set.empty,
                                  env_ind_ext = default_inductive_env_ext,
                                  env_quot_enabled = True }

-- TODO confirm environment is a descendent of the current one
-- or maybe make the kernel responsible for adding it
env_add :: Environment -> CertifiedDeclaration -> Environment
env_add env cdecl = case lookup_declaration env (decl_name (cdecl_decl cdecl)) of
  Nothing -> env { env_declarations = Map.insert (decl_name (cdecl_decl cdecl)) (cdecl_decl cdecl) (env_declarations env) }
  Just decl -> error "Already defined this guy, but the TypeChecker should have caught this already, will refactor later"

-- TODO return either
env_add_uni :: Environment -> Name -> Environment
env_add_uni env name = case Set.member name (env_global_names env) of
  False -> env { env_global_names = Set.insert name (env_global_names env) }
  True -> error "Already defined global universe, but interpreter should have caught this already, will refactor later"
-}
