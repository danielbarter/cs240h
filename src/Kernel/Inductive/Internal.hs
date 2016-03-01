{-|
Module      : Kernel.Inductive.Internal
Description : Inductive type declarations
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of inductive type declaration processing.
The main roles of this module are:
1. To validate inductive type declarations
2. To compute the corresponding eliminator
3. To compute the corresponding computation rule
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Kernel.Inductive.Internal where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Level (Level)
import Kernel.Expr
import Kernel.Env
import Kernel.InductiveExt (IndDecl)
import qualified Kernel.InductiveExt as Ext
import qualified Kernel.TypeChecker as TC

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Lens.Simple (makeLenses, use, view, over, (%=), (.=), (%%=))

import Data.List (genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)
import qualified Data.Maybe as Maybe

import Debug.Trace

data IndDeclError = NumParamsMismatchInIndDecl Integer Integer
                        | ArgDoesNotMatchInductiveParameters Integer Name
                        | UniLevelOfArgTooBig Integer Name Level Level
                        | NonRecArgAfterRecArg Integer Name
                        | InvalidRecArg Integer Name
                        | InvalidReturnType Name
                        | NonPosOccurrence Integer Name
                        | NonValidOccurrence Integer Name
                        | TypeCheckError TC.TypeError String
                        deriving (Eq,Show)

data ElimInfo = ElimInfo {
  elimInfoC :: LocalData, -- type former constant
  elimInfoIndices :: [LocalData], --local constant for each index
  elimInfoMajorPremises :: LocalData, -- major premise for each inductive decl
  elimInfoMinorPremises :: [LocalData] -- minor premise for each introduction rule
} deriving (Eq,Show)

data AddInductiveS = AddInductiveS {
  -- TODO(dhs): much better to put these all in a different structure and populate them at once
  -- (or possibly into a few different ones if they are populated at different stages)
  _addIndEnv :: Env,
  _addIndIDecl :: IndDecl,

  _addIndIsDefinitelyNotZero :: Bool,
  _addIndNextId :: Integer,
  _addIndDepElim :: Bool,

  _addIndElimLevel :: Maybe Level,
  _addIndParamLocals :: Maybe [LocalData], -- local constants used to represent global parameters
  _addIndIndLevel :: Maybe Level, -- the levels for each inductive datatype in [m_idecls]
  _addIndIndConst :: Maybe ConstantData, -- the constants for each inductive datatype in [m_idecls]
  _addIndNumArgs :: Maybe Int, -- total number of arguments (params + indices) for each inductive datatype in m_idecls

  _addIndElimInfo :: Maybe ElimInfo,
  _addIndKTarget :: Bool
}

makeLenses ''AddInductiveS

mkAddInductiveS :: Env -> IndDecl -> AddInductiveS
mkAddInductiveS env idecl = AddInductiveS {
  _addIndEnv = env,
  _addIndIDecl = idecl,

  _addIndNextId = 0,

  _addIndIsDefinitelyNotZero = False,
  _addIndDepElim = False,
  _addIndElimLevel = Nothing,

  _addIndParamLocals = [],
  _addIndIndLevel = Nothing,
  _addIndIndConst = Nothing,
  _addIndNumArgs = Nothing,
  _addIndElimInfo = Nothing,
  _addIndKTarget = False
  }

type AddInductiveMethod = ExceptT IndDeclError (State AddInductiveS)

{- Misc -}
-- TODO(dhs): put these at the bottom

gensym :: AddInductiveMethod Int
gensym = addIndNextId %%= \n -> (n, n + 1)

mkLocalFor :: BindingData -> AddInductiveMethod LocalData
mkLocalFor bind = do
  nextId <- gensym
  return $ mkLocalData (mkSystemNameI nextId) (bindingName bind) (bindingDomain bind) (bindingInfo bind)

indAssert :: Bool -> IndDeclError -> AddInductiveMethod ()
indAssert b err = if b then return () else throwE err

-- TODO(dhs): why did old version add another layer to this?
mkFreshName :: AddInductiveMethod Name
mkFreshName = gensym >>= mkSystemNameI

addInductive :: Env -> IndDecl -> Either IndDeclError Env
addInductive env idecl =
  let (a, s) = runState (runExceptT addInductiveCore) (mkAddInductiveS env idecl) in
   case a of
    Left err -> Left err
    Right () -> Right $ view addIndEnv s

addInductiveCore :: AddInductiveMethod ()
addInductiveCore = do
  checkIndType
  declareIndType
  checkIntroRules
  declareIntroRules
  declareElimRules
  mkCompRules

checkIndType :: AddInductiveMethod ()
checkIndType = do
  (IndDecl numParams lpNames name ty introRules) <- asks _addIndIDecl
  checkType ty lpNames
  let (rest, paramLocals) = telescopePiN numParams ty
  indAssert (length paramLocals == numParams) $ NumParamsMismatchInIndDecl (length locals) numParams
  let (body, indexLocals) = telescopePi rest
  sort <- ensureSort body
  lpNames <- map mkLevelParam . indDeclLPNames <$> asks addIndIDecl
  addIndIsDefinitelyNotZero .= Level.isDefinitelyNotZero (sortLevel sort)
  addIndIndConst .= Just (ConstantData name lpNames)
  addIndIndLevel .= Just (sortLevel sort)
  addIndNumArgs .= Just (length indexLocals)
  addIndParamLocals .= Just paramLocals

-- Add all datatype declarations to environment.
declareIndType :: AddInductiveMethod ()
declareIndType = do
  idecl@(IndDecl numParams lpNames name ty introRules) <- use addIndIDecl
  -- TODO(dhs): put Env and TypeChecker in the same module, and only expose `envAddAxiom` and `envAddDefinition`
  addIndEnv %= envAddAxiom lpNames name ty
  addIndEnv %= envAddIndDecl idecl


{- Check if
   - all introduction rules start with the same parameters
   - the type of all arguments (which are not datatype global params) live in universes <= level of the corresponding datatype
   - all inductive datatype occurrences are positive
   - all introduction rules are well typed

   Note: this method must be executed after declareIndType
-}
checkIntroRules :: AddInductiveMethod ()
checkIntroRules = do
  (IndDecl numParams lpNames name ty introRules) <- use addIndIDecl
  mapM_ checkIntroRule introRules
    where
      checkIntroRule :: IntroRule -> AddInductiveMethod ()
      checkIntroRule (IntroRule name ty) = do
        checkType ty lpNames
        checkIntroRuleCore 0 False name ty

      checkIntroRuleCore :: Int -> Bool -> Name -> Expr -> AddInductiveMethod ()
      checkIntroRuleCore paramNum foundRec name ty =
        case ty of
         Pi pi -> do
           numParams <- use (addIndIDecl . indDeclNumParams)
           paramLocals <- use addIndParamLocals
           if paramNum < numParams
             then do let local = paramLocals !! paramNum
                     isDefEq (bindingDomain pi) (localType local) >>=
                       flip indAssert (ArgDoesNotMatchInductiveParameters paramNum name)
                     checkIntroRuleCore (paramNum+1) foundRec name (instantiate (bindingBody pi) (Local local))
             else do sort <- ensureType (bindingDomain pi)
                     indLevel <- liftM Maybe.fromJust $ use addIndIndLevel
                     env <- use addIndEnv
                     indAssert (levelNotBiggerThan (sortLevel sort) indLevel || (isZero indLevel && envPropImpredicative env))
                       (UniLevelOfArgTooBig paramNum name (sortLevel sort) indLevel)
                     domainTy <- whnf (bindingDomain pi)
                     checkPositivity domainTy name paramNum
                     argIsRec <- isRecArg domainTy
                     indAssert (not foundRec || argIsRec) (NonRecArgAfterRecArg paramNum name)
                     ty <- if argIsRec
                           then indAssert (closed (bindingBody pi)) (InvalidRecArg paramNum name) >> return (bindingBody pi)
                           else mkLocalFor pi >>= return . instantiate (bindingBody pi) . Local
                     checkIntroRuleCore (paramNum+1) argIsRec name ty
         _ -> isValidIndApp ty >>= flip indAssert (InvalidReturnType name)


{-




-- Check if ty contains only positive occurrences of the inductive datatypes being declared.
check_positivity ty name paramNum = do
  ty <- whnf ty
  it_occ <- has_it_occ ty
  if not it_occ then return () else
    case ty of
      Pi pi -> do it_occ <- has_it_occ (bindingDomain pi)
                  ind_assert (not it_occ) (NonPosOccurrence paramNum name)
                  local <- mk_local_for pi
                  check_positivity (instantiate (bindingBody pi) $ Local local) name paramNum
      _ -> is_valid_it_app ty >>= flip ind_assert (NonValidOccurrence paramNum name)

-- Return true if ty does not contain any occurrence of a datatype being declared.
has_it_occ ty = do
  it_consts <- gets m_it_consts
  return . Maybe.isJust $ find_in_expr (\e _ -> case e of
                            Constant const -> const_name const `elem` (map const_name it_consts)
                            _ -> False) ty

{- Return some(d_idx) iff \c t is a recursive argument, \c d_idx is the index of the recursive inductive datatype.
   Return none otherwise. -}
is_rec_argument ty = do
  ty <- whnf ty
  case ty of
    Pi pi -> mk_local_for pi >>= is_rec_argument . (instantiate (bindingBody pi)) . Local
    _ -> is_valid_it_app ty

is_valid_it_app_idx :: Expression -> Integer -> AddInductiveMethod Bool
is_valid_it_app_idx ty d_idx = do
  it_const <- liftM (flip genericIndex d_idx . m_it_consts) get
  num_args <- liftM (flip genericIndex d_idx . m_it_num_args) get
  (fn,args) <- return $ (get_operator ty,get_app_args ty)
  is_eq <- is_def_eq fn (Constant it_const)
  param_consts <- gets m_param_consts
  return $ is_eq && genericLength args == num_args && all (uncurry (==)) (zip args (map Local param_consts))

is_valid_it_app :: Expression -> AddInductiveMethod Bool
is_valid_it_app ty = do
  valid_it_app <- runExceptT (is_valid_it_app_core ty)
  case valid_it_app of
    Left d_idx -> return True
    Right () -> return False

get_valid_it_app_idx ty = do
  valid_it_app <- runExceptT (is_valid_it_app_core ty)
  case valid_it_app of
    Left d_idx -> return $ Just d_idx
    Right () -> return $ Nothing

is_valid_it_app_core :: Expression -> ExceptT Integer AddInductiveMethod ()
is_valid_it_app_core ty = do
  it_consts <- gets m_it_consts
  mapM_ (\d_idx -> do is_valid <- lift $ is_valid_it_app_idx ty d_idx
                      if is_valid then throwE d_idx else return ())
    [0..(genericLength it_consts - 1)]

-- Add all introduction rules (aka constructors) to environment.
declareIntroRules =
  gets m_idecls >>=
  mapM_ (\(IndDecl it_name _ intro_rules) -> do
            mapM_ (\(IntroRule ir_name ty) -> do
                      level_names <- gets m_level_names
                      cdecl <- certify_declaration ir_name level_names ty
                      update_m_env (flip env_add cdecl)
                      ext_add_intro_info ir_name it_name)
              intro_rules)

-- Declare the eliminator/recursor for each datatype.
declareElimRules = do
  init_dep_elim
  init_elim_level
  init_elim_info
  idecls <- gets m_idecls
  mapM_ (uncurry declare_elim_rule) (zip idecls [0..])

init_dep_elim = do
  env <- gets m_env
  it_levels <- gets m_it_levels
  case it_levels of
    it_level : _ ->
      modify (\ind_data -> ind_data { m_dep_elim = not (is_impredicative env && is_prop_proof_irrel env && is_zero it_level) })

-- Return true if type formers C in the recursors can only map to Type.{0}
elim_only_at_universe_zero = do
  only_at_zero <- runExceptT elim_only_at_universe_zero_core
  case only_at_zero of
    Left b -> return b
    Right () -> return False

elim_only_at_universe_zero_core :: ExceptT Bool AddInductiveMethod ()
elim_only_at_universe_zero_core = do
  env <- gets m_env
  idecls <- gets m_idecls
  is_not_zero <- gets m_is_not_zero
  if is_impredicative env && is_not_zero then throwE False else return ()
  case idecls of
    d1:d2:_ -> throwE True
    [(IndDecl _ _ [])] -> throwE False
    [(IndDecl _ _ (_:_:_))] -> throwE True
    [(IndDecl _ _ [(IntroRule name ty)])] -> do
      {- We have only one introduction rule, the final check is, the type of each argument that is not a parameter:
          1- It must live in Type.{0}, *OR*
          2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
             We can justify 2 by observing that this information is not a *secret* it is part of the type.
             By eliminating to a non-proposition, we would not be revealing anything that is not already known. -}
      (ty,args_to_check) <- lift $ check_condition1 ty 0
      result_args <- return $ get_app_args ty
      mapM_ (\arg_to_check -> if not (arg_to_check `elem` result_args) then throwE True else return ())
        (map Local args_to_check)

check_condition1 :: Expression -> Integer -> AddInductiveMethod (Expression,[LocalData])
check_condition1 (Pi pi) paramNum = do
  local <- mk_local_for pi
  body <- return $ instantiate (bindingBody pi) (Local local)
  (ty,rest) <- check_condition1 body (paramNum+1)
  num_params <- gets m_num_params
  if paramNum >= num_params
    then do sort <- ensure_type (bindingDomain pi)
            return $ if not (is_zero (sort_level sort)) then (ty,local : rest) else (ty,rest)
    else return (ty,rest)

check_condition1 ty _ = return (ty,[])

-- Initialize m_elim_level.
init_elim_level = do
  only_at_zero <- elim_only_at_universe_zero
  if only_at_zero
    then modify (\ind_data -> ind_data { m_elim_level = Just mk_zero })
    else modify (\ind_data -> ind_data { m_elim_level = Just (mk_level_param (mk_system_name_s "elim_level")) })

init_elim_info = do
  idecls <- gets m_idecls
  mapM_ (uncurry populate_C_indices_major) (zip idecls [0..])
  mapM_ (uncurry populate_minor_premises) (zip idecls [0..])

populate_C_indices_major :: IndDecl -> Integer -> AddInductiveMethod ()
populate_C_indices_major (IndDecl name ty intro_rules) d_idx = do
  (indices,body) <- build_indices ty 0
  fresh_name_major <- mk_fresh_name
  it_consts <- gets m_it_consts
  param_consts <- gets m_param_consts
  major_premise <- return $ mk_local_data fresh_name_major (mk_name ["n"])
                   (mk_app_seq (mk_app_seq
                                (Constant $ genericIndex it_consts d_idx) (map Local param_consts))
                    (map Local indices))
  elim_level <- gets m_elim_level
  c_ty <- return $ mk_sort (Maybe.fromJust elim_level)
  dep_elim <- gets m_dep_elim
  c_ty <- return $ if dep_elim then abstract_pi major_premise c_ty else c_ty
  c_ty <- return $ abstract_pi_seq indices c_ty
  num_its <- liftM (genericLength . m_idecls) get
  c_name <- return $ if num_its > 1 then name_append_i (mk_name ["C"]) d_idx else mk_name ["C"]
  fresh_name_C <- mk_fresh_name
  c <- return $ mk_local_data fresh_name_C c_name c_ty
  modify (\ind_data -> ind_data { m_elim_infos = (m_elim_infos ind_data) ++ [ElimInfo c indices major_premise []] })

build_indices :: Expression -> Integer -> AddInductiveMethod ([LocalData],Expression)
build_indices (Pi pi) paramNum = do
  num_params <- gets m_num_params
  use_param <- return $ paramNum < num_params
  local <- if use_param
           then liftM (flip genericIndex paramNum . m_param_consts) get
           else mk_local_for pi
  (indices,body) <- build_indices (instantiate (bindingBody pi) (Local local)) (paramNum+1)
  if use_param
    then return (indices,body)
    else return (local:indices,body)

build_indices ty paramNum = return ([],ty)

populate_minor_premises :: IndDecl -> Integer -> AddInductiveMethod ()
populate_minor_premises (IndDecl name ty intro_rules) d_idx = do
  env <- gets m_env
  it_level <- liftM (flip genericIndex d_idx . m_it_levels) get
  -- A declaration is target for K-like reduction when it has one intro,
  -- the intro has 0 arguments, proof irrelevance is enabled, and it is a proposition.
  modify (\ind_data -> ind_data { m_K_target = is_prop_proof_irrel env && is_zero it_level && length intro_rules == 1 })
  -- In the populate_minor_premises_intro_rule we check if the intro rule has 0 arguments.
  mapM_ (populate_minor_premises_ir d_idx) intro_rules

build_ir_args rec_args nonrec_args ir_name ir_type paramNum = do
  num_params <- gets m_num_params
  param_const <- liftM (flip genericIndex paramNum . m_param_consts) get
  case ir_type of
    Pi pi | paramNum < num_params -> build_ir_args rec_args nonrec_args ir_name (instantiate (bindingBody pi) (Local param_const)) (paramNum+1)
          | otherwise -> do
      -- intro rule has an argument
      modify (\ind_data -> ind_data { m_K_target = False })
      local <- mk_local_for pi
      is_rec_arg <- is_rec_argument (bindingDomain pi)
      if is_rec_arg
        then build_ir_args (rec_args ++ [local]) nonrec_args ir_name (instantiate (bindingBody pi) (Local local)) (paramNum+1)
        else build_ir_args rec_args (nonrec_args ++ [local]) ir_name (instantiate (bindingBody pi) (Local local)) (paramNum+1)
    _ -> return (rec_args,nonrec_args,ir_type)

populate_minor_premises_ir d_idx (IntroRule ir_name ir_type) = do
  (rec_args,nonrec_args,ir_type) <- build_ir_args [] [] ir_name ir_type 0
  ir_type <- whnf ir_type
  (it_idx,it_indices) <- get_I_indices ir_type
  elim_infos <- gets m_elim_infos
  c_app <- return $ mk_app_seq (Local . m_C $ genericIndex elim_infos it_idx) it_indices
  dep_elim <- gets m_dep_elim
  levels <- gets m_levels
  param_consts <- gets m_param_consts
  c_app <- return $ if dep_elim then
                      let intro_app = mk_app_seq
                                      (mk_app_seq
                                       (mk_app_seq (mk_constant ir_name levels) (map Local param_consts))
                                       (map Local nonrec_args))
                                      (map Local rec_args) in
                      mk_app c_app intro_app
                    else c_app
  -- populate ind_args given rec_args
  -- we have one ind_arg for each rec_arg
  -- whenever we take an argument of the form (Pi other_type ind_type), we get to assume `C` holds for every possible output
  ind_args <- build_ind_args (zip rec_args [0..])
  fresh_name_minor <- mk_fresh_name
  minor_ty <- return $ abstract_pi_seq nonrec_args
              (abstract_pi_seq rec_args
               (abstract_pi_seq ind_args c_app))
  minor_premise <- return $ mk_local_data fresh_name_minor (name_append_i (mk_name ["e"]) d_idx) minor_ty
  push_minor_premise d_idx minor_premise

build_xs rec_arg_ty xs =
  case rec_arg_ty of
    Pi pi -> mk_local_for pi >>= (\x -> build_xs (instantiate (bindingBody pi) (Local x)) (xs ++ [x]))
    _ -> return (xs,rec_arg_ty)

build_ind_args [] = return []
build_ind_args ((rec_arg,rec_arg_num):rest) = do
  rest_ind_args <- build_ind_args rest
  rec_arg_ty <- whnf (local_type rec_arg)
  (xs,rec_arg_ty) <- build_xs rec_arg_ty []
  rec_arg_ty <- whnf rec_arg_ty
  (it_idx,it_indices) <- get_I_indices rec_arg_ty
  c <- liftM (m_C . (flip genericIndex it_idx) . m_elim_infos) get
  c_app <- return $ mk_app_seq (Local c) it_indices
  dep_elim <- gets m_dep_elim
  c_app <- return $ if dep_elim then mk_app c_app (mk_app_seq (Local rec_arg) (map Local xs)) else c_app
  ind_arg_ty <- return $ abstract_pi_seq xs c_app
  fresh_name_ind_arg <- mk_fresh_name
  ind_arg <- return $ mk_local_data fresh_name_ind_arg (name_append_i (mk_name ["v"]) rec_arg_num) ind_arg_ty
  return $ ind_arg:rest_ind_args

{- Given t of the form (I As is) where I is one of the inductive datatypes being defined,
   As are the global parameters, and `is` the actual indices provided to it.
   Return the index of I, and store is in the argument \c indices. -}
get_I_indices rec_arg_ty = do
  maybe_it_idx <- get_valid_it_app_idx rec_arg_ty
  num_params <- gets m_num_params
  case maybe_it_idx of
    Just d_idx -> return (d_idx,genericDrop num_params (get_app_args rec_arg_ty))

declare_elim_rule (IndDecl name ty intro_rules) d_idx = do
  elim_info <- liftM (flip genericIndex d_idx . m_elim_infos) get
  c_app <- return $ mk_app_seq (Local $ m_C elim_info) (map Local $ m_indices elim_info)
  dep_elim <- gets m_dep_elim
  c_app <- return $ if dep_elim then mk_app c_app (Local $ m_major_premise elim_info) else c_app
  elim_type <- return $ abstract_pi (m_major_premise elim_info) c_app
  elim_type <- return $ abstract_pi_seq (m_indices elim_info) elim_type
  elim_type <- abstract_all_introduction_rules elim_type
  elim_type <- abstract_all_type_formers elim_type
  param_consts <- gets m_param_consts
  elim_type <- return $ abstract_pi_seq param_consts elim_type
  level_names <- get_elim_level_param_names
  cdecl <- certify_declaration (get_elim_name name) level_names elim_type
  update_m_env (flip env_add cdecl)

get_elim_name name = name_append_s name "rec"
get_elim_name_idx it_idx = do
  idecls <- gets m_idecls
  case genericIndex idecls it_idx of
    IndDecl name _ _ -> return $ get_elim_name name

abstract_all_introduction_rules elim_type =
  gets m_elim_infos >>= return .
  (foldr (\(ElimInfo _ _ _ minor_premises) elim_type ->
          foldr (\minor_premise elim_type ->
                  abstract_pi minor_premise elim_type)
          elim_type
          minor_premises)
    elim_type)

abstract_all_type_formers elim_type =
  gets m_elim_infos >>= return . (foldr (\(ElimInfo c _ _ _) elim_type -> abstract_pi c elim_type) elim_type)

get_elim_level_params = do
  elim_level <- gets m_elim_level
  levels <- gets m_levels
  case elim_level of
    Just el@(LevelParam l) -> return $ el : levels
    _ -> return levels

get_elim_level_param_names = do
  elim_level <- gets m_elim_level
  level_names <- gets m_level_names
  case elim_level of
    Just (LevelParam l) -> return $ l : level_names
    _ -> return level_names

-- | Create computional rules RHS. They are used by the normalizer extension.
mkCompRules = do
  idecls <- gets m_idecls
  elim_infos <- gets m_elim_infos
  mapM_ (uncurry mkCompRules_idecl) (zip idecls elim_infos)

mkCompRules_idecl (IndDecl name ty intro_rules) (ElimInfo _ indices _ minor_premises) = do
  ext_add_elim name (genericLength indices)
  mapM_ (uncurry $ register_comp_rhs name) (zip intro_rules minor_premises)

register_comp_rhs ind_name (IntroRule ir_name ir_type) minor_premise = do
  (rec_args,nonrec_args,ir_type) <- build_ir_args [] [] ir_name ir_type 0
  e_app <- build_e_app rec_args
  e_app <- return $ mk_app_seq (mk_app_seq (mk_app_seq (Local minor_premise) (map Local nonrec_args))
                                (map Local rec_args)) e_app
  param_consts <- gets m_param_consts
  cs <- liftM (map m_C . m_elim_infos) get
  minor_premises <- liftM (concat . map m_minor_premises . m_elim_infos) get
  comp_rhs <- return $
              abstract_lambda_seq param_consts
              (abstract_lambda_seq cs
               (abstract_lambda_seq minor_premises
                (abstract_lambda_seq nonrec_args
                 (abstract_lambda_seq rec_args e_app))))
  level_param_names <- get_elim_level_param_names
  check_type comp_rhs level_param_names
  ext_add_comp_rhs ir_name (get_elim_name ind_name) (genericLength rec_args + genericLength nonrec_args) comp_rhs

build_e_app [] = return []
build_e_app (rec_arg:rest) = do
  rest_rhs <- build_e_app rest
  rec_arg_ty <- whnf (local_type rec_arg)
  (xs,rec_arg_ty) <- build_xs rec_arg_ty []
  rec_arg_ty <- whnf rec_arg_ty
  (it_idx,it_indices) <- get_I_indices rec_arg_ty
  ls <- get_elim_level_params
  param_consts <- gets m_param_consts
  elim_infos <- gets m_elim_infos
  elim_name <- get_elim_name_idx it_idx
  elim_app <- return $ mk_constant elim_name ls
  elim_app <- return $ mk_app
              (mk_app_seq
               (mk_app_seq
                (mk_app_seq
                 (mk_app_seq elim_app (map Local param_consts))
                 (map (Local . m_C) elim_infos))
                (map Local . concat $ map m_minor_premises elim_infos))
               it_indices)
              (mk_app_seq (Local rec_arg) (map Local xs))
  return $ (abstract_lambda_seq xs elim_app):rest_rhs

{- Wrappers for the type checker -}

check_type e level_names = do
  env <- gets m_env
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.infer_type e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "check_type"
    Right (e,next) -> modify (\tc -> tc { m_next_id = next }) >> return e

ensure_sort e = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.ensure_sort e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "ensure_sort"
    Right (sort,next) -> modify (\tc -> tc { m_next_id = next }) >> return sort

ensure_type e = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.ensure_type e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "ensure_type"
    Right (sort,next) -> modify (\tc -> tc { m_next_id = next }) >> return sort

is_def_eq e1 e2 = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.is_def_eq e1 e2) of
    Left tc_err -> throwE $ TypeCheckError tc_err "is_def_eq"
    Right (b,next) -> modify (\tc -> tc { m_next_id = next }) >> return b

certify_ideclaration :: IndDecl -> AddInductiveMethod CertifiedDeclaration
certify_ideclaration (IndDecl name ty intro_rules) = do
  level_names <- gets m_level_names
  certify_declaration name level_names ty

certify_declaration :: Name -> [Name] -> Expression -> AddInductiveMethod CertifiedDeclaration
certify_declaration name level_names ty = do
  env <- gets m_env
  next_id <- gets m_next_id
  let decl = mk_axiom name level_names ty in
    case TypeChecker.tc_eval env level_names next_id (TypeChecker.check_main decl) of
      Left tc_err -> throwE $ TypeCheckError tc_err "certify_declaration"
      Right (cdecl,next) -> modify (\tc -> tc { m_next_id = next }) >> return cdecl

whnf e = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.whnf e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "whnf"
    Right (e,next) -> modify (\tc -> tc { m_next_id = next }) >> return e


-- Other helpers
replaceAtIndex ls n item = a ++ (item:b) where (a, (_:b)) = genericSplitAt n ls

push_minor_premise d_idx minor_premise = do
  elim_infos <- gets m_elim_infos
  let old_elim_info = genericIndex elim_infos d_idx
      old_minor_premises = m_minor_premises old_elim_info
      new_elim_info = old_elim_info { m_minor_premises = old_minor_premises ++ [minor_premise] }
    in
   modify (\ind_data -> ind_data { m_elim_infos = replaceAtIndex elim_infos d_idx new_elim_info })

update_m_env f = do
  env <- gets m_env
  modify (\ind_data -> ind_data { m_env = f env })

{- Extensions -}


ext_add_intro_info ir_name ind_name = update_m_env $ ind_ext_add_intro_info ir_name ind_name

ext_add_elim ind_name num_indices = do
  elim_level_param_names <- get_elim_level_param_names
  ind_data <- get
  num_cs <- liftM (genericLength . m_idecls) get
  num_minor_ps <- return $ sum $ map (genericLength . m_minor_premises) $ m_elim_infos ind_data
  update_m_env (ind_ext_add_elim
                (get_elim_name ind_name)
                ind_name
                elim_level_param_names
                (m_num_params ind_data)
                (m_num_params ind_data + num_cs + num_minor_ps)
                (num_indices)
                (m_K_target ind_data)
                (m_dep_elim ind_data))


ext_add_comp_rhs ir_name elim_name num_rec_args_nonrec_args comp_rhs =
  update_m_env (ind_ext_add_comp_rhs ir_name elim_name num_rec_args_nonrec_args comp_rhs)
-}
