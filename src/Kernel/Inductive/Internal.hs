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
import Kernel.Level
import Kernel.Expr
import Kernel.TypeChecker (IndDecl(IndDecl)
                           , indDeclNumParams, indDeclLPNames, indDeclName, indDeclType, indDeclIntroRules
                           , IntroRule(IntroRule)
                           , Env
                           , envAddIndDecl, envAddIntroRule, envAddElimInfo, envAddCompRule, envLookupDecl
                           , envPropProofIrrel, envPropImpredicative
                           , envAddAxiom
                           , TypeError, TCMethod)

import qualified Kernel.TypeChecker as TC

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Lens.Simple (makeLenses, use, uses, view, over, (%=), (.=), (%%=))

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
  _addIndIndexLocals :: Maybe [LocalData], -- local constants used to represent indices
  _addIndIndBody :: Maybe Expr, -- inner body of indType
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

  _addIndParamLocals = Nothing,
  _addIndIndexLocals = Nothing,
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

indAssert :: IndDeclError -> Bool -> AddInductiveMethod ()
indAssert err b = if b then return () else throwE err

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
  indAssert (length paramLocals == numParams) $ NumParamsMismatchInIndDecl (length paramLocals) numParams
  let (body, indexLocals) = telescopePi rest
  sort <- ensureSort body
  lpNames <- map mkLevelParam . indDeclLPNames <$> asks addIndIDecl
  addIndIsDefinitelyNotZero .= isDefinitelyNotZero (sortLevel sort)
  addIndIndConst .= Just (ConstantData name lpNames)
  addIndIndLevel .= Just (sortLevel sort)
  addIndNumArgs .= Just (length indexLocals)
  addIndParamLocals .= Just paramLocals
  addIndIndexLocals .= Just indexLocals
  addIndIndBody .= Just body

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
  mapM_ (checkIntroRule lpNames) introRules
    where
      checkIntroRule :: [Name] -> IntroRule -> AddInductiveMethod ()
      checkIntroRule lpNames (IntroRule name ty) = do
        checkType ty lpNames
        checkIntroRuleCore 0 False name ty

      checkIntroRuleCore :: Int -> Bool -> Name -> Expr -> AddInductiveMethod ()
      checkIntroRuleCore paramNum foundRec name ty =
        case ty of
         Pi pi -> do
           numParams <- use (addIndIDecl . indDeclNumParams)
           paramLocals <- liftM Maybe.fromJust $ use addIndParamLocals
           if paramNum < numParams
             then do let local = paramLocals !! paramNum
                     isDefEq (bindingDomain pi) (localType local) >>=
                       indAssert (ArgDoesNotMatchInductiveParameters paramNum name)
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
         _ -> isValidIndApp ty >>= indAssert (InvalidReturnType name)


      checkPositivity :: Expr -> Name -> Int -> AddInductiveMethod ()
      checkPositivity ty name paramNum = do
        ty <- whnf ty
        itOccurs <- indTypeOccurs ty
        if not itOccurs then return () else
          case ty of
           Pi pi -> do indTypeOccurs (bindingDomain pi) >>= flip indAssert (NonPosOccurrence paramNum name) . not
                       local <- mkLocalFor pi
                       checkPositivity (instantiate (bindingBody pi) $ Local local) name paramNum
           _ -> isValidIndApp ty >>= flip indAssert (NonValidOccurrence paramNum name)

      indTypeOccurs :: Expr -> AddInductiveMethod Bool
      indTypeOccurs e = do
        indTypeConst <- liftM Maybe.fromJust $ use addIndIndConst
        return . Maybe.isJust $ findInExpr (\e _ -> case e of
                                             Constant const -> constName const == constName indTypeConst
                                             _ -> False) e

      isValidIndApp :: Expr -> AddInductiveMethod Bool
      isValidIndApp e = do
        indTypeConst <- liftM Maybe.fromJust $ use addIndIndConst
        paramLocals <- liftM Maybe.fromJust $ use addIndParamLocals
        numArgs <- use addIndNumArgs
        let (op, args) = getAppOpArgs e
        opEq <- isDefEq op (Constant indTypeConst)
        return $ opEq && length args == numArgs && all (uncurry (==)) (zip args (map Local paramLocals))

      isRecArg :: Expr -> AddInductiveMethod Bool
      isRecArg e = do
        e <- whnf e
        case e of
         Pi pi -> mkLocalFor pi >>= isRecArg . (instantiate (bindingBody pi)) . Local
         _ -> isValidIndApp e

declareIntroRules :: AddInductiveMethod ()
declareIntroRules = do
  (IndDecl _ lpNames itName _ introRules) <- use addIndIDecl
  mapM_ (\(IntroRule irName irType) -> envAddAxiom irName lpNames irType >> envAddIntroRule irName itName) introRules

-- Declare the eliminator/recursor for each datatype.
declareElimRule :: AddInductiveMethod ()
declareElimRule = do
  initDepElim
  initElimLevel
  initElimInfo
  liftM declareElimRule $ use addIndIDecl
  where
    initDepElim :: AddInductiveMethod ()
    initDepElim = do
      env <- use addIndEnv
      indLevel <- use addIndIndLevel
      addIndDepElim .= not (envPropImpredicative env && envPropProofIrrel env && isZero indLevel)

    initElimLevel :: AddInductiveMethod ()
    initElimLevel = do
      onlyAtZero <- elimOnlyAtLevelZero
      if onlyAtZero
        then addIndElimLevel .= Just mkZero
        else addIndElimLevel .= Just (mkLevelParam (mkSystemNameS "elimLevel"))

    -- Return true if type formers C in the recursors can only map to Type.{0}
    elimOnlyAtLevelZero :: AddInductiveMethod Bool
    elimOnlyAtLevelZero = do
      env <- use addIndEnv
      isDefinitelyNotZero <- use addIndIsDefinitelyNotZero
      if envPropImpredicative env && isDefinitelyNotZero then return False else do
        (IndDecl _ _ _ _ introRules) <- use addIndIDecl
        case introRules of
         [] -> return False
         (_:_:_) -> return True
         [IntroRule irName irType] -> do
         {- We have only one introduction rule, the final check is, the type of each argument that is not a parameter:
          1- It must live in Type.{0}, *OR*
          2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
             We can justify 2 by observing that this information is not a *secret* it is part of the type.
             By eliminating to a non-proposition, we would not be revealing anything that is not already known. -}
           (irBodyType, argsToCheck) <- collectArgsToCheck irType 0
           let resultArgs = getAppArgs irBodyType
           results <- mapM (\argToCheck -> if not (argToCheck `elem` resultArgs) then return True else return False) $ map Local argsToCheck
           return $ any results

    {- We proceed through the arguments to the introRule, and return (innerBody, [locals for all (non-param) args that do not live in Prop]) -}
    collectArgsToCheck :: Expr -> Integer -> AddInductiveMethod (Expr, [LocalData])
    collectArgsToCheck ty paramNum =
      case ty of
        Pi pi -> do local <- mkLocalFor pi
                    let body = instantiate (bindingBody pi) (Local local)
                    (ty, rest) <- collectArgsToCheck body (paramNum+1)
                    numParams <- use (addIndIDecl . indDeclNumParams)
                    if paramNum >= numParams
                    then do sort <- ensureType (bindingDomain pi)
                            return $ if not (isZero (sortLevel sort)) then (ty, local : rest) else (ty, rest)
                    else return (ty, rest)
        _ -> return (ty, [])


    initElimInfo :: AddInductiveMethod ()
    initElimInfo = initCIndicesMajor >> initMinorPremises

    initCIndicesMajor :: AddInductiveMethod ()
    initCIndicesMajor = do (IndDecl _ _ indName indType introRules) <- use addIndIDecl
                           paramLocals <- use addIndParamLocals
                           indexLocals <- use addIndIndexLocals
                           indBody <-use addIndIndBody
                           indConst <- use addIndIndConst
                           majorName <- mkFreshName
                           let majorPremise = mkLocalData majorName (mkName ["major"])
                                              (mkAppSeq (mkAppSeq (Constant indConst) (map Local paramLocals))
                                                            (map Local indexLocals))
                           elimLevel <- liftM Maybe.fromJust $ use addIndElimLevel
                           depElim <- liftM Maybe.fromJust $ use addIndDepElim
                           let cType0 = mkSort elimLevel
                           let cType1 = if depElim then abstractPi majorPremise cType0 else cType0
                           let cType2 = abstractPiSeq indexLocals cType1
                           let cPPName = mkName ["C"]
                           cName <- mkFreshName
                           let c = mkLocalData cName cPPName cType2 BinderDefault
                           addIndElimInfo .= Just $ ElimInfo c indexLocals majorPremise []


    initMinorPremises :: AddInductiveMethod()
    initMinorPremises =
        do
          (IndDecl _ _ indName indType introRules) <- use addIndIDecl
          env <- use addIndEnv
          indLevel <- uses addIndIndLevel Maybe.fromJust
          -- Note: this is not the final K-Target check
          addIndKTarget .= envPropProofIrrel env && isZero indLevel && length introRules == 1
          mapM_ initMinorPremise introRules

    initMinorPremise :: IntroRule -> AddInductiveMethod ()
    initMinorPremise (IntroRule irName irType) =
        do
          paramLocals <- use addIndParamLocals
          indexLocals <- use addIndIndexLocals
          elimInfo <- use addIndElimInfo
          depElim <- use addIndDepElim
          indLevel <- use addIndIndLevel
          levels <- uses (addIndIDecl . indDeclLPNames) (map mkLevelParam)
          (nonrecArgs, recArgs) <- splitIntroRuleType irName irType
          c <- use (addIndElimInfo . elimInfoC)
          let minorPremiseType0 = mkAppSeq (Local c) indexLocals
          let minorPremiseType1 = if depElim
                                  then let introApp = mkAppSeq
                                                      (mkAppSeq
                                                       (mkAppSeq (mkConstant irName levels)
                                                                     (map Local paramLocals))
                                                       (map Local nonrecArgs))
                                                      (map Local recArgs) in
                                       mkApp minorPremiseType0 introApp
                                  else minorPremiseType0
          indArgs <- constructIndArgs recArgs [0..]
          minorPremiseName <- mkFreshName
          let minorPremiseType2 = abstractPiSeq nonrecArgs
                                  (abstractPiSeq recArgs
                                   (abstractPiSeq indArgs minorPremiseType1))
          let minorPremise = mkLocalData minorPremiseName (mkName ["e"]) minorPremiseType2
          addIndElimInfo . elimInfoMinorPremises %= (++ [minorPremise])

    splitIntroRuleType :: Name -> Expr -> AddInductiveMethod ([LocalData], [LocalData])
    splitIntroRuleType irName irType = splitIntroRuleTypeCore [] [] irName irType 0

    splitIntroRuleTypeCore :: [LocalData] -> [LocalData] -> Name -> Expr -> AddInductiveMethod ([LocalData], [LocalData])
    splitIntroRuleTypeCore nonRecArgs recArgs irName irType paramNum =
        do
          numParams <- use (addIndIDecl . indDeclNumParams)
          paramLocal <- uses addIndParamLocals (!! paramNum)
          case irType of
            Pi pi | paramNum < numParams -> splitIntroRuleTypeCore nonRecArgs recArgs irName (instantiate (bindingBody pi) (Local paramLocal)) (paramNum+1)
                  | otherwise ->
                      do
                        -- intro rule has an argument, so we set KTarget to False
                        addIndKTarget .= False
                        local <- mkLocalFor pi
                        argIsRec <- isRecArg (bindingDomain pi)
                        let (newNonRecArgs, newRecArgs) = if argIsRec then (nonRecArgs, recArgs ++ [local]) else (nonRecArgs ++ [local], recArgs)
                        splitIntroRuleTypeCore newNonRecArgs newRecArgs irName (instantiate (bindingBody pi) (Local local)) (paramNum+1)
            _ -> return (nonRecArgs, recArgs)

    constructIndArgs :: [LocalData] -> [Int] -> AddInductiveMethod [LocalData]
    constructIndArgs [] _ = return []
    constructIndArgs (recArg : recArgs) (recArgNum : recArgNums) =
        do
          restIndArgs <- constructIndArgs recArgs recArgNums
          recArgType <- whnf . localType recArg
          (xs, recArgTypeBody) <- constructIndArgArgs recArgType
          recArgTypeBody <- whnf recArgTypeBody
          c <- uses addIndElimInfo (view elimInfoC . Maybe.fromJust)
          indexLocals <- use addIndIndexLocals
          let cApp0 = mkAppSeq (Local c) indexLocals
          depElim <- use addIndDepElim
          let cApp1 = if depElim
                      then mkApp cApp0 (mkAppSeq (Local recArg) (map Local xs))
                      else cApp0
          let indArgType = abstractPiSeq xs cApp1
          indArgName <- mkFreshName
          let indArg = mkLocalData indArgName (nameRConsI (mkName ["v"]) recArgNum) indArgType
          return $ indArg : restIndArgs

    constructIndArgArgs :: Expr -> AddInductiveMethod ([LocalData], Expr)
    constructIndArgArgs recArgType = constructIndArgArgsCore [] recArgType

    constructIndArgArgsCore :: [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
    constructIndArgArgsCore xs recArgType =
        case recArgType of
          Pi pi -> do local <- mkLocalFor pi
                      constructIndArgArgsCore (xs ++ [local]) (instantiate (bindingBody pi) (Local local))
          _ -> return (xs, recArgType)


{-
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

certify_declaration :: Name -> [Name] -> Expr -> AddInductiveMethod CertifiedDeclaration
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
