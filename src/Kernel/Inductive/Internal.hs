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
                          , CompRule(CompRule)
                          , Env
                          , envAddIndDecl, envAddIntroRule, envAddElimInfo, envAddCompRule, envLookupDecl
                          , envPropProofIrrel, envPropImpredicative
                          , envAddAxiom
                          , TypeError, TCMethod)

import qualified Kernel.TypeChecker as TypeChecker

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Lens.Simple (makeLenses, use, uses, view, over, (%=), (.=), (%%=))

import Data.List (genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)
import qualified Data.Maybe as Maybe

import Debug.Trace

data IndDeclError = NumParamsMismatchInIndDecl Int Int
                        | ArgDoesNotMatchInductiveParameters Int Name
                        | UniLevelOfArgTooBig Int Name Level Level
                        | NonRecArgAfterRecArg Int Name
                        | InvalidRecArg Int Name
                        | InvalidReturnType Name
                        | NonPosOccurrence Int Name
                        | NonValidOccurrence Int Name
                        | TypeCheckError TypeChecker.TypeError String
                        deriving (Eq,Show)

data ElimInfo = ElimInfo {
  elimInfoC :: LocalData, -- type former constant
  elimInfoIndices :: [LocalData], --local constant for each index
  elimInfoMajorPremise :: LocalData, -- major premise for each inductive decl
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

gensym :: AddInductiveMethod Integer
gensym = addIndNextId %%= \n -> (n, n + 1)

mkLocalFor :: BindingData -> AddInductiveMethod LocalData
mkLocalFor bind = do
  nextId <- gensym
  return $ mkLocalData (mkSystemNameI nextId) (bindingName bind) (bindingDomain bind) (bindingInfo bind)

indAssert :: IndDeclError -> Bool -> AddInductiveMethod ()
indAssert err b = if b then return () else throwE err

-- TODO(dhs): why did old version add another layer to this?
mkFreshName :: AddInductiveMethod Name
mkFreshName = gensym >>= return . mkSystemNameI

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
  computeElimRule
  declareElimRule
  mkCompRules

checkIndType :: AddInductiveMethod ()
checkIndType = do
  (IndDecl numParams lpNames name ty introRules) <- asks _addIndIDecl
  checkType ty lpNames
  let (paramLocals, rest) = telescopePiN numParams ty
  indAssert (length paramLocals == numParams) $ NumParamsMismatchInIndDecl (length paramLocals) numParams
  let (indexLocals, body) = telescopePi rest
  sort <- ensureSort body lpNames
  lpNames <- map mkLevelParam . indDeclLPNames <$> asks addIndIDecl
  addIndIsDefinitelyNotZero .= isDefinitelyNotZero (sortLevel sort)
  addIndIndConst .= Just (ConstantData name lpNames)
  addIndIndLevel .= Just (sortLevel sort)
  addIndNumArgs .= Just (length indexLocals)
  addIndParamLocals .= Just paramLocals
  addIndIndexLocals .= Just indexLocals
  addIndIndBody .= Just body
      where
        telescopePiN :: Int -> Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePiN numTake e = telescopePiNCore numTake [] e

        telescopePiNCore :: Int -> [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePiNCore numTake locals e =
          case e of
            _ | numTake <= 0 -> return (locals, e)
            Pi pi -> do local <- mkLocalFor pi
                        telescopePiNCore (numTake - 1) (locals ++ [local]) (instantiate (bindingBody pi) (Local local))
            _ -> return (locals, e)

        telescopePi :: Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePi e = telescopePiCore [] e

        telescopePiCore :: [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePiCore locals e =
            case e of
              Pi pi -> do local <- mkLocalFor pi
                          telescopePiCore (locals ++ [local]) (instantiate (bindingBody pi) (Local local))
              _ -> return (locals, e)


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
           lpNames <- use (addIndIDecl . indDeclLPNames)
           paramLocals <- liftM Maybe.fromJust $ use addIndParamLocals
           if paramNum < numParams
             then do let local = paramLocals !! paramNum
                     isDefEq (bindingDomain pi) (localType local) >>=
                       indAssert (ArgDoesNotMatchInductiveParameters paramNum name)
                     checkIntroRuleCore (paramNum+1) foundRec name (instantiate (bindingBody pi) (Local local))
             else do sort <- ensureType (bindingDomain pi) lpNames
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

computeElimRule :: AddInductiveMethod ()
computeElimRule = do
  initDepElim
  initElimLevel
  initElimInfo
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
    collectArgsToCheck :: Expr -> Int -> AddInductiveMethod (Expr, [LocalData])
    collectArgsToCheck ty paramNum =
      case ty of
        Pi pi -> do local <- mkLocalFor pi
                    let body = instantiate (bindingBody pi) (Local local)
                    (ty, rest) <- collectArgsToCheck body (paramNum+1)
                    numParams <- use (addIndIDecl . indDeclNumParams)
                    lpNames <- use (addIndIDecl . indDeclLPNames)
                    if paramNum >= numParams
                    then do sort <- ensureType (bindingDomain pi) lpNames
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
          (nonrecArgs, recArgs) <- splitIntroRuleType irType
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
splitIntroRuleType irType = splitIntroRuleTypeCore [] [] irType 0
    where
      splitIntroRuleTypeCore :: [LocalData] -> [LocalData] -> Expr -> AddInductiveMethod ([LocalData], [LocalData])
      splitIntroRuleTypeCore nonRecArgs recArgs irType paramNum =
          do
            numParams <- use (addIndIDecl . indDeclNumParams)
            paramLocal <- uses addIndParamLocals (!! paramNum)
            case irType of
              Pi pi | paramNum < numParams -> splitIntroRuleTypeCore nonRecArgs recArgs (instantiate (bindingBody pi) (Local paramLocal)) (paramNum+1)
                    | otherwise ->
                        do
                          -- intro rule has an argument, so we set KTarget to False
                          addIndKTarget .= False
                          local <- mkLocalFor pi
                          argIsRec <- isRecArg (bindingDomain pi)
                          let (newNonRecArgs, newRecArgs) = if argIsRec then (nonRecArgs, recArgs ++ [local]) else (nonRecArgs ++ [local], recArgs)
                          splitIntroRuleTypeCore newNonRecArgs newRecArgs (instantiate (bindingBody pi) (Local local)) (paramNum+1)
              _ -> return (nonRecArgs, recArgs)

constructIndArgs :: [LocalData] -> [Int] -> AddInductiveMethod [LocalData]
constructIndArgs [] _ = return []
constructIndArgs (recArg : recArgs) (recArgNum : recArgNums) =
    do
      restIndArgs <- constructIndArgs recArgs recArgNums
      recArgType <- whnf . localType recArg
      xs <- constructIndArgArgs recArgType
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

constructIndArgArgs :: Expr -> AddInductiveMethod [LocalData]
constructIndArgArgs recArgType = constructIndArgArgsCore [] recArgType
    where
      constructIndArgArgsCore :: [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
      constructIndArgArgsCore xs recArgType =
          case recArgType of
            Pi pi -> do local <- mkLocalFor pi
                        constructIndArgArgsCore (xs ++ [local]) (instantiate (bindingBody pi) (Local local))
            _ -> return xs

declareElimRule :: AddInductiveMethod ()
declareElimRule =
  do
    (IndDecl numParams lpNames indName indType introRules) <- use addIndIDecl
    elimInfo <- uses addIndElimInfo Maybe.fromJust
    let (c, majorPremise, minorPremises) = (elimInfoC, elimInfoMajorPremise, elimInfoMinorPremises) <$> elimInfo
    paramLocals <- use addIndParamLocals
    indexLocals <- use addIndIndexLocals
    depElim <- use addIndDepElim
    elimLPNames <- getElimLPNames
    let elimType0 = mkAppSeq (Local c) (map Local indexLocals)
    let elimType1 = if depElim then mkApp elimType0 (Local majorPremise) else elimType0
    let elimType2 = abstractPi majorPremise elimType1
    let elimType3 = abstractPiSeq indexLocals elimType2
    let elimType4 = foldr abstractPi elimType3 minorPremises
    let elimType5 = abstractPi c elimType4
    let elimType6 = abstractPiSeq paramLocals elimType5
    addIndEnv %= envAddElimInfo elimInfo
    addIndEnv %= envAddAxiom (getElimName indName)  elimLPNames elimType6

getElimName :: Name -> Name
getElimName indName = nameRConsS indName "rec"

getElimLPNames :: AddInductiveMethod [Name]
getElimLPNames = do
  lpNames <- use (addIndIDecl . indDeclLPNames)
  elimLevel <- use addIndElimLevel
  case maybeParamName elimLevel of
   Just n -> return $ n : lpNames
   Nothing -> return lpNames

mkCompRules :: AddInductiveMethod ()
mkCompRules = do
  (IndDecl _ _ indName _ introRules) <- use addIndIDecl
  (ElimInfo _ _ _ minorPremises) <- use addIndElimInfo
  mapM_ (uncurry $ mkCompRule indName) (zip introRules minorPremises)

mkCompRule :: Name -> IntroRule -> LocalData -> AddInductiveMethod ()
mkCompRule indName (IntroRule irName irType) minorPremise = do
  elimInfo <- uses addIndElimInfo Maybe.fromJust
  let (elimName, c, majorPremise, minorPremises) = (elimInfoC, elimInfoMajorPremise, elimInfoMinorPremises) <$> elimInfo
  paramLocals <- use addIndParamLocals
  elimLPNames <- getElimLPNames
  (nonRecArgs, recArgs) <- splitIntroRuleType irType
  recApps <- constructRecApps recArgs
  let compRHS0 = mkAppSeq (mkAppSeq (mkAppSeq (Local minorPremise)
                                     (map Local nonRecArgs))
                           (map Local recArgs)) recArgs
  let compRHS1 = abstractLambdaSeq paramLocals
                 (abstractLambdaSeq c
                  (abstractLambdaSeq minorPremises
                   (abstractLambdaSeq nonRecArgs
                    (abstractLambdaSeq recArgs compRHS1))))
  checkType compRHS1 elimLPNames
  envAddCompRule irName (CompRule (getElimName indName) (length nonRecArgs + length recArgs) compRHS1)
    where
      constructRecApps :: [LocalData] -> AddInductiveMethod [Expr]
      constructRecApps [] = return []
      constructRecApps (recArg:recArgs) = do
        elimInfo <- uses addIndElimInfo Maybe.fromJust
        let (elimName, c, majorPremise, minorPremises) = (elimInfoC, elimInfoMajorPremise, elimInfoMinorPremises) <$> elimInfo
        paramLocals <- uses addIndParamLocals Maybe.fromJust
        indexLocals <- use addIndIndexLocals
        restApps <- constructRecApps recArgs
        recArgType <- whnf . localType $ recArg
        xs <- constructIndArgArgs recArgType
        let elimName = getElimName indName
        elimLPNames <- map mkLevelParam <$> getElimLPNames
        let recApp0 = mkConstant elimName elimLPNames
        let recApp1 = mkApp (mkAppSeq (mkAppSeq (mkApp (mkAppSeq recApp0 (map Local paramLocals))
                                                           (Local c))
                                       (map Local minorPremises))
                             indexLocals)
                      (mkAppSeq (Local recArg) (map Local xs))
        let recApp2 = abstractLambdaSeq xs recApp1
        return recApp2 : restApps

{- Wrappers for the type checker -}

wrapTC :: Expr -> [Name] -> (Expr -> TCMethod a) -> String -> AddInductiveMethod a
wrapTC e lpNames tcFn msg = do
  env <- use addIndEnv
  nextId <- use addIndNextId
  case TypeChecker.tcEval env lpNames nextId (tcFn e) of
    Left tcErr -> throwE $ TypeCheckError tcErr msg
    Right (val, next) -> addIndNextId .= next >> return val

checkType :: Expr -> [Name] -> AddInductiveMethod Expr
checkType e lpNames = wrapTC e lpNames TypeChecker.inferType "inferType"

ensureSort :: Expr -> [Name] -> AddInductiveMethod SortData
ensureSort e lpNames = wrapTC e lpNames TypeChecker.ensureSort "ensureSort"

ensureType :: Expr -> [Name] -> AddInductiveMethod SortData
ensureType e lpNames = wrapTC e lpNames TypeChecker.ensureType "ensureType"

whnf :: Expr -> AddInductiveMethod Expr
whnf e = wrapTC e [] TypeChecker.whnf "whnf"

isDefEq :: Expr -> Expr -> [Name] -> AddInductiveMethod Bool
isDefEq e1 e2 lpNames = do
  env <- use addIndEnv
  nextId <- use addIndNextId
  case TypeChecker.tcEval env lpNames nextId (TypeChecker.isDefEq e1 e2) of
    Left tcErr -> throwE $ TypeCheckError tcErr "isDefEq"
    Right (b, next) -> addIndNextId .= next >> return b

{-
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
-}
