{-|
Module      : Kernel.TypeChecker.Internal
Description : Type checker
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of type checker
-}
{-# TupleSections #-}
module Kernel.TypeChecker.Internal where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

import Data.List (nub,find,genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Maybe as Maybe

import Debug.Trace

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Level (Level)
import Kernel.Expr
import Kernel.Env
import Kernel.DefEqCache

{- TCMethods -}

data TypeError = UndefGlobalUniv Name
               | UndefLevelParam Name
               | TypeExpected Expr
               | FunctionExpected Expr
               | TypeMismatchAtApp Expr Expr
               | TypeMismatchAtDef Expr Expr
               | DeclHasFreeVars Expr
               | DeclHasLocals Expr
               | NameAlreadyDeclared Decl
               | DuplicateLevelParamName
               | ConstNotFound Name
               | ConstHasWrongNumLevels Name [Name] [Level]
               deriving (Eq,Show)

data TypeCheckerR = TypeCheckerR {
  tcrEnv :: Env ,
  tcrLPNames :: [Name]
}

data TypeCheckerS = TypeCheckerS {
  tcsNextId :: Integer ,
  tcsDefEqCache :: DefEqCache,
  tcsInferTypeCache :: Map Expr Expr
  }

mkTypeCheckerR :: Env -> [Name] -> TypeCheckerR
mkTypeCheckerR env levelParamNames  = TypeCheckerR env levelParamNames

mkTypeCheckerS :: Integer -> TypeCheckerS
mkTypeCheckerS nextId = TypeCheckerS nextId mkDefEqCache Map.empty

type TCMethod = ExceptT TypeError (StateT TypeCheckerS (Reader TypeCheckerR))

tcEval :: Env -> [Name] -> Integer -> TCMethod a -> Either TypeError (a, Integer)
tcEval env lpNames nextId tcFn =
  let (x, tc) = runReader (runStateT (runExceptT tcFn) (mkTypeCheckerS nextId)) (mkTypeCheckerR env lpNames) in
  (,tcsNextId tc) <$> x

tcRun :: Env -> [Name] -> Integer -> TCMethod a -> Either TypeError a
tcRun env lpNames nextId = fmap fst . (tcEval env lpNames nextId)

check :: Env -> Decl -> Either TypeError ()
check env d = tcRun env (declLPNames d) 0 (checkMain d)

checkMain :: Decl -> TCMethod ()
checkMain d = do
  checkNoLocal (declType d)
  maybe (return ()) checkNoLocal (declVal d)
  checkName (declName d)
  checkDuplicatedParams
  sort <- inferType (declType d)
  ensureSort sort
  maybe (return ()) (checkValMatchesType (declType d)) (declVal d)

tcAssert :: Bool -> TypeError -> TCMethod ()
tcAssert b err = if b then return () else throwE err

{- Checkers -}

checkNoLocal :: Expr -> TCMethod ()
checkNoLocal e = tcAssert (not $ exprHasLocal e) (DeclHasLocals e)

checkName :: Name -> TCMethod()
checkName name = do
  env <- asks tcrEnv
  maybe (return ()) (throwE . NameAlreadyDeclared) (envLookupDecl env name)

checkDuplicatedParams :: TCMethod ()
checkDuplicatedParams = do
  lpNames <- asks tcrLPNames
  tcAssert (lpNames == nub lpNames) DuplicateLevelParamName

checkValMatchesType :: Expr -> Expr -> TCMethod()
checkValMatchesType ty val = do
  valTy <- inferType val
  isDefEq valTy ty >>= flip tcAssert (TypeMismatchAtDef valTy ty)

checkClosed :: Expr -> TCMethod ()
checkClosed e = tcAssert (not $ hasFreeVars e) (DeclHasFreeVars e)

checkLevel :: Level -> TCMethod ()
checkLevel level = do
  tcr <- ask
  maybe (return ()) (throwE . UndefLevelParam) (Level.getUndefParam level (tcrLPNames tcr))
  maybe (return ()) (throwE . UndefGlobalUniv) (Level.getUndefGlobal level (envGlobalNames $ tcrEnv tcr))

ensureSort :: Expr -> TCMethod SortData
ensureSort e = case e of
  Sort sort -> return sort
  _ -> do
    eWhnf <- whnf e
    case eWhnf of
      Sort sort -> return sort
      _ -> throwE $ TypeExpected eWhnf

ensureType :: Expr -> TCMethod SortData
ensureType e = inferType e >>= ensureSort

ensurePi :: Expr -> TCMethod BindingData
ensurePi e = case e of
  Pi pi -> return pi
  _ -> do
    eWhnf <- whnf e
    case eWhnf of
      Pi pi -> return pi
      _ -> throwE $ FunctionExpected eWhnf

{- Infer type -}

inferType :: Expr -> TCMethod Expr
inferType e = do
  checkClosed e
  inferTypeCache <- gets tcsInferTypeCache
  case Map.lookup e inferTypeCache of
    Just ty -> return ty
    Nothing -> do
      ty <- case e of
        Local local -> return $ localType local
        Sort sort -> let level = sortLevel sort in checkLevel level >> (return . mkSort . Level.mkSucc) level
        Constant constant -> inferConstant constant
        Lambda lambda -> inferLambda lambda
        Pi pi -> inferPi pi
        App app -> inferApp app
      -- TODO(dhs): lenses
      inferTypeCache <- gets tcsInferTypeCache
      modify (\tc -> tc { tcsInferTypeCache = Map.insert e ty inferTypeCache })
      return ty

inferConstant :: ConstantData -> TCMethod Expr
inferConstant c = do
  env <- asks tcrEnv
  case envLookupDecl env (constName c) of
    Nothing -> throwE (ConstNotFound c)
    Just d -> do
      let (dLPNames, cLevels) = (declLPNames d, constLevels c)
      tcAssert (length dLPNames == length cLevels) $ ConstHasWrongNumLevels (constName c) dLPNames cLevels
      mapM_ checkLevel cLevels
      return $ instantiateLevelParams (declType d) dLPNames cLevels

mkLocalFor :: BindingData -> TCMethod LocalData
mkLocalFor bind = do
  nextId <- gensym
  return $ mkLocalData (mkSystemNameI nextId) (bindingName bind) (bindingDomain bind) (bindingInfo bind)

inferLambda :: BindingData -> TCMethod Expr
inferLambda lam = do
  domainTy <- inferType (bindingDomain lam)
  ensureSort domainTy
  local <- mkLocalFor lam
  bodyTy <- inferType (instantiate (bindingBody lam) (Local local))
  return $ abstractPi local bodyTy

inferPi :: BindingData -> TCMethod Expr
inferPi pi = do
  domainTy <- inferType (bindingDomain pi)
  domainTyAsSort <- ensureSort domainTy
  local <- mkLocalFor pi
  bodyTy <- inferType (instantiate (bindingBody pi) (Local local))
  bodyTyAsSort <- ensureSort bodyTy
  return $ mkSort (Level.mkIMax (sortLevel domainTyAsSort) (sortLevel bodyTyAsSort))

inferApp :: AppData -> TCMethod Expr
inferApp app = do
  fnTy <- inferType (appFn app)
  fnTyAsPi <- ensurePi fnTy
  argTy <- inferType (appArg app)
  isEq <- isDefEq (bindingDomain fnTyAsPi) argTy
  if isEq then return $ instantiate (bindingBody fnTyAsPi) (appArg app)
    else throwE $ TypeMismatchAtApp (bindingDomain fnTyAsPi) argTy
