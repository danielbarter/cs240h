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

import Lens.Simple (makeLenses, over, view)

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Maybe as Maybe

data Decl = Decl {
  declName :: Name,
  declLPNames :: [Name],
  declType :: Expr,
  declVal :: Maybe Expr,
  declWeight :: Int
  } deriving (Eq,Show)

data Env = Env {
  _envDecls :: Map Name Decl,
  _envGlobalNames :: Set Name,
  _envIndExt :: InductiveExt,
  _envQuotEnabled :: Bool,
  _envPropProofIrrel :: Bool,
  _envPropImpredicative :: Bool
  } deriving (Show)

makeLenses ''Env

mkStdEnv = Env Map.empty Set.empty mkEmptyInductiveExt True True True

{- Decls -}

mkDefinition :: Env -> Name -> [Name] -> Expr -> Expr -> Decl
mkDefinition env name levelParamNames ty val =
  Decl name levelParamNames ty (Just val) (1 + getMaxDeclWeight env val)

mkAxiom :: Name -> [Name] -> Expr -> Decl
mkAxiom name levelParamNames ty = Decl name levelParamNames ty Nothing 0

isDefinition :: Decl -> Bool
isDefinition decl = Maybe.isJust $ declVal decl

getMaxDeclWeight :: Env -> Expr -> Int
getMaxDeclWeight env e = case e of
  Var _ -> 0
  Local local -> getMaxDeclWeight env (localType local)
  Constant const -> maybe 0 declWeight (envLookupDecl (constName const) env)
  Sort _ -> 0
  Lambda lam -> getMaxDeclWeight env (bindingDomain lam) `max` getMaxDeclWeight env (bindingBody lam)
  Pi pi -> getMaxDeclWeight env (bindingDomain pi) `max` getMaxDeclWeight env (bindingBody pi)
  App app -> getMaxDeclWeight env (appFn app) `max` getMaxDeclWeight env (appArg app)


envLookupDecl :: Name -> Env -> Maybe Decl
envLookupDecl name  = Map.lookup name . view envDecls

envAddDecl :: Decl -> Env -> Env
envAddDecl decl env = case envLookupDecl (declName decl) env of
                       Nothing -> over envDecls (Map.insert (declName decl) decl) env

envHasGlobalLevel :: Name -> Env -> Bool
envHasGlobalLevel name = Set.member name . view envGlobalNames

envAddGlobalLevel :: Name -> Env -> Env
envAddGlobalLevel name env = case envHasGlobalLevel name env of
                              False -> over envGlobalNames (Set.insert name) env

{- Inductive extension -}

envAddIndDecl :: IndDecl -> Env -> Env
envAddIndDecl idecl = over (envIndExt . indExtIndDecls) $ Map.insert (view indDeclName idecl) idecl

envAddIntroRule :: Name -> Name -> Env -> Env
envAddIntroRule irName indName = over (envIndExt . indExtIntroNameToIndName) $ Map.insert irName indName

envAddElimInfo :: ElimInfo -> Env -> Env
envAddElimInfo elimInfo = over (envIndExt . indExtElimInfos) $ Map.insert (elimInfoIndName elimInfo) elimInfo

envAddCompRule :: Name -> CompRule -> Env -> Env
envAddCompRule irName compRule = over (envIndExt . indExtCompRules) $ Map.insert irName compRule
