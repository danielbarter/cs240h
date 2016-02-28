{-|
Module      : Kernel.InductiveInfo
Description : Information about inductive datatypes
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Information about inductive datatypes
-}
{-# LANGUAGE TemplateHaskell #-}
module Kernel.InductiveExt where

import Kernel.Name
import Kernel.Level
import Kernel.Expr

import Lens.Simple

import qualified Data.Map as Map
import Data.Map (Map)

data IntroRule = IntroRule Name Expr deriving (Show)

data InductiveDecl = InductiveDecl {
  indDeclLevelParamNames :: [Name],
  indDeclNumParams :: Integer,
  indDeclName :: Name,
  indDeclType :: Expr,
  indDeclIntroRules :: [IntroRule]
  } deriving (Show)

data ElimInfo = ElimInfo {
  elimInfoName :: Name, -- ^ name of the inductive datatype associated with eliminator
  elimInfoLevelParamNames :: [Name], -- ^ level parameter names used in computational rule
  elimInfoNumParams :: Int, -- ^ number of global parameters A
  elimInfoNumACe :: Int, -- ^ sum of number of global parameters A, type formers C, and minor preimises e.
  elimInfoNumIndices :: Int, -- ^ number of inductive datatype indices
  -- | We support K-like reduction when the inductive datatype is in Type.{0} (aka Prop), proof irrelevance is enabled,
  -- it has only one introduction rule, the introduction rule has "0 arguments".
  elimInfoKTarget :: Bool,
  elimInfoDepElim :: Bool -- ^ eei_dep_elim == true if dependent elimination is used for this eliminator
  } deriving (Show)

-- | Represents a single computation rule
data CompRule = CompRule {
  compRuleElimName :: Name, -- ^ name of the corresponding eliminator
  compRuleNumArgs :: Int, -- ^ sum of number of rec_args and nonrec_args in the corresponding introduction rule.
  compRuleRHS :: Expr -- ^ computational rule RHS: Fun (A, C, e, b, u), (e_k_i b u v)
  } deriving (Show)

data InductiveExt = InductiveExt {
  _indExtElimInfos :: Map Name ElimInfo,
  _indExtCompRules :: Map Name CompRule,
  _indExtIntroNameToIndName :: Map Name Name,
  _indExtIndDecls :: Map Name InductiveDecl
  } deriving (Show)

makeLenses ''InductiveExt

mkEmptyInductiveExt = InductiveExt Map.empty Map.empty Map.empty Map.empty
