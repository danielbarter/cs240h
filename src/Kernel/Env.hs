{-|
Module      : Kernel.Env
Description : Environments
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for environments
-}
module Kernel.Env (
  Decl
, declName, declLPNames, declType, declVal, declWeight
, Env
, envGlobalNames
, mkStdEnv
, isImpredicative, isPropProofIrrel
, mkDefinition, mkAxiom
, isDefinition
, envLookupDecl, envAddDecl
, envHasGlobalLevel, envAddGlobalLevel
, envAddInductiveDecl, envAddIntroRule, envAddElimInfo, envAddCompRule
) where
import Kernel.Env.Internal
