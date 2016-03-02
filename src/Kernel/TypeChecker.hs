{-|
Module      : Kernel.TypeChecker
Description : Type checker
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for type checker
-}
module Kernel.TypeChecker (
  IndDecl(IndDecl), indDeclNumParams, indDeclLPNames, indDeclName, indDeclType, indDeclIntroRules
  , IntroRule(IntroRule)
  , CompRule(CompRule)
  , Env
  , envAddIndDecl, envAddIntroRule, envAddElimInfo, envAddCompRule
  , envLookupDecl
  , envAddAxiom, envAddDefinition
  , envPropProofIrrel, envPropImpredicative
  , TypeError, TCMethod
  , ensureSort, ensureType
  , tcEval, tcRun
  , check, whnf, isDefEq, inferType
  ) where
import Kernel.TypeChecker.Internal
