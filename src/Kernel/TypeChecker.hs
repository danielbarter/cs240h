{-|
Module      : Kernel.TypeChecker
Description : Type checker
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for type checker
-}
module Kernel.TypeChecker (
  IndDecl(IndDecl), Env
  , envAddIndDecl, envAddIntroRule, envAddElimInfo, envAddCompRule
  , envLookupDecl, envAddDecl
  , TypeError, TCMethod
  , tcEval, tcRun
  , check, whnf, isDefEq
  ) where
import Kernel.TypeChecker.Internal
