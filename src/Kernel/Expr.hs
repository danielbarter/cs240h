{-|
Module      : Expr
Description : Expressions
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for expressions
-}
module Kernel.Expr (
  Expr(..)
  , LocalData, VarData, SortData, ConstantData, BindingData, AppData
  , mkVar, mkLocal, mkLocalDefault, mkLocalData, mkConstant, mkSort
  , mkLambda, mkLambdaDefault, mkPi, mkPiDefault
  , mkApp, mkAppSeq
  , varIdx
  , sortLevel
  , localName, localType
  , constName, constLevels
  , bindingName, bindingDomain, bindingBody, bindingInfo
  , appFn, appArg, getOperator, getAppArgs, getAppOpArgs
  , exprHasLocal, exprHasLevelParam, hasFreeVars, closed
  , abstractPi, abstractPiSeq, abstractLambda, abstractLambdaSeq
  , instantiate, instantiateSeq, instantiateLevelParams
  , isConstant, maybeConstant
  , innerBodyOfLambda
   -- TODO(dhs): need to expose more!
  , mkProp
  ) where
import Kernel.Expr.Internal
