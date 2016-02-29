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
  , mkVar, mkLocal, mkLocalDefault, mkConstant, mkSort
  , mkLambda, mkLambdaDefault, mkPi, mkPiDefault
  , mkApp, mkAppSeq
  , varIdx
  , sortLevel
  , localName, localType
  , constName, constLevels
  , bindingDomain, bindingBody
  , appFn, appArg, getOperator, getAppArgs, getAppOpArgs
  , exprHasLocal, exprHasLevelParam
   -- TODO(dhs): need to expose more!
    ) where
import Kernel.Expr.Internal
