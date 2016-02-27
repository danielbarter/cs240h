{-|
Module      : Expr
Description : Expressions
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for expressions
-}
module Kernel.Expr (
  Expr
  , get_operator, get_app_args, get_app_op_args
  , mk_var, mk_local, mk_local_default, mk_constant, mk_sort
  , mk_lambda, mk_lambda_default, mk_pi, mk_pi_default
  , mk_app, mk_app_seq
   -- TODO(dhs): need to expose more!
    ) where
import Kernel.Expr.Internal
