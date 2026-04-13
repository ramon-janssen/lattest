{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Expr
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
--
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Interface file for Value Expressions.
-----------------------------------------------------------------------------
module Lattest.Model.Symbolic.Expr
( Expr
, view
, ExprView(..)
, Type(..)
, varName
, varType
, Constant(..)
, constType
, ConstType
, fromConst
, toConst
, Variable(..)
, VarModel
, Assignable
, assign
, assignValues
, eval
, subst
, substConst
, Valuation
, assignedExpr
, (=:)
, freeVars
, module Lattest.Model.Symbolic.Internal.ExprImpls
, module Lattest.Model.Symbolic.Internal.ExprImplsExtension
)
where

import           Lattest.Model.Symbolic.Internal.ExprDefs
import           Lattest.Model.Symbolic.Internal.ExprImpls
import           Lattest.Model.Symbolic.Internal.ExprImplsExtension
