{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ValExpr
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
--
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Interface file for Value Expressions.
-----------------------------------------------------------------------------
module Lattest.Model.Symbolic.ValExpr.ValExpr
( ValExpr
, view
, eval
, ValExprView(..)
, PredefKind(..)
, Resettable
, module Lattest.Model.Symbolic.ValExpr.ValExprImpls
, module Lattest.Model.Symbolic.ValExpr.ValExprImplsExtension
)
where

import           Lattest.Model.Symbolic.ValExpr.Id
import           Lattest.Model.Symbolic.ValExpr.ValExprDefs
import           Lattest.Model.Symbolic.ValExpr.ValExprImpls
import           Lattest.Model.Symbolic.ValExpr.ValExprImplsExtension
