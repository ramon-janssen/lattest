{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  FuncDef
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Function Definition
-----------------------------------------------------------------------------
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DeriveAnyClass #-}
module Lattest.Model.Symbolic.ValExpr.FuncDef
where

import GHC.Generics (Generic)
import Control.DeepSeq

import Lattest.Model.Symbolic.ValExpr.Id (Resettable)

import Lattest.Model.Symbolic.ValExpr.ValExprDefs

-- | Data structure to store the information of a Function Definition:
-- * A list of variables
-- * A body (possibly using the variables)
data  FuncDef v i    = FuncDef    [v] (ValExpr i)
     deriving (Eq,Ord,Show)

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
