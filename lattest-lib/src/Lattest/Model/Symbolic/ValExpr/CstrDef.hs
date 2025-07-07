{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  CstrDef
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Data structure for constructors
-----------------------------------------------------------------------------
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE DeriveAnyClass #-}
module Lattest.Model.Symbolic.ValExpr.CstrDef
where

import GHC.Generics (Generic)
import Control.DeepSeq

import Lattest.Model.Symbolic.ValExpr.FuncId
import Lattest.Model.Symbolic.ValExpr.Id (Resettable)

-- | A constructor has a `isCstr` functions, and a list of accessors functions.
data  CstrDef       = CstrDef    FuncId [FuncId]       -- constructor_check [field_selectors]
     deriving (Eq,Ord,Read,Show, Generic, NFData)

instance Resettable CstrDef

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
