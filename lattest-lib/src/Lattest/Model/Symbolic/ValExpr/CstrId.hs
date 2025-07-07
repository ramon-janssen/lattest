{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  CstrId
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Data structure for identifiers for constructors
-----------------------------------------------------------------------------
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
module Lattest.Model.Symbolic.ValExpr.CstrId

where

import           Control.DeepSeq
import           Data.Data
import           GHC.Generics    (Generic)

import           Lattest.Model.Symbolic.ValExpr.Id
import           Lattest.Model.Symbolic.ValExpr.Name
import           Lattest.Model.Symbolic.ValExpr.SortId

-- | Identifier for Constructor
data CstrId = CstrId
    { name     :: Name            -- capid
    , unid     :: Id
    , cstrargs :: [SortId]
    , cstrsort :: SortId
    } deriving (Eq, Ord, Read, Show, Generic, NFData, Data)

-- | CstrId is Resettable
instance Resettable CstrId
-- | CstrId is Identifiable
instance Identifiable CstrId
