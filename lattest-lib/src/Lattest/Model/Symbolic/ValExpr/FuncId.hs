{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}

-- ----------------------------------------------------------------------------------------- --
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
module Lattest.Model.Symbolic.ValExpr.FuncId

where

import           Control.DeepSeq
import           Data.Data
import           GHC.Generics    (Generic)

import           Lattest.Model.Symbolic.ValExpr.Id
import           Lattest.Model.Symbolic.ValExpr.Name
import           Lattest.Model.Symbolic.ValExpr.SortId

data FuncId = FuncId
    { name     :: Name            -- smallid
    , unid     :: Id
    , funcargs :: [SortId]
    , funcsort :: SortId
    } deriving (Eq, Ord, Read, Show, Generic, NFData, Data)

instance Resettable FuncId
instance Identifiable FuncId
