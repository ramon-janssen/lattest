{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}
-- ----------------------------------------------------------------------------------------- --

module Lattest.Model.Symbolic.ValExpr.VarId

where

import           Control.DeepSeq
import           Data.Data
import qualified Data.Text       as T
import           GHC.Generics    (Generic)
import           Lattest.Model.Symbolic.ValExpr.Id

-- Local imports.
import           Lattest.Model.Symbolic.ValExpr.Name
import           Lattest.Model.Symbolic.ValExpr.SortId
import           Lattest.Model.Symbolic.ValExpr.SortOf
import           Lattest.Model.Symbolic.ValExpr.Variable


data VarId = VarId
    { name    :: Name             --smallid
    , unid    :: Id
    , varsort :: SortId
    } deriving (Eq, Ord, Read, Show, Generic, NFData, Data)

instance Variable VarId where
  vname v            = Lattest.Model.Symbolic.ValExpr.VarId.name v <> "$$" <> (T.pack . show) (Lattest.Model.Symbolic.ValExpr.VarId.unid v)
  vunid              = _id . Lattest.Model.Symbolic.ValExpr.VarId.unid
  vsort              = Lattest.Model.Symbolic.ValExpr.VarId.varsort
  cstrVariable n i   = VarId (T.pack n) (Id i)

instance Resettable VarId
instance Identifiable VarId

instance SortOf VarId  where
  sortOf (VarId _nm _unid srt)                    = srt
