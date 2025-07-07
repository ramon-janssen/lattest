{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}

module Lattest.Model.Symbolic.ValExpr.Variable

where

import           Lattest.Model.Symbolic.ValExpr.Name
import           Lattest.Model.Symbolic.ValExpr.SortId

class (Eq v, Ord v, Read v, Show v) => Variable v where
  vname  :: v -> Name
  vunid  :: v -> Int
  vsort  :: v -> SortId
  cstrVariable  :: String -> Int -> SortId -> v
