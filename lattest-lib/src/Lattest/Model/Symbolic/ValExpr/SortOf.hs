{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}

-- | SortOf for Value Expressions
module Lattest.Model.Symbolic.ValExpr.SortOf
( SortOf(..)
)
where

import           Lattest.Model.Symbolic.ValExpr.SortId

-- | Sort of a value expression
class SortOf s where
  sortOf :: s -> SortId
