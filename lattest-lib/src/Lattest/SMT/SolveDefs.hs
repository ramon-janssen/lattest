{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}


-- ----------------------------------------------------------------------------------------- --
--
--   Module SolveDefs :  Some Definitions for Solving
--
-- ----------------------------------------------------------------------------------------- --


{-# LANGUAGE FlexibleInstances #-}
module Lattest.SMT.SolveDefs
( Solution
, SolvableProblem(..)
, SolveProblem(..)
)

where

import qualified Data.Map  as Map

import Lattest.Model.Symbolic.ValExpr.Constant

-- ----------------------------------------------------------------------------------------- --
-- SMT definitions


type  Solution v       =  Map.Map v Constant

data  SolvableProblem  = Sat
                       | Unsat
                       | Unknown
     deriving (Eq,Ord,Read,Show)

data  SolveProblem v  = Solved (Solution v)
                      | Unsolvable
                      | UnableToSolve
     deriving (Eq,Ord,Read,Show)

-- ----------------------------------------------------------------------------------------- --
--                                                                                           --
-- ----------------------------------------------------------------------------------------- --
