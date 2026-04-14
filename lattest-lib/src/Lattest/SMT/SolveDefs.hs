{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent SMT folder.
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

import Lattest.Model.Symbolic.Expr(Constant)

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
