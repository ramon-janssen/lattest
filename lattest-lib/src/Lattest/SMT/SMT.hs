{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}

-- ----------------------------------------------------------------------------------------- --
module Lattest.SMT.SMT
-- ----------------------------------------------------------------------------------------- --
--
-- SMT: open a connection to SMT, send constraints, and retrieve a model
--
-- ----------------------------------------------------------------------------------------- --
-- export

( createSMTEnv
, openSolver
, close
--, addDefinitions
--, addDeclarations
, addAssertions
, getSolvable
, getSolution
, push
, pop
, put
, putT
, valExprToString
, SMTRef
, createSMTRef
, newSMTRef
, runSMT
, readSMTRef
, Solution
, SolvableProblem(..)
, SMT
)

-- ----------------------------------------------------------------------------------------- --
-- import

where

import           Lattest.SMT.SMTInternal
import           Lattest.SMT.SMTData
import           Lattest.SMT.SolveDefs