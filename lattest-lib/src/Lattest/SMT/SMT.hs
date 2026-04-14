{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent SMT folder.
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
, addDeclarations
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