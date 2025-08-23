{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}


-- ----------------------------------------------------------------------------------------- --

module Lattest.SMT.ParamCore

-- ----------------------------------------------------------------------------------------- --
-- 
-- TorXakis Core Parameters
-- 
-- ----------------------------------------------------------------------------------------- --
-- export

( Params                 -- Params = Map.Map String (String,String->Bool)
--, ImpRel (..)
--, InputCompletion (..)
, initParams             -- initParams :: Map.Map String (String,String->Bool)
                         -- initial values of parameters
)

where

import qualified Data.Char as Char
import qualified Data.Map  as Map


----------------------------------------------------------------------------------------- --
-- Params

type  Params  =  Map.Map String (String,String->Bool)


-- ----------------------------------------------------------------------------------------- --
-- types of parameters


-- Represent String a positive integer within the given range?
-- lower and upper bound are inclusive.
withinRangeInt :: Int -> Int -> String -> Bool
withinRangeInt low high s = not (null s) && all Char.isDigit s && (let v = read s :: Int in ( low <= v ) && ( v <= high) )
      

-- ----------------------------------------------------------------------------------------- --
-- parameter initialization

initParams :: Params
initParams  =  Map.fromList $ map ( \(x,y,z) -> (x,(y,z)) )

-- ----------------------------------------------------------------------------------------- --
  [
-- no params at the moment
  ]

-- ----------------------------------------------------------------------------------------- --
--                                                                                           --
-- ----------------------------------------------------------------------------------------- --
