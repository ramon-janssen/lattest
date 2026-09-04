{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lattest.Util.STSJSONWriter (
    stsToJSON,
    stsToJSONFile,
    stsListToJSONFile,
) where

import qualified Data.Aeson as JSON
import Lattest.Model.Alphabet (IOAct (..), SymInteract (..), isInputGate, isOutputGate)

-- TODO: Do we want to export the STS with the check guards?

someVarName :: Some Variable -> String
someVarName (Some v) = varName v

-- | Assign every location a string id, TODO find a nice way to flatten them
assignLocationIds :: (Ord loc, Show loc) => Set.Set loc -> Map.Map loc String

gatesJSON :: Set.Set SymInteract (IOAct String String) -> (JSON.Value, JSON.Value)
gatesJSON alph = (JSON.toJSON inputGates, JSON.toJSON outputGates)
    where
    inputGates = [ gateName g | g <- Set.toList alph, isInputGate g ]
    outputGates = [ gateName g | g <- Set.toList alph, isOutputGate g ]

-- | The initial location(s): single id for atomic, or an array of ids when the initial
-- location is a conjunction.
initLocationJSON -- TODO: What to do if it is not atomic? Do we only allow conjunction?

-- | Turn a tuple of id, STS, initial valuation into a JSON.
stsToJSON :: (Ord loc, Show loc) => String -> IOSTS FreeLattice loc String String -> Valuation -> JSON.Value
stsToJSON sid sts valuation =
    object $
        [ "id" .= sid
        , "initial_location" .= initLocationJSON locIds (initConf sts)
        , "locationVariables" .= 
        , "parameters" .= 
        , "initialValuation" .= 
        , "locations" .= locIds
        , "inputGates" .= inputGatesJSON
        , "outputGates" .= outputGatesJSON
        , "guards" .= -- TODO do we also give guards identifiers?
        , "assignments" .= -- TODO do we also give assignments identifiers?
        , "switches" .=
        , "forbiddenTransitions" .=
        , "underspecifiedTransitions" .= 
        ]
    where
    locs = allLocations sts
    locIds = assignLocationIds locs
    alph = alphabet sts
    (inputGatesJSON, outputGatesJSON) = gatesJSON alph
    ws = buildSwitches locIds sts locs

-- | Write a single STS to a JSON file.
stsToJSONFile :: (Ord loc, Show loc) => FilePath -> String -> IOSTS FreeLattice loc String String -> Valuation -> IO ()
stsToJSONFile path sid sts valuation = BSL.writeFile path (JSON.encode (stsToJSON sid sts valuation))

-- | Write a list of STSs to a single file containing a JSON array.
stsListToJSONFile :: (Ord loc, Show loc) => FilePath -> [(String, IOSTS FreeLattice loc String String, Valuation)] -> IO ()
stsListToJSONFile path stss = BSL.writeFile path (JSON.encode [ stsToJSON sid sts valuation | (sid, sts, valuation) <- stss ])
