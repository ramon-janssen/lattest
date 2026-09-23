module Lib
    ( run
    ) where

import           Lattest.Model.Automaton
import           Lattest.Model.StandardAutomata
import           Lattest.Model.Symbolic.SolveSTS (offlineTests)
import           Lattest.Exec.StandardTestControllers
import           Lattest.Util.STSJSONParser (stsListFromJSONFile)
import Lattest.Exec.Testing (Verdict(..))
import Lattest.Model.BoundedMonad (BoundedConfiguration(..))
import qualified Data.Map as Map
import Lattest.Util.STSJSONWriter (stsListToJSONFile, stsToJSONFile)
import Data.Tuple (swap)

run :: IO ()
run = do
    putStrLn "loading STSs from JSON..."
    result <- stsListFromJSONFile "example.json"
    stss <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    putStrLn $ unlines $ map (\(_,sts,_,_,_) -> prettyPrint sts) stss
    -- Compose all parsed STSs
    let checked  = [ (sid, prependOutputChecks (\/) ("check_" ++) sts) | (sid, sts, _, _, _) <- stss ]
        conjmodel   = conjunctionAll checked
        seqComposed = conjmodel |>> conjmodel
        initVal  = case stss of
            [] -> error "no STSs loaded"
            (_, _, _, _, val):_ -> val    -- TODO: now each STS has its initial valuation, but this should be common as we are representing a single system
        model    = interpretSTS seqComposed initVal
        gs = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,g,_,_) -> g) stss
        as = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,_,a,_) -> a) stss

    putStrLn $ prettyPrintIntrp model

    putStrLn "computing offline test cases..."
    let nrSteps = 10
        randomSeed = 456
        observeVerdict (Just _) _ _ _ = error "shouldn't happen?"
        observeVerdict Nothing _ _ lattice
          | isForbidden lattice = pure $ Just Fail
          | isUnderspecified lattice = pure $ Just Pass
          | otherwise = pure Nothing
        controller = randomDataTestSelectorFromSeed randomSeed `untilCondition` stopAfterSteps nrSteps `observingOnly` observer Nothing observeVerdict pure
    tests <- offlineTests model controller
    print tests

    -- To write to a file:
    -- stsListToJSONFile "example_single_stss.json" (map (\(id,sts,_,_,val) -> (id,sts,val)) stss) gs as
    -- stsToJSONFile "example_composed.json" "stscomposed" seqComposed gs as initVal
