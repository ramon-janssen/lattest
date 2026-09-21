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

run :: IO ()
run = do
    putStrLn "loading STSs from JSON..."
    result <- stsListFromJSONFile "example.json"
    stss <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    putStrLn $ unlines $ map (\(_,sts,_) -> prettyPrint sts) stss
    -- Compose all parsed STSs
    let checked  = [ (sid, prependOutputChecks (\/) ("check_" ++) sts) | (sid, sts, _) <- stss ]
        conjmodel   = conjunctionAll checked
        seqComposed = conjmodel |>> conjmodel
        initVal  = case stss of
            [] -> error "no STSs loaded"
            (_, _, val):_ -> val    -- TODO: now each STS has its initial valuation, but this should be common as we are representing a single system
        model    = interpretSTS seqComposed initVal

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
