module Lib
    ( run
    ) where

import      Lattest.Model.Automaton
import      Lattest.Model.StandardAutomata
import      Lattest.Model.Symbolic.SolveSTS (offlineTests)
import      Lattest.Util.ReportUtils (appendTestTrace)
import      Lattest.Model.Symbolic.Expr (getVariables)
import      Lattest.Exec.StandardTestControllers
import      Lattest.Util.STSJSONParser (stsListFromJSONFile)
import      Lattest.Exec.Testing (Verdict(..))
import      Lattest.Model.BoundedMonad (BoundedConfiguration(..))
import      qualified Data.Map as Map
import      Lattest.Util.STSJSONWriter (stsListToJSONFile, stsToJSONFile)
import      Data.Tuple (swap)
import      Control.Monad.State (evalStateT)
import      System.Random (mkStdGen)
import      Control.Monad (forM_)
import      Data.Time (getZonedTime, formatTime, defaultTimeLocale)

run :: IO ()
run = do
    putStrLn "loading STSs from JSON..."
    result <- stsListFromJSONFile "example.json"
    -- result <- stsListFromJSONFile "example_coffee_machine.json"
    stss <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    --putStrLn $ unlines $ map (\(_,sts,_,_,_,_) -> prettyPrint sts) stss
    -- Compose all parsed STSs
    let checked  = [ (sid, prependOutputChecks (\/) ("check_" ++) sts) | (sid, sts, _, _,_, _) <- stss ]
        conjunctedSTS = conjunctionAll checked
        conjunctModel = interpretSTS conjunctedSTS initVal
        --seqComposed = conjmodel |>> conjmodel
        (seqSelfComposed, discardedTransit) = selfSequentiallyPruned (getVariables initVal) conjunctedSTS
        (seqComposed, discardedTrans2) = conjunctModel `sequentiallyPruned` seqSelfComposed
        initVal  = case stss of
            [] -> error "no STSs loaded"
            (_, _, _, _, val,_):_ -> val    -- TODO: now each STS has its initial valuation, but this should be common as we are representing a single system
        gs = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,g,_,_,_) -> g) stss
        as = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,_,a,_,_) -> a) stss
        es =                                        Map.unions $ map (\(_,_,_,_,_,e) -> e) stss

    --putStrLn $ prettyPrintIntrp seqComposed
    --print discardedTransit
    timestamp <- formatTime defaultTimeLocale "%Y-%m-%d_%H-%M-%S" <$> getZonedTime 
    putStrLn ("computing offline test cases..." ++ timestamp)
    let nrSteps = 10
        nrTests = 10 :: Int
        randomSeed = 111
        tracesFile = "test_traces_" ++ timestamp ++ ".txt"

        observeVerdict _ _ _ lattice
          | isForbidden lattice = pure $ Just Fail
          | isUnderspecified lattice = pure $ Just Pass
          | otherwise = pure Nothing
    
    writeFile tracesFile ""

    -- one test case per seed
    forM_ [1 .. nrTests] $ \n -> do
        putStrLn $ "  test " ++ show n ++ "/" ++ show nrTests
        let controller = randomDataTestSelectorFromSeed (randomSeed + n) `untilCondition` stopAfterSteps nrSteps `observingOnly` observer Nothing observeVerdict pure
        tests <- evalStateT (offlineTests seqComposed controller) (mkStdGen (randomSeed + n))
        appendTestTrace tracesFile seqComposed tests
    putStrLn $ "wrote " ++ show nrTests ++ " test cases to " ++ tracesFile

    print "Composition finished, writing result to file..."
    -- To write to a file:
    stsToJSONFile "example_composed2.json" "stscomposed" (syntacticAutomaton seqComposed) gs as es initVal
