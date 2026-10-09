module Lib
    ( run
    ) where

import           Lattest.Model.Automaton (prettyPrintIntrp, prettyPrint, syntacticAutomaton)
import           Lattest.Model.Symbolic.Expr (getVariables)
import           Lattest.Model.StandardAutomata
import           Lattest.Model.Symbolic.SolveSTS (offlineTests)
import           Lattest.Util.ReportUtils (appendTestTrace)
import           Lattest.Exec.StandardTestControllers
import           Lattest.Exec.StandardTestControllers.CompleteTestSuite(slowRandomInputCoverer, allSwitches, isInputSwitch, observeInputCoverage, mergeInputCoverage, prettyPrintInputCoverage)
import           Lattest.Util.STSJSONParser (stsListFromJSONFile)
import Lattest.Exec.Testing (Verdict(..))
import Lattest.Model.BoundedMonad (BoundedConfiguration(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Util.STSJSONWriter (stsListToJSONFile, stsToJSONFile)
import Data.Tuple (swap)
import Control.Monad.State (evalStateT)
import System.Random (mkStdGen)
import Data.Foldable (toList)
import Data.Time (getZonedTime, formatTime, defaultTimeLocale)

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
        model = seqComposed
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
    let nrSteps = 8
        nrTrailingSteps = 5 -- the extra steps a test may take to end right after an output
        maxStale = 20 :: Int -- stop after this many consecutive test cases that did not increase coverage
        nrTests = 10 :: Int
        randomSeed = 456
        tracesFile = "test_traces_" ++ timestamp ++ ".txt"

        observeVerdict (Just _) _ _ _ = error "shouldn't happen?"
        observeVerdict Nothing _ _ lattice
          | isForbidden lattice = pure $ Just Fail
          | isUnderspecified lattice = pure $ Just Pass
          | otherwise = pure Nothing
        switches      = allSwitches model
        inputSwitches = Set.filter isInputSwitch switches

    writeFile tracesFile ""

    -- the covered switches and the input coverage report are carried from one kept test case to the next
    let testCases toCover report n kept stale
          | Set.null toCover = pure (toCover, report, n, kept, "full switch coverage reached")
          | stale >= maxStale = pure (toCover, report, n, kept, "the last " ++ show maxStale ++ " test cases did not increase coverage")
          | otherwise = do
              -- target the (location, gate) pairs of input switches not covered yet
              let controller = observeControllerState (slowRandomInputCoverer model (Just toCover) nrSteps (mkStdGen (randomSeed + n)) `untilCondition` stopAfterStepsAtOutput nrSteps nrTrailingSteps) `andObserving` observer Nothing observeVerdict pure `andObserving` observeInputCoverage
              tests <- evalStateT (offlineTests model controller $ \st -> ((fst $ fst st, Just Fail), snd st)) (mkStdGen (randomSeed + n))
              -- compute the covered switches
              let toCover' = foldr (Set.intersection . (\((((_,x,_,_),_),_),_) -> x)) toCover (toList tests)
              if Set.size toCover' < Set.size toCover
                then do
                  -- the test case increases coverage: keep it
                  appendTestTrace tracesFile model (snd . fst <$> tests)
                  putStrLn $ "test " ++ show (n + 1) ++ ": kept, switch coverage "
                      ++ show (Set.size switches - Set.size toCover') ++ "/" ++ show (Set.size switches)
                      ++ ", input switch coverage "
                      ++ show (Set.size inputSwitches - Set.size (Set.filter isInputSwitch toCover')) ++ "/" ++ show (Set.size inputSwitches)
                  -- a test is a tree with a report per leaf, so merge over the leaves as well
                  testCases toCover' (foldr (mergeInputCoverage . snd) report (toList tests)) (n + 1) (kept + 1) 0
                else do
                  putStrLn $ "test " ++ show (n + 1) ++ ": discarded"
                  testCases toCover report (n + 1) kept (stale + 1)
    (leftToCover, suiteReport, nrGenerated, nrKept, stopReason) <- testCases switches mempty 0 (0 :: Int) (0 :: Int)
    putStrLn $ "stopped: " ++ stopReason
    putStrLn $ "generated " ++ show nrGenerated ++ " test cases, kept " ++ show nrKept ++ " in " ++ tracesFile
    putStrLn "input coverage of the test suite:"
    putStr $ prettyPrintInputCoverage suiteReport
    putStrLn $ ("left to cover: " ++ show leftToCover)

    print "Composition finished, writing result to file..."
    -- To write to a file:
    stsToJSONFile "example_composed2.json" "stscomposed" (syntacticAutomaton seqComposed) gs as es initVal
