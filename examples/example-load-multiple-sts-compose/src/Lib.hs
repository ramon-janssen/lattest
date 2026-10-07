module Lib
    ( run
    ) where

import           Lattest.Model.Automaton (prettyPrintIntrp, prettyPrint, syntacticAutomaton)
import           Lattest.Model.Symbolic.Expr (getVariables)
import           Lattest.Model.StandardAutomata
import           Lattest.Model.Symbolic.SolveSTS (offlineTests)
import           Lattest.Exec.StandardTestControllers
import           Lattest.Exec.StandardTestControllers.CompleteTestSuite(randomCoveringTestSelectorFromSeed, allSwitches, isInputSwitch, observeInputCoverage, mergeInputCoverage, prettyPrintInputCoverage)
import           Lattest.Util.STSJSONParser (stsListFromJSONFile)
import Lattest.Exec.Testing (Verdict(..))
import Lattest.Model.BoundedMonad (BoundedConfiguration(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Util.STSJSONWriter (stsListToJSONFile, stsToJSONFile)
import Data.Tuple (swap)
import Control.Monad (foldM)
import Data.Foldable (toList)

run :: IO ()
run = do
    putStrLn "loading STSs from JSON..."
    result <- stsListFromJSONFile "example.json"
    -- result <- stsListFromJSONFile "example_coffee_machine.json"
    stss <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    --putStrLn $ unlines $ map (\(_,sts,_,_,_) -> prettyPrint sts) stss
    -- Compose all parsed STSs
    let checked  = [ (sid, prependOutputChecks (\/) ("check_" ++) sts) | (sid, sts, _, _, _) <- stss ]
        conjunctedSTS = conjunctionAll checked
        conjunctModel = interpretSTS conjunctedSTS initVal
        --seqComposed = conjmodel |>> conjmodel
        (seqSelfComposed, discardedTransit) = selfSequentiallyPruned (getVariables initVal) conjunctedSTS
        (seqComposed, discardedTrans2) = conjunctModel `sequentiallyPruned` seqSelfComposed
        model = seqComposed
        initVal  = case stss of
            [] -> error "no STSs loaded"
            (_, _, _, _, val):_ -> val    -- TODO: now each STS has its initial valuation, but this should be common as we are representing a single system
        gs = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,g,_,_) -> g) stss
        as = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,_,a,_) -> a) stss

    --putStrLn $ prettyPrintIntrp seqComposed
    --print discardedTransit

    putStrLn "computing offline test cases..."
    let nrSteps = 28
        nrTests = 8
        randomSeed = 456
        observeVerdict (Just _) _ _ _ = error "shouldn't happen?"
        observeVerdict Nothing _ _ lattice
          | isForbidden lattice = pure $ Just Fail
          | isUnderspecified lattice = pure $ Just Pass
          | otherwise = pure Nothing
        switches      = allSwitches model
        inputSwitches = Set.filter isInputSwitch switches
    -- the covered switches and the input coverage report are carried from one test case to the next
    let testCase (toCover, report) n = do
          -- target the (location, gate) pairs of input switches not covered yet
          let controller = observeControllerState (randomCoveringTestSelectorFromSeed model (Just toCover) (randomSeed + n) `untilCondition` stopAfterSteps nrSteps) `andObserving` observer Nothing observeVerdict pure `andObserving` observeInputCoverage
          tests <- offlineTests model controller $ \st -> ((fst $ fst st, Just Fail), snd st)
          -- compute the covered switches
          -- print $ map (\(((_,x,_,_),_),_) -> x) $ toList tests
          let toCover' = foldr (Set.intersection . (\((((_,x,_,_),_),_),_) -> x)) switches (toList tests)
          putStrLn $ "after test " ++ show (n + 1) ++ ": switch coverage "
              ++ show (Set.size switches - Set.size toCover') ++ "/" ++ show (Set.size switches)
              ++ ", input switch coverage "
              ++ show (Set.size inputSwitches - Set.size (Set.filter isInputSwitch toCover')) ++ "/" ++ show (Set.size inputSwitches)
          -- a test is a tree with a report per leaf, so merge over the leaves as well
          pure (toCover', foldr (mergeInputCoverage . snd) report (toList tests))
    (_, suiteReport) <- foldM testCase (switches, mempty) [0 .. nrTests - 1]
    putStrLn "input coverage of the test suite:"
    putStr $ prettyPrintInputCoverage suiteReport

    print "Composition finished, writing result to file..."
    -- To write to a file:
    stsToJSONFile "example_composed2.json" "stscomposed" (syntacticAutomaton seqComposed) gs as initVal
