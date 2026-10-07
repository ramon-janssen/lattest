module Lib
    ( run
    ) where

import           Lattest.Model.Automaton (prependOutputChecks, prettyPrintIntrp, prettyPrint)
import           Lattest.Model.StandardAutomata
import           Lattest.Model.Symbolic.SolveSTS (offlineTests)
import           Lattest.Exec.StandardTestControllers
import           Lattest.Exec.StandardTestControllers.CompleteTestSuite(randomCoveringTestSelectorFromSeed, allSwitches, isInputSwitch, observeInputCoverage)
import           Lattest.Util.STSJSONParser (stsListFromJSONFile)
import Lattest.Exec.Testing (Verdict(..))
import Lattest.Model.BoundedMonad (BoundedConfiguration(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Util.STSJSONWriter (stsListToJSONFile, stsToJSONFile)
import Data.Tuple (swap)
import Control.Monad (foldM_)
import Data.Foldable (toList)

run :: IO ()
run = do
    putStrLn "loading STSs from JSON..."
    result <- stsListFromJSONFile "example_coffee_machine.json"
    stss <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    -- putStrLn $ unlines $ map (\(_,sts,_,_,_) -> prettyPrint sts) stss
    -- Compose all parsed STSs
    let checked  = [ (sid, prependOutputChecks (\/) ("check_" ++) sts) | (sid, sts, _, _, _) <- stss ]
        conjmodel   = conjunctionAll checked
        seqSelfComposed = conjmodel |>> conjmodel
        seqComposed = conjmodel |> seqSelfComposed
        initVal  = case stss of
            [] -> error "no STSs loaded"
            (_, _, _, _, val):_ -> val    -- TODO: now each STS has its initial valuation, but this should be common as we are representing a single system
        model    = interpretSTS seqComposed initVal
        gs = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,g,_,_) -> g) stss
        as = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,_,a,_) -> a) stss

    putStrLn $ prettyPrintIntrp model

    putStrLn "computing offline test cases..."
    let nrSteps = 5
        nrTests = 3
        randomSeed = 456
        observeVerdict (Just _) _ _ _ = error "shouldn't happen?"
        observeVerdict Nothing _ _ lattice
          | isForbidden lattice = pure $ Just Fail
          | isUnderspecified lattice = pure $ Just Pass
          | otherwise = pure Nothing
        switches      = allSwitches model
        inputSwitches = Set.filter isInputSwitch switches
    -- the covered switches are carried from one test case to the next
    let testCase toCover n = do
          -- target the (location, gate) pairs of input switches not covered yet
          let controller = observeControllerState (randomCoveringTestSelectorFromSeed model (Just toCover) (randomSeed + n) `untilCondition` stopAfterSteps nrSteps) `andObserving` observer Nothing observeVerdict pure `andObserving` observeInputCoverage
          tests <- offlineTests model controller $ \st -> ((fst $ fst st, Just Fail), snd st)
          print $ snd <$> tests
          -- compute the covered switches
          -- print $ map (\(((_,x,_,_),_),_) -> x) $ toList tests
          let toCover' = foldr (Set.intersection . (\((((_,x,_,_),_),_),_) -> x)) switches (toList tests)
          putStrLn $ "after test " ++ show (n + 1) ++ ": switch coverage "
              ++ show (Set.size switches - Set.size toCover') ++ "/" ++ show (Set.size switches)
              ++ ", input switch coverage "
              ++ show (Set.size inputSwitches - Set.size (Set.filter isInputSwitch toCover')) ++ "/" ++ show (Set.size inputSwitches)
          pure toCover'
    foldM_ testCase switches [0 .. nrTests - 1]

    -- To write to a file:
    -- stsListToJSONFile "example_single_stss.json" (map (\(id,sts,_,_,val) -> (id,sts,val)) stss) gs as
    stsToJSONFile "example_composed.json" "stscomposed" seqComposed gs as initVal
