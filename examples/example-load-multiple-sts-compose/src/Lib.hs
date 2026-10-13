module Lib
    ( run
    ) where

import      Lattest.Model.Automaton
import      Lattest.Model.StandardAutomata
import      Lattest.Model.Symbolic.SolveSTS (offlineTests)
import      Lattest.Util.ReportUtils (appendTestTrace)
import      Lattest.Model.Symbolic.Expr (getVariables)
import      Lattest.Model.Symbolic.MCDCSTS (SplitMode(..), completeMCDCReportWith, prettyMCDCReport)
import      Lattest.Model.Alphabet (IOAct(..), SymInteract(..))
import      Lattest.Exec.StandardTestControllers
import      Lattest.Exec.StandardTestControllers.CompleteTestSuite (slowRandomInputCoverer, allSwitches, isInputSwitch, switchesTaken, observeInputCoverage, mergeInputCoverage, prettyPrintInputCoverage)
import      Lattest.Util.STSJSONParser (stsListFromJSONFile)
import      Lattest.Exec.Testing (Verdict(..))
import      Lattest.Model.BoundedMonad (BoundedConfiguration(..))
import      qualified Data.Map as Map
import      qualified Data.Set as Set
import      Lattest.Util.STSJSONWriter (stsListToJSONFile, stsToJSONFile)
import      Data.Tuple (swap)
import      Control.Monad.State (evalStateT)
import      System.Random (mkStdGen)
import      Data.Foldable (toList)
import      Data.List (isPrefixOf)
import      Data.Time (getZonedTime, formatTime, defaultTimeLocale, getCurrentTime, diffUTCTime)
import      System.IO (hSetBuffering, stdout, BufferMode(..))
import      Text.Printf (printf)

run :: IO ()
run = do
    hSetBuffering stdout LineBuffering
    putStrLn "loading STSs from JSON..."
    result <- stsListFromJSONFile "example.json"
    -- result <- stsListFromJSONFile "example_coffee_machine.json"
    stss <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    --putStrLn $ unlines $ map (\(_,sts,_,_,_,_) -> prettyPrint sts) stss
    -- Compose all parsed STSs
    let checked  = [ (sid, prependOutputChecks (\/) ("check_" ++) sts) | (sid, sts, _, _,_, _, _) <- stss ]
        conjunctedSTS = conjunctionAll checked
        conjunctModel = interpretSTS conjunctedSTS initVal
        --seqComposed = conjmodel |>> conjmodel
        (seqSelfComposed, discardedTransit) = selfSequentiallyPruned (getVariables initVal) conjunctedSTS
        (seqComposed, discardedTrans2) = conjunctModel `sequentiallyPruned` seqSelfComposed
        initVal  = case stss of
            [] -> error "no STSs loaded"
            (_, _, _, _, val,_,_):_ -> val    -- TODO: now each STS has its initial valuation, but this should be common as we are representing a single system
        gs = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,g,_,_,_,_) -> g) stss
        as = Map.fromList $ map swap $ Map.toList $ Map.unions $ map (\(_,_,_,a,_,_,_) -> a) stss
        es =                                        Map.unions $ map (\(_,_,_,_,_,e,_) -> e) stss
        fs =                                        Map.unions $ map (\(_,_,_,_,_,_,f) -> f) stss

    --putStrLn $ prettyPrintIntrp seqComposed
    --print discardedTransit
    timestamp <- formatTime defaultTimeLocale "%Y-%m-%d_%H-%M-%S" <$> getZonedTime 
    putStrLn ("computing offline test cases..." ++ timestamp)
    let nrSteps = 30
        nrTrailingSteps = 10 -- the extra steps a test may take to end right after an output
        maxStale = 10 :: Int -- stop after this many consecutive test cases that did not increase coverage
        randomSeed = 678
        tracesFile = "test_traces_" ++ timestamp ++ ".txt"

        observeVerdict (Just _) _ _ _ = error "shouldn't happen?"
        observeVerdict Nothing _ _ lattice
          | isForbidden lattice = pure $ Just Fail
          | isUnderspecified lattice = pure $ Just Pass
          | otherwise = pure Nothing
    
    writeFile tracesFile ""

    putStrLn "completing MCDC..."
    let seqComposedSTS = syntacticAutomaton seqComposed
        inputGates = ["In1", "In4", "In5", "In8", "In7"]
        -- the guards that restrict a parameter to its domain are named G_<parameter>.<constraint>
        domainGuards = [ guard | (_, _, guards, _, _, _, _) <- stss, (name, guard) <- Map.toList guards, "G_" `isPrefixOf` name ]
    (mcdcComposed, mcdcReport) <- completeMCDCReportWith SplitInitial [1,2] domainGuards seqComposedSTS inputGates
    putStrLn $ prettyMCDCReport mcdcReport
    -- the MC/DC completed model is the one that is tested
    let model = interpretSTS mcdcComposed initVal
        -- all switches taken in a test case, also the ones that were covered by an earlier test case
        observeSwitchesTaken = observer Set.empty (\taken intrpr act mq -> pure $ taken <> switchesTaken intrpr mq act) pure
        switches      = allSwitches model
        inputSwitches = Set.filter isInputSwitch switches
        -- covered/total, with the percentage
        coverage :: Int -> Int -> String
        coverage covered total = show covered ++ "/" ++ show total
            ++ if total == 0 then "" else " (" ++ printf "%.1f" (100 * fromIntegral covered / fromIntegral total :: Double) ++ "%)"

    let composedFilename = "example_composed_mcdc_another.json"
    putStrLn $ "writing composition to file: " ++ composedFilename
    -- To write to a file:
    stsToJSONFile composedFilename "stscomposedmcdc" mcdcComposed gs as es fs initVal

    writeFile tracesFile ""

    -- the covered switches and the input coverage report are carried from one kept test case to the next
    let testCases toCover n kept stale
          | Set.null toCover = pure (toCover, n, kept, "full switch coverage reached")
          | stale >= maxStale = pure (toCover, n, kept, "the last " ++ show maxStale ++ " test cases did not increase coverage")
          | otherwise = do
              -- target the (location, gate) pairs of input switches not covered yet
              let controller = observeControllerState (slowRandomInputCoverer model (Just toCover) nrSteps (mkStdGen (randomSeed + n)) `untilCondition` stopAfterStepsAtOutput nrSteps nrTrailingSteps) `andObserving` observer Nothing observeVerdict pure `andObserving` (observeInputCoverage `andObserving` observeSwitchesTaken)
              start <- getCurrentTime
              tests <- evalStateT (offlineTests model controller $ \st -> ((fst $ fst st, Just Fail), snd st)) (mkStdGen (randomSeed + n))
              -- compute the covered switches
              let toCover' = foldr (Set.intersection . (\((((_,x,_,_),_),_),_) -> x)) toCover (toList tests)
                  -- prefix with the time at which the test case was finished, and how long it took to generate
                  report' msg = do
                    end <- getCurrentTime
                    now <- formatTime defaultTimeLocale "%H:%M:%S" <$> getZonedTime
                    putStrLn $ now ++ " test " ++ show (n + 1) ++ " (" ++ show (diffUTCTime end start) ++ "): " ++ msg
              if Set.size toCover' < Set.size toCover
                then do
                  -- the test case increases coverage: keep it
                  appendTestTrace tracesFile model (snd . fst <$> tests)
                  report' $ "kept, switch coverage "
                      ++ coverage (Set.size switches - Set.size toCover') (Set.size switches)
                      ++ ", input switch coverage "
                      ++ coverage (Set.size inputSwitches - Set.size (Set.filter isInputSwitch toCover')) (Set.size inputSwitches)
                  -- a test is a tree with a report and the switches taken per leaf, so merge over the leaves
                  let testReport = foldr (mergeInputCoverage . fst . snd) mempty (toList tests)
                      testTaken = foldMap (snd . snd) (toList tests)
                  testCases toCover' (n + 1) ((snd . fst <$> tests, testReport, testTaken) : kept) 0
                else do
                  report' "discarded"
                  testCases toCover (n + 1) kept (stale + 1)
    (leftToCover, nrGenerated, kept, stopReason) <- testCases switches (0 :: Int) [] (0 :: Int)
    putStrLn $ "stopped: " ++ stopReason
    -- a test case that added coverage when it was generated, may be made redundant by the test cases generated after it
    let takenBy (_, _, taken) = taken
        minimal = minimalCover takenBy kept
        suiteReport = foldr (\(_, testReport, _) -> mergeInputCoverage testReport) mempty minimal
    writeFile tracesFile ""
    mapM_ (\(test, _, _) -> appendTestTrace tracesFile model test) minimal
    putStrLn $ "generated " ++ show nrGenerated ++ " test cases, of which " ++ show (length kept) ++ " increased coverage; kept the "
        ++ show (length minimal) ++ " that are needed for the same coverage in " ++ tracesFile
    putStrLn $ show (length $ irreplaceable takenBy kept) ++ " of the test cases that increased coverage take a switch that none of the others take"
    putStrLn "input coverage of the test suite:"
    putStr $ prettyPrintInputCoverage es fs suiteReport
    putStrLn $ ("left to cover: " ++ show leftToCover)

-- | Pick elements that together cover the same as all given elements: going from the last element to the first, pick the ones
-- that cover something that the elements picked so far do not. Then drop the picked elements that the other picked elements have
-- made redundant, earlier elements first. The remaining elements are returned in their original order.
minimalCover :: Ord a => (t -> Set.Set a) -> [t] -> [t]
minimalCover cover ts = dropRedundant [] $ fst $ foldr pick ([], Set.empty) ts
  where
    -- foldr goes over the elements from last to first
    pick t (picked, covered)
      | cover t `Set.isSubsetOf` covered = (picked, covered)
      | otherwise = (t : picked, covered <> cover t)
    dropRedundant needed [] = reverse needed
    dropRedundant needed (t : rest)
      | cover t `Set.isSubsetOf` foldMap cover (needed ++ rest) = dropRedundant needed rest
      | otherwise = dropRedundant (t : needed) rest

-- | The elements that cover something that none of the other elements cover, so that no selection can do without them.
irreplaceable :: Ord a => (t -> Set.Set a) -> [t] -> [t]
irreplaceable cover ts = [ t | (i, t) <- indexed, not $ cover t `Set.isSubsetOf` foldMap (cover . snd) (filter ((/= i) . fst) indexed) ]
  where indexed = zip [0 :: Int ..] ts
