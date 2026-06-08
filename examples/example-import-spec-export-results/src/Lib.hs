module Lib
    ( runMultipleTests
    ) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Adapter.StandardAdapters(Adapter,connectJSONSocketAdapterAcceptingInputs,withQuiescenceMillis)
import Lattest.Model.StandardAutomata
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester)
import Lattest.Exec.StandardTestControllers
import Lattest.Adapter.Adapter(send, Adapter(..), close, observe)
import Lattest.Util.ModelParsingUtils(dumpLTSdot, readAutFile)
import Lattest.Util.ReportUtils(writeResults, flushResults, initResultsFile, TestResult(..))
import Control.Monad (forM_, foldM)
import qualified Data.Sequence as Seq

nrSteps = 10
nrTests = 12
initialSeed = 111
csvPath = "results.csv"

runMultipleTests :: IO ()
runMultipleTests = do
    let filePath = "./spec.aut"

    (inputAlphabet, outputAlphabet, states, initialState, maybeTransitions) <- readAutFile filePath
    case maybeTransitions of
        Nothing -> error "No transitions found"
        Just transitions -> do
            putStrLn "Input Alphabet:"
            print inputAlphabet
            putStrLn "\nOutput Alphabet:"
            print outputAlphabet
            putStrLn "\nStates:"
            print states
            putStrLn "\nTransitions:"
            mapM_ print transitions

            let Just detConcTransitions = detConcTransFromRel transitions
                alphabet = ioAlphabet inputAlphabet outputAlphabet
                initialConfiguration = pure initialState
                spec = automaton initialConfiguration alphabet detConcTransitions
                model = interpretQuiescentConcrete spec

            -- Initialize CSV file for results (with default header)
            initResultsFile csvPath Nothing
            putStrLn "Starting tests..."
            
            finalRevBuf <- foldM (\revBuf i -> do
                putStrLn $ "\n--- Test #" ++ show i ++ " ---"
                putStrLn "Connecting..."
                adap <- connectJSONSocketAdapterAcceptingInputs :: IO (Adapter (IOAct String String) String)
                imp  <- withQuiescenceMillis 200 adap
                let testSelector = randomTestSelectorFromSeed (initialSeed + i)
                                `untilCondition` stopAfterSteps nrSteps
                                `observingOnly` printActions
                                `observingOnly` traceObserver
                                `andObserving` stateObserver
                (verdict, (observed, maybeMq)) <- runTester model testSelector imp
                close adap
                writeResults csvPath [TestResult i (show verdict) (show observed)] revBuf 5
                ) (Seq.empty) [1..nrTests]
            
            putStrLn "\nAll tests completed."
            -- Flush any remaining results to CSV
            flushResults csvPath finalRevBuf

            -- Dump the DOT file with the specification
            dumpLTSdot "LTS.dot" transitions