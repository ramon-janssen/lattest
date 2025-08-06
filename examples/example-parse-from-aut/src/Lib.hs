module Lib
    ( runMultipleTests
    ) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Adapter.StandardAdapters(Adapter,connectJSONSocketAdapterAcceptingInputs,withQuiescenceMillis)
import Lattest.Model.StandardAutomata
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, Verdict(Pass))
import Lattest.Exec.StandardTestControllers
import Lattest.Adapter.Adapter(send, Adapter(..), close, observe)
import Lattest.Util.ModelParsingUtils(dumpLTSdot, readAutFile)
import Control.Monad (forM_)

nrSteps = 10
nrTests = 10
initialSeed = 111

runMultipleTests :: IO ()
runMultipleTests = do
    let filePath = "./spec.aut"

    (inputAlphabet, outputAlphabet, states, Just transitions) <- readAutFile filePath

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
        initialConfiguration = pure "PickEither"
        spec = automaton initialConfiguration alphabet detConcTransitions
        model = interpretQuiescentConcrete spec

    -- Dump the DOT file next to the executable
    dumpLTSdot "LTS.dot" transitions
    putStrLn "Starting tests..."

    forM_ [1..nrTests] $ \i -> do
        putStrLn $ "\n--- Test #" ++ show i ++ " ---"
        putStrLn "Connecting..."
        adap <- connectJSONSocketAdapterAcceptingInputs :: IO (Adapter (IOAct String String) String)
        imp  <- withQuiescenceMillis 500 adap
        let testSelector = randomTestSelectorFromSeed (initialSeed + i)
                         `untilCondition` stopAfterSteps nrSteps
                         `observingOnly` printActions
                         `observingOnly` traceObserver
                         `andObserving` stateObserver
        (verdict, (observed, maybeMq)) <- runTester model testSelector imp
        putStrLn $ "Verdict: " ++ show verdict
        putStrLn $ "Observed: " ++ show observed
        putStrLn $ "Final state: " ++ show maybeMq
        close adap

    putStrLn "\nAll tests completed."
