module Lib
    ( run
    ) where

import qualified Lattest.SMT.Config as Config
import qualified Lattest.SMT.SMT as SMT
import qualified Data.Maybe as Maybe
import           Lattest.Adapter.StandardAdapters
import           Lattest.Model.Alphabet (IOSuspGateValue, GateValue)
import           Lattest.Model.StandardAutomata
import           Lattest.Exec.Testing(TestController(..), Verdict(..), runTester)
import           Lattest.Exec.StandardTestControllers
import           Lattest.Util.STSJSONParser (stsFromJSONFile)

run :: IO ()
run = do
    putStrLn "loading STS from JSON..."
    result <- stsFromJSONFile "toy_example_sts_coffee.json"
    (sts, initVal) <- case result of
        Left  err -> error $ "failed to parse STS JSON: " ++ err
        Right r   -> return r

    let model = interpretSTSQuiescent sts initVal

    let cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = Maybe.fromJust (Config.getProc cfg)
    putStrLn "starting SMT solver..."
    smtRef <- SMT.createSMTRef smtProc smtLog

    putStrLn "connecting to SUT..."
    let quiescenceMillis = 300
        delayMillis = 100
    adap <- connectJSONSocketAdapterAcceptingInputs
                >>= withQuiescenceMillis quiescenceMillis
                >>= withInputDelayMillis delayMillis
                >>= asSymbolicSuspAdapter
                    :: IO (Adapter (IOSuspGateValue String String) (Maybe (GateValue String)))

    -- NOTE: These tests are expected to fail; the spec was constructed to depict how overlapping guards work
    putStrLn "starting test..."
    let nrSteps = 50
        probabilityOfWaitForOutput = 0.0
        randomSeed = 456
        testSelector =
            randomDataOrWaitForOutputTestSelectorFromSeed smtRef randomSeed probabilityOfWaitForOutput
            `untilCondition` stopAfterSteps nrSteps
            `observingOnly` traceObserver
            `andObserving` stateObserver
            `andObserving` inconclusiveStateObserver
    (verdict, (observed, maybeMq)) <- runTester model testSelector adap

    putStrLn $ "verdict: " ++ show verdict
    putStrLn $ "observed: " ++ show observed
    putStrLn $ "final state: " ++ show maybeMq
