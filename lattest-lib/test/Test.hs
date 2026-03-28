{-# LANGUAGE DeriveGeneric #-}

import Test.Lattest.Adapter.StandardAdapters
import Test.Lattest.Exec.StandardTestControllers
import Test.Lattest.Exec.Testing
import Test.Lattest.Model.StandardAutomata
import Test.Lattest.Model.STSTest
import Test.Lattest.Model.Symbolic.ValExpr.ValExpr
import Test.Lattest.Util.ModelParsingUtils
import qualified Lattest.SMT.Config as Config
import qualified Lattest.SMT.SMT as SMT
import Test.System.IO.Streams.Synchronized(prop_consumeBufferedWith, testConsumeBufferedWith,testConsumeBufferedWith_short, prop_jsonStream)

import qualified Data.Maybe as M
import Data.Functor(void)
import System.Timeout(timeout)
import Test.HUnit hiding (Path, path, assert)
import Test.QuickCheck (Property, quickCheck, within, withMaxSuccess)

durationSeconds :: Int
durationSeconds = 2

main :: IO ()
main = do
    -- unit tests, for fully written out scenarios
--    putStrLn ">>>>>>> HUNIT TEST <<<<<<<<<"
--    void $ timeout (durationSeconds * 10000000) $ runTestTT hunitTests
    -- property tests
    putStrLn ">>>>>>> QUICKCHECK TEST <<<<<<<<<"
    void $ runQuickCheckTests

runQuickCheckTests :: IO ()
runQuickCheckTests = do
    quickCheckWithTimeout (prop_jsonStream :: [(Int,Bool,Bool)] -> Property)
    quickCheckWithTimeoutWithNum prop_consumeBufferedWith 15
    --quickCheckWithTimeoutWithNum (prop_evalSymbolic :: PropEvalSymbolic Bool) 10000
    smtRef <- createTestSMTRef
    quickCheckWithTimeoutWithNum (prop_solveSymbolic smtRef) 100
    where
    quickCheckWithTimeout prop = quickCheckWithTimeoutWithNum prop 100
    quickCheckWithTimeoutWithNum prop n = quickCheck $ \testparam -> within (durationSeconds * 1000000) (withMaxSuccess n (prop testparam))
    createTestSMTRef =
        let cfg = Config.changeLog Config.defaultConfig True 
            smtLog = Config.smtLog cfg
            smtProc = M.fromJust (Config.getProc cfg)
        in SMT.createSMTRef smtProc smtLog

hunitTests :: Test
hunitTests = TestList $
    [
    testConsumeBufferedWith,
    testConsumeBufferedWith_short,
    testJSONSocketAdapterByte,
    testAdapterAcceptingInput,
    testJSONSocketAdapterInt,
    testJSONSocketAdapterObject,
    testQuiscence,
    testInputDelay,
    testTraceHappy,
    testTraceFailsAtLastOutput,
    testTraceFailsBeforeLastOutput,
    testTraceIncompleteAtLastOutput,
    testTraceIncompleteBeforeLastOutput,
    testTraceFailsWithQuiescence,
    testOutputOutsideAlphabet,
    testSpecF,
    testPrintSpecF,
    testSpecG,
    testSpecGQuiescent,
    testSTSTestSelection,
    testSTSDisnjunction1,
    testRandomFCorrect,
    testRandomFIncorrectOutput,
    testRandomFIncorrectInput,
    testSTSHappyFlow,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testReadAutFile
    ]
    ++ valExprTests











