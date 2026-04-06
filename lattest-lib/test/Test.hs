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
import Test.QuickCheck

durationSeconds :: Int
durationSeconds = 2

main :: IO ()
main = do
    -- unit tests, for fully written out scenarios
    putStrLn ">>>>>>> HUNIT TEST <<<<<<<<<"
    hunitTests <- makeHUnitTests
    void $ timeout (durationSeconds * 10000000) $ runTestTT hunitTests
    -- property tests
    putStrLn ">>>>>>> QUICKCHECK TEST <<<<<<<<<"
    void $ runQuickCheckTests

runQuickCheckTests :: IO ()
runQuickCheckTests = do
    quickCheckWithTimeout (prop_jsonStream :: [(Int,Bool,Bool)] -> Property)
    quickCheckWithTimeoutNum prop_consumeBufferedWith 15
--  Disable symbolic expression tests for now as they are too flaky
--    quickCheckWithTimeoutNum (prop_evalSymbolic :: PropEvalSymbolic Bool) 10000
--    smtRef <- createTestSMTRef
--    quickCheckWithTimeoutNumSize (prop_solveSymbolic smtRef) 100 2
    where
    quickCheckWithTimeout prop = quickCheckWithTimeoutNum prop 100
    quickCheckWithTimeoutNum prop n = quickCheck $ \testparam -> within (durationSeconds * 1000000) (withMaxSuccess n (prop testparam))
    
    quickCheckWithTimeoutNumSize prop n maxSize = quickCheck $ within (durationSeconds * 1000000) $ withMaxSuccess n $ forAllShrink (scale (max maxSize) arbitrary) shrink prop

makeHUnitTests :: IO Test
makeHUnitTests = do
    smt <- createTestSMTRef
    return $ TestList $
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
        testRandomFCorrect,
        testRandomFIncorrectOutput,
        testRandomFIncorrectInput,
        testSTSHappyFlow,
        testErrorThrowingGates,
        testSTSUnHappyFlow,
        testPrintSTS,
        testReadAutFile
        ]
        ++ testLatticeSTS
        ++ evalTests
        ++ fmap ($ smt) solveTests


createTestSMTRef =
    let cfg = Config.changeLog Config.defaultConfig True 
        smtLog = Config.smtLog cfg
        smtProc = M.fromJust (Config.getProc cfg)
    in SMT.createSMTRef smtProc smtLog










