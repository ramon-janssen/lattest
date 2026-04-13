{-# LANGUAGE DeriveGeneric #-}

import Test.Lattest.Adapter.StandardAdapters
import Test.Lattest.Exec.StandardTestControllers
import Test.Lattest.Exec.NComplete
import Test.Lattest.Exec.Testing
import Test.Lattest.Model.BoundedMonad
import Test.Lattest.Model.StandardAutomata
import Test.Lattest.Model.STSTest
import Test.Lattest.Model.Symbolic.Expr
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
    quickCheckWithTimeoutWithNum prop_consumeBufferedWith 15
--  Disable symbolic expression tests for now as they are too flaky
--    quickCheckWithTimeoutWithNum (prop_evalSymbolic :: PropEvalSymbolic Bool) 10000
--    smtRef <- createTestSMTRef
--    quickCheckWithTimeoutWithNumWithSize (prop_solveSymbolic smtRef) 100 2
    quickCheckWithTimeoutWithNum prop_consumeBufferedWith 15
    quickCheckWithTimeoutWithNum (prop_latticeIsCNF :: LatticeOp Int -> Bool) 10000

    where
    quickCheckWithTimeout prop = quickCheckWithTimeoutWithNum prop 100
    quickCheckWithTimeoutWithNum prop n = quickCheck $ \testparam -> within (durationSeconds * 1000000) (withMaxSuccess n (prop testparam))
    quickCheckWithTimeoutWithNumWithSize prop n maxSize = quickCheck $ within (durationSeconds * 1000000) $ withMaxSuccess n $ forAllShrink (scale (max maxSize) arbitrary) shrink prop

makeHUnitTests :: IO Test
makeHUnitTests = do
    smt <- createTestSMTRef
    return $ TestList $
        [
        testAccSeq,
        testADG,
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
        testExponentialNonDeterminism,
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
        ++ testLatticeSTSQuiescence
        ++ evalTests
        ++ fmap ($ smt) solveTests


createTestSMTRef =
    let cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = M.fromJust (Config.getProc cfg)
    in SMT.createSMTRef smtProc smtLog

