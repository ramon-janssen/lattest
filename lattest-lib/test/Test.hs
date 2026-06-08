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

import Test.Tasty
import Test.Tasty.HUnit
import Test.HUnit 
import Test.Tasty.QuickCheck
import Test.QuickCheck

durationSeconds :: Int
durationSeconds = 2

main :: IO ()
main = do
    hunitTests <- makeHUnitTests
    defaultMain $ testGroup "Lattest-tests"
      [ hunitTests
      , quickCheckTests
      ]
    -- -- unit tests, for fully written out scenarios
    -- putStrLn ">>>>>>> HUNIT TEST <<<<<<<<<"
    -- void $ timeout (durationSeconds * 10000000) $ runTestTT hunitTests
    -- -- property tests
    -- putStrLn ">>>>>>> QUICKCHECK TEST <<<<<<<<<"
    -- void $ runQuickCheckTests

quickCheckTests :: TestTree
quickCheckTests = testGroup "Quickcheck"
  [ quickCheckWithTimeout (prop_jsonStream :: [(Int,Bool,Bool)] -> Property) "jsonStream"
  , quickCheckWithTimeoutWithNum prop_consumeBufferedWith 15 "consumeBufferedWith"
--  Disable symbolic expression tests for now as they are too flaky
--    quickCheckWithTimeoutWithNum (prop_evalSymbolic :: PropEvalSymbolic Bool) 10000
--    smtRef <- createTestSMTRef
--    quickCheckWithTimeoutWithNumWithSize (prop_solveSymbolic smtRef) 100 2
  , quickCheckWithTimeoutWithNum prop_consumeBufferedWith 15 "consumeBufferedWith"
  , quickCheckWithTimeoutWithNum (prop_latticeIsCNF :: LatticeOp Int -> Bool) 10000 "latticeIsCNF"
  ]

    where
    quickCheckWithTimeout prop = quickCheckWithTimeoutWithNum prop 100
    quickCheckWithTimeoutWithNum prop n name = testProperty name $ \testparam -> within (durationSeconds * 1000000) (withMaxSuccess n (prop testparam))


makeHUnitTests :: IO TestTree
makeHUnitTests = do
    smt <- createTestSMTRef
    return $ 
      testGroup "unit tests" $ 
      map (\(TestCase a) -> testCase "unitTest" a) $
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


createTestSMTRef :: IO SMT.SMTRef
createTestSMTRef =
    let cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = M.fromJust (Config.getProc cfg)
    in SMT.createSMTRef smtProc smtLog

