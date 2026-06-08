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

import Test.Tasty
import Test.Tasty.Runners as Tasty
import Test.Tasty.Providers
import Test.HUnit 
import Test.Tasty.QuickCheck

durationSeconds :: Int
durationSeconds = 2

main :: IO ()
main = do
    hunitTests <- makeHUnitTests
    defaultMain $ 
      localOption (NumThreads 1) $ -- some of these tests open concrete sockets, and thus can't be run multiple times in parallel
      testGroup "Lattest-tests"
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
      localOption (NumThreads 1) $ -- some of these tests open concrete sockets, and thus can't be run multiple times in parallel
      singleTest "unit tests" $
      -- TestCase $
      -- propagateHUnitFailure $
      -- runTestTT $
      -- testGroup "unit tests" $ 
      TestList $
      -- map (\(TestCase a) -> testCase "unitTest" a) $
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

instance IsTest Test where
  run _ t _ = runTestTT t >>= \c ->
    if errors c + failures c > 0
      then return $ testFailed (show c)
      else return $ testPassed (show c)
  testOptions = pure []


createTestSMTRef :: IO SMT.SMTRef
createTestSMTRef =
    let cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = M.fromJust (Config.getProc cfg)
    in SMT.createSMTRef smtProc smtLog

