import Test.Lattest.Adapter.StandardAdapters
import Test.Lattest.Exec.StandardTestControllers
import Test.Lattest.Exec.NComplete
import Test.Lattest.Exec.Testing
import Test.Lattest.Model.BoundedMonad
import Test.Lattest.Model.StandardAutomata
import Test.Lattest.Model.STSTest
import Test.Lattest.Model.Symbolic.Expr
import Test.Lattest.Util.ModelParsingUtils
import Test.Lattest.Util.STSJSONParserTest
import qualified Lattest.SMT as SMT
import Test.System.IO.Streams.Synchronized(prop_consumeBufferedWith, testConsumeBufferedWith,testConsumeBufferedWith_short, prop_jsonStream)
import qualified Data.Maybe as M

import Test.Tasty
import Test.Tasty.Runners as Tasty
import Test.Tasty.Providers as Tasty
import Test.HUnit as HUnit
import Test.Tasty.QuickCheck

durationSeconds :: Int
durationSeconds = 3

main :: IO ()
main = do
    hunitTests <- makeHUnitTests
    defaultMain $ 
      localOption (NumThreads 1) $ -- some of these tests open concrete sockets, and thus can't be run multiple times in parallel
      testGroup "Lattest-tests"
        [ hunitTests
        , quickCheckTests
        ]

quickCheckTests :: TestTree
quickCheckTests = testGroup "Quickcheck"
  [ quickCheckWithTimeout (prop_jsonStream :: [(Int,Bool,Bool)] -> Property) "jsonStream"
--  Disable symbolic expression tests for now as they are too flaky
--    quickCheckWithTimeoutWithNum (prop_evalSymbolic :: PropEvalSymbolic Bool) 10000
--    smtRef <- createTestSMTRef
--    quickCheckWithTimeoutWithNumWithSize (prop_solveSymbolic smtRef) 100 2
  , quickCheckWithTimeoutWithNum prop_consumeBufferedWith 15 "consumeBufferedWith"
  , quickCheckWithTimeoutWithNum (prop_latticeIsCNF :: LatticeOp Int -> Bool) 10000 "latticeIsCNF"
  ]

    where
    quickCheckWithTimeout prop = quickCheckWithTimeoutWithNum prop 100
    quickCheckWithTimeoutWithNum prop n name = testProperty name $ \testparam -> 
      within (durationSeconds * 1000000) $ withMaxSize 20 $
      -- Shrinking interacts really badly with the timeout: QuickCheck ends up on a search for the smallest input that exceeds the timelimit.
      noShrinking $ prop testparam


makeHUnitTests :: IO TestTree
makeHUnitTests = do
    return $
      localOption (NumThreads 1) $ -- some of these tests open concrete sockets, and thus can't be run in parallel
      singleTest "unit tests" $
      TestList $
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
        testReadAutFile,
        testSTSJSONParserNominal,
        testSTSJSONParserUnknownType,
        testSTSJSONParserUnsupportedGuardOperand,
        testSTSJSONParserUnsupportedAssignmentOperand,
        testSTSJSONParserMissingSwitches,
        testSTSJSONParserMissingGates,
        testSTSJSONParserAssignmentTypeMismatch,
        testSTSJSONParserGuardTypeMismatch,
        testSTSJSONParserGateIdDup,
        testLatticeCoffeeSTS
        ]
        ++ testLatticeSTS
        ++ testLatticeSTSQuiescence
        ++ evalTests
        ++ fmap ($ undefined) solveTests -- undefined is the unused smtref

-- TODO: This wraps HUnit tests into a Tasty test.
-- The reason we need this wrapper, is that plain HUnit
-- does not set the exit code, making CI runs pass even
-- when tests fail.
-- Instead, we should migrate the HUnit tests to
-- tasty-hunit, which exposes a very similar interface.
instance Tasty.IsTest HUnit.Test where
  run _ t _ = runTestTT t >>= \c ->
    if errors c + failures c > 0
      then return $ testFailed (show c)
      else return $ testPassed (show c)
  testOptions = pure []

