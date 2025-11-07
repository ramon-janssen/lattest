{-# LANGUAGE DeriveGeneric #-}

import Test.Lattest.Adapter.StandardAdapters
import Test.Lattest.Exec.StandardTestControllers
import Test.Lattest.Exec.Testing
import Test.Lattest.Model.StandardAutomata
import Test.Lattest.Model.STSTest
import Test.Lattest.Util.ModelParsingUtils
import Test.System.IO.Streams.Synchronized(prop_consumeBufferedWith, testConsumeBufferedWith,testConsumeBufferedWith_short, prop_jsonStream)

import Data.Functor(void)
import System.Timeout(timeout)
import Test.HUnit hiding (Path, path, assert)
import Test.QuickCheck (Property, quickCheck, within)

durationSeconds :: Int
durationSeconds = 2

main :: IO ()
main = do
    -- unit tests, for fully written out scenarios
    putStrLn ">>>>>>> HUNIT TEST <<<<<<<<<"
    void $ timeout (durationSeconds * 10000000) $ runTestTT hunitTests
    -- property tests
    putStrLn ">>>>>>> QUICKCHECK TEST <<<<<<<<<"
    void $ runQuickCheckTests

runQuickCheckTests :: IO ()
runQuickCheckTests = do
    quickCheckWithTimeout (prop_jsonStream :: [(Int,Bool,Bool)] -> Property)
    quickCheckWithTimeout prop_consumeBufferedWith
    where
    quickCheckWithTimeout prop = quickCheck $ \testparam -> within (durationSeconds * 1000000) (prop testparam)


hunitTests :: Test
hunitTests = TestList [
    testAccSeq,
    testConsumeBufferedWith,
    testConsumeBufferedWith_short,
    testJSONSocketAdapterByte,
    testAdapterAcceptingInput,
    testJSONSocketAdapterInt,
    testJSONSocketAdapterObject,
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
    testRandomFCorrect,
    testRandomFIncorrectOutput,
    testRandomFIncorrectInput,
    testSTSHappyFlow,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testReadAutFile
    ]











