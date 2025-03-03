{-# LANGUAGE DeriveGeneric #-}
module Test.Lattest.Exec.StandardTestControllers (
testRandomFCorrect,
testRandomFIncorrectOutput,
testRandomFIncorrectInput
)
where

import Test.HUnit hiding (Path, path)

import Test.Lattest.Model.StandardAutomata(IF(..),OF(..),sf,IG(..),OG(..),sg)

-- TODO prototype imports, (re)move or insert into alphabetical order
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, Verdict(Pass))
import Lattest.Model.StateConfiguration(DetState(..),NonDetState(..), isConclusive)
import Lattest.Model.Automaton(AutSyn, AutSem, automaton, transRel, locConf)
import Lattest.Model.StandardAutomata(ConcreteAutSem, semanticsConcrete, semanticsQuiescentInputAttemptConcrete)
import Lattest.Model.Alphabet(IOAct(..), isOutput, TimeoutIO, Timeout(..), Attempt (..))
import Lattest.Util.Utils((&&&))
import System.Random(StdGen, uniformR, mkStdGen)
import Data.List (span)
import qualified Data.Map as Map (toList, insert, fromList)
import qualified Data.Set as Set (toList, fromList)
import Lattest.Adapter.StandardAdapters(Adapter,pureAdapter,acceptingInputs)

nrSteps = 50
testSelector = randomTestSelectorFromSeed 456 `untilCondition` stopAfterSteps nrSteps `observingOnly` traceObserver `andObserving` stateObserver

x = Out X
y = Out Y
af = In A
bf = In B

data StateFDet = Q0fd | Q1fd | Q2fd deriving (Show, Eq, Ord)
tFDetCorrect Q0fd = Map.fromList [(af, Q1fd), (x, Q0fd), (y, Q0fd)]
tFDetCorrect Q1fd = Map.fromList [(af, Q1fd), (x, Q0fd), (y, Q2fd)]
tFDetCorrect Q2fd = Map.fromList [(af, Q1fd), (bf, Q0fd), (y, Q2fd)]
impFDetCorrect = pureAdapter (mkStdGen 123) 0.5 tFDetCorrect Q0fd

testRandomFCorrect :: Test
testRandomFCorrect = TestCase $ do
    imp <- impFDetCorrect
    let model = semanticsQuiescentInputAttemptConcrete sf
    (verdict, (observed, maybeMq)) <- runTester model testSelector imp
    assertEqual "testRandomFCorrect should pass" Pass verdict
    assertEqual "incorrect number of observations made" nrSteps (length observed)
    assertEqual "final state should be definite" (Just True) (isConclusive <$> maybeMq)

tFDetIncorrectOutput Q0fd = Map.fromList [(af, Q1fd), (x, Q0fd), (y, Q0fd)]
tFDetIncorrectOutput Q1fd = Map.fromList [(af, Q1fd), (x, Q0fd), (y, Q2fd)]
tFDetIncorrectOutput Q2fd = Map.fromList [(af, Q1fd), (bf, Q0fd), (x, Q2fd), (y, Q2fd)] -- incorrect x-transition
impFDetIncorrectOutput = pureAdapter (mkStdGen 123) 0.5 tFDetIncorrectOutput Q0fd

testRandomFIncorrectOutput :: Test
testRandomFIncorrectOutput = TestCase $ do
    imp <- impFDetIncorrectOutput
    let model = semanticsQuiescentInputAttemptConcrete sf
    (verdict, (observed, maybeMq)) <- runTester model testSelector imp
    let prev = last $ init observed
    assertEqual "testRandomFIncorrectOutput should fail" Fail verdict
    assertBool "incorrect number of observations " $ nrSteps >= length observed
    -- the only non-conformance is the output Y from Q2fd
    assertEqual "expected test failure on !Y" (Out $ TimeoutOut X) (last observed)
    -- the only observations leading to Q2fd are X and Y
    assertBool "expected observation before the test failure to be !X or !Y" $ (Out $ TimeoutOut X) == prev || (Out $ TimeoutOut Y) == prev
    assertEqual "final state should be definite" (Just True) (isConclusive <$> maybeMq)

tFDetIncorrectInput Q0fd = Map.fromList [(af, Q1fd), (x, Q0fd), (y, Q0fd)]
tFDetIncorrectInput Q1fd = Map.fromList [(af, Q1fd), (x, Q0fd), (y, Q2fd)]
tFDetIncorrectInput Q2fd = Map.fromList [(af, Q1fd), (y, Q2fd)] -- incorrect absence of a b-transition
impFDetIncorrectInput = pureAdapter (mkStdGen 123) 0.5 tFDetIncorrectInput Q0fd

testRandomFIncorrectInput :: Test
testRandomFIncorrectInput = TestCase $ do
    imp <- impFDetIncorrectInput
    let model = semanticsQuiescentInputAttemptConcrete sf
    (verdict, (observed, maybeMq)) <- runTester model testSelector imp
    let prev = last $ init observed
    assertEqual "testRandomFIncorrectInput should fail" Fail verdict
    assertBool "incorrect number of observations " $ nrSteps >= length observed
    -- the only non-conformance is the output Y from Q2fd
    assertEqual "expected test failure on ?A̅" (In $ Attempt (B, False)) (last observed)
    -- the only observation leading to Q2fd is Y
    assertBool "expected observation before the test failure to be !X or !Y" $ (Out $ TimeoutOut X) == prev || (Out $ TimeoutOut Y) == prev
    assertEqual "final state should be definite" (Just True) (isConclusive <$> maybeMq)
    



