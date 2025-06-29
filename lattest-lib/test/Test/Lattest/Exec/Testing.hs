module Test.Lattest.Exec.Testing (
testTraceHappy,
testTraceFailsAtLastOutput,
testTraceFailsBeforeLastOutput,
testTraceIncompleteAtLastOutput,
testTraceIncompleteBeforeLastOutput,
testTraceFailsWithQuiescence
)
where

import Test.HUnit hiding (Path, path)

import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, Verdict(Pass))
import Lattest.Model.Automaton(AutSyntax, automaton)
import Lattest.Model.StandardAutomata(semanticsQuiescentConcrete)
import Lattest.Model.Alphabet(IOAct(..), IOSuspAct, Suspended(..))
import Lattest.Model.StateConfiguration
import qualified Data.Map as Map (insert, fromList)
import Lattest.Adapter.StandardAdapters(Adapter,pureMealyAdapter,acceptingInputs)

testTraceHappy :: Test
testTraceHappy = TestCase $ do
    let t = [In 1, In 2, Out 3, In 4, Out 5, Out 6] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (semanticsQuiescentConcrete $ traceSpecification t) (ioTraceTestController t) adap
    assertEqual "testTraceHappy should pass" verdict Pass
    assertEqual "testTraceHappy should be complete" finished True

testTraceFailsAtLastOutput :: Test
testTraceFailsAtLastOutput = TestCase $ do
    let t = [Out 1, Out 1, Out 2] :: [IOAct Integer Integer]
    let tspec = [Out 1, Out 2] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (semanticsQuiescentConcrete $ traceSpecification tspec) (ioTraceTestController tspec) adap
    assertEqual "testTraceFailsAtLastOutput should fail" Fail verdict 
    assertEqual "testTraceFailsAtLastOutput should be complete" True finished

testTraceFailsBeforeLastOutput :: Test
testTraceFailsBeforeLastOutput = TestCase $ do
    let t = [Out 1, Out 2] :: [IOAct Integer Integer]
    let tspec = [Out 2, Out 1] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (semanticsQuiescentConcrete $ traceSpecification tspec) (ioTraceTestController tspec) adap
    assertEqual "testTraceFailsBeforeLastOutput should fail" Fail verdict
    assertEqual "testTraceFailsBeforeLastOutput should be incomplete" False finished

testTraceIncompleteAtLastOutput :: Test
testTraceIncompleteAtLastOutput = TestCase $ do
    let t = [Out 1, Out 2] :: [IOAct Integer Integer]
    let tController = [Out 1, Out 1] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (semanticsQuiescentConcrete $ traceSpecification t) (ioTraceTestController tController) adap
    assertEqual "testTraceIncompleteAtLastOutput should pass" Pass verdict 
    assertEqual "testTraceIncompleteAtLastOutput should be complete" True finished

testTraceIncompleteBeforeLastOutput :: Test
testTraceIncompleteBeforeLastOutput = TestCase $ do
    let t = [Out 1, Out 2] :: [IOAct Integer Integer]
    let tController = [Out 2, Out 2] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (semanticsQuiescentConcrete $ traceSpecification t) (ioTraceTestController tController) adap
    assertEqual "testTraceIncompleteBeforeLastOutput should pass" Pass verdict
    assertEqual "testTraceIncompleteBeforeLastOutput should be incomplete" False finished

testTraceFailsWithQuiescence :: Test
testTraceFailsWithQuiescence = TestCase $ do
    let t = [Out 1, In 2] :: [IOAct Integer Integer]
    let tspec = [Out 1, Out 2] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (semanticsQuiescentConcrete $ traceSpecification tspec) (ioTraceTestController tspec) adap
    assertEqual "testTraceFailsWithQuiescence should fail" Fail verdict
    assertEqual "testTraceFailsWithQuiescence should be incomplete" True finished

ioTraceTestController :: (Eq i, Eq o) => [IOAct i o] -> TestController m loc q t tloc (IOSuspAct i o) [Either (Maybe i) (IOSuspAct i o)] (Maybe i) Bool
ioTraceTestController ioActs = traceTestController $ toCommandsAndActs ioActs
    where
    toCommandsAndActs [] = []
    toCommandsAndActs (In i:rest) = Left (Just i) : Right (In i) : toCommandsAndActs rest
    toCommandsAndActs (Out o:rest) = Right (Out $ OutSusp o) : toCommandsAndActs rest

-- a hardcoded test controller just follows the input commands and observations in the given list. Returns whether it finish the list
traceTestController :: (Eq act) => [Either (Maybe i) act] -> TestController m loc q t tloc act [Either (Maybe i) act] (Maybe i) Bool
traceTestController steps = TestController {
    -- testControllerState :: (TestChoice i act) => [Either i act]
    testControllerState = steps,
    --selectTest :: (TestChoice i act) => [Either i act] -> AutSem m loc q t tloc act -> m q -> IO (Either (i, [Either i act]) Boolean),
    selectTest = traceSelectTest,
    --updateTestController :: [Either i act] -> AutSem m loc q t tloc act -> act -> m q -> IO (Either [Either i act] Boolean),
    updateTestController = traceUpdateTestController,
    --handleTestClose :: [Either i act] -> IO Boolean -- When testing finishes, return a result
    handleTestClose = return . null
    }
    where
    traceSelectTest [] _ _ = return $ Right True
    traceSelectTest (Left (Just i):steps') _ _ = return $ Left (Just i, steps')
    traceSelectTest (Right act:steps') _ _ = return $ Left (Nothing, (Right act:steps')) -- the test controller must choose input but it wanted to make an observation.
    traceSelectTest _ _ _ = error "should not happen"
    traceUpdateTestController [] _ _ _ = return $ Right True
    traceUpdateTestController (Left _:_) _ _ _ = return $ Right False -- test controller makes an observation but wanted to choose an input
    traceUpdateTestController (Right expectedAct:steps') _ act _ = return $ if expectedAct == act then Left steps' else Right (null steps')

traceSpecification :: (Ord i, Ord o) => [IOAct i o] -> AutSyntax DetState [IOAct i o] (IOAct i o) () -- TODO automata are inconsistent: no explicit alphabet, but an explicit transition map
traceSpecification steps = automaton (if null steps then UnderspecDet else Det steps) steps traceTransRel
    where
    traceTransRel (step:steps') = Map.insert step (Det ((), steps')) baseTransRel
    traceTransRel [] = baseTransRel
    baseTransRel = Map.fromList [(act, detStateFromAct act) | act <- steps]
    detStateFromAct (In _) = UnderspecDet
    detStateFromAct (Out _) = ForbiddenDet
{-
traceAdapter :: (Show i, Show o) => [IOAct i o] -> IO (Adapter (IOSuspAct i o) (Maybe i))
traceAdapter steps = pureAdapter traceTrans traceOutput $ if (null $ takeOutputs steps) then steps else error "traceAdapter cannot start with output"
    where
    -- invariant: before and in between transitions, the first step is always an input
    traceTrans steps' _ = snd (span isOutput steps') -- after the first input, drop all next outputs
    traceOutput steps' _ = takeOutputs steps' -- after the first input, take all next outputs
    takeOutputs steps' = fst (span isOutput steps')
-}
traceAdapter :: (Eq i) => [IOAct i o] -> IO (Adapter (IOSuspAct i o) (Maybe i))
traceAdapter steps = pureMealyAdapter traceTrans traceOutput steps
    where
    traceTrans [] _ = []
    traceTrans (In is:steps') (Just i) = if i == is then steps' else []
    traceTrans (In is:steps') Nothing = (In is:steps')
    traceTrans (Out _:steps') _ = steps' -- potential race condition between the (Just i) and the output. Let the adapter win to pester the tester
    traceOutput [] _ = [Out Quiescence] -- if the adapter is not processing any more actions, show timeouts. Even if an input is attempted, because it will not be processed
    traceOutput (In _:_) (Just i) = [In i]
    traceOutput (In _:_) Nothing = [Out Quiescence] -- the adapter is waiting for an input but doesn't receive one, so show a timeout.
    traceOutput (Out os:_) _ = [Out $ OutSusp os] -- potential race condition between the (Just i) and the output. Let the adapter win to pester the tester




