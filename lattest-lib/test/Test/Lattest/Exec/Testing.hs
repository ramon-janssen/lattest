module Test.Lattest.Exec.Testing (
testTraceHappy,
testTraceFailsAtLastOutput,
testTraceFailsBeforeLastOutput,
testTraceIncompleteAtLastOutput,
testTraceIncompleteBeforeLastOutput,
testTraceFailsWithQuiescence,
testOutputOutsideAlphabet,
testOfflineTrace
)
where

import Lattest.Adapter.StandardAdapters(Adapter,pureMealyAdapter, pureAdapter)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, offlineTester, offlineTreeToTrace)
import Lattest.Model.Alphabet(IOAct(..), IOSuspAct, Suspended(..), SuspendedIF)
import Lattest.Model.Automaton(AutSyntax, automaton)
import Lattest.Model.BoundedMonad
import Lattest.Model.StandardAutomata(interpretQuiescentConcrete, ioAlphabet, interpretConcrete, interpretQuiescentInputAttemptConcrete, detConcTransFromRel)

import Data.Maybe (fromJust)
import System.Random(StdGen, mkStdGen)
import Test.HUnit hiding (Path, path)
import qualified Data.Map as Map (Map, insert, fromList)


testTraceHappy :: Test
testTraceHappy = TestCase $ do
    let t = [In 1, In 2, Out 3, In 4, Out 5, Out 6] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (interpretQuiescentConcrete $ traceSpecification t) (ioTraceTestController t) adap
    assertEqual "testTraceHappy should pass" verdict Pass
    assertEqual "testTraceHappy should be complete" finished True

testTraceFailsAtLastOutput :: Test
testTraceFailsAtLastOutput = TestCase $ do
    let t = [Out 1, Out 1, Out 2] :: [IOAct Integer Integer]
    let tspec = [Out 1, Out 2] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (interpretQuiescentConcrete $ traceSpecification tspec) (ioTraceTestController tspec) adap
    assertEqual "testTraceFailsAtLastOutput should fail" Fail verdict
    assertEqual "testTraceFailsAtLastOutput should be complete" True finished

testTraceFailsBeforeLastOutput :: Test
testTraceFailsBeforeLastOutput = TestCase $ do
    let t = [Out 1, Out 2] :: [IOAct Integer Integer]
    let tspec = [Out 2, Out 1] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (interpretQuiescentConcrete $ traceSpecification tspec) (ioTraceTestController tspec) adap
    assertEqual "testTraceFailsBeforeLastOutput should fail" Fail verdict
    assertEqual "testTraceFailsBeforeLastOutput should be incomplete" False finished

testTraceIncompleteAtLastOutput :: Test
testTraceIncompleteAtLastOutput = TestCase $ do
    let t = [Out 1, Out 2] :: [IOAct Integer Integer]
    let tController = [Out 1, Out 1] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (interpretQuiescentConcrete $ traceSpecification t) (ioTraceTestController tController) adap
    assertEqual "testTraceIncompleteAtLastOutput should pass" Pass verdict
    assertEqual "testTraceIncompleteAtLastOutput should be complete" True finished

testTraceIncompleteBeforeLastOutput :: Test
testTraceIncompleteBeforeLastOutput = TestCase $ do
    let t = [Out 1, Out 2] :: [IOAct Integer Integer]
    let tController = [Out 2, Out 2] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (interpretQuiescentConcrete $ traceSpecification t) (ioTraceTestController tController) adap
    assertEqual "testTraceIncompleteBeforeLastOutput should pass" Pass verdict
    assertEqual "testTraceIncompleteBeforeLastOutput should be incomplete" False finished

testTraceFailsWithQuiescence :: Test
testTraceFailsWithQuiescence = TestCase $ do
    let t = [Out 1, In 2] :: [IOAct Integer Integer]
    let tspec = [Out 1, Out 2] :: [IOAct Integer Integer]
    adap <- traceAdapter t
    (verdict, finished) <- runTester (interpretQuiescentConcrete $ traceSpecification tspec) (ioTraceTestController tspec) adap
    assertEqual "testTraceFailsWithQuiescence should fail" Fail verdict
    assertEqual "testTraceFailsWithQuiescence should be incomplete" True finished

ioTraceTestController :: (Eq i, Eq o) => [IOAct i o] -> TestController m loc q t tdest (IOSuspAct i o) [Either (Maybe i) (IOSuspAct i o)] (Maybe i) Bool
ioTraceTestController ioActs = traceTestController $ toCommandsAndActs ioActs
    where
    toCommandsAndActs [] = []
    toCommandsAndActs (In i:rest) = Left (Just i) : Right (In i) : toCommandsAndActs rest
    toCommandsAndActs (Out o:rest) = Right (Out $ OutSusp o) : toCommandsAndActs rest

-- a hardcoded test controller just follows the input commands and observations in the given list. Returns whether it finish the list
traceTestController :: (Eq act) => [Either (Maybe i) act] -> TestController m loc q t tdest act [Either (Maybe i) act] (Maybe i) Bool
traceTestController steps = TestController {
    -- testControllerState :: (TestChoice i act) => [Either i act]
    testControllerState = steps,
    --selectTest :: (TestChoice i act) => [Either i act] -> AutIntrpr m loc q t tdest act -> m q -> IO (Either (i, [Either i act]) Boolean),
    selectTest = traceSelectTest,
    --updateTestController :: [Either i act] -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (Either [Either i act] Boolean),
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

traceSpecification :: (Ord i, Ord o) => [IOAct i o] -> AutSyntax Det [IOAct i o] (IOAct i o) () -- TODO automata are inconsistent: no explicit alphabet, but an explicit transition map
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

testSelector :: TestController Det StateFDet StateFDet (IOAct IF OF) () (SuspendedIF IF OF) ((((StdGen, Int), [SuspendedIF IF OF]), Maybe (Det StateFDet)), Maybe (Det StateFDet)) (Maybe IF) (([SuspendedIF IF OF], Maybe (Det StateFDet)), Maybe (Det StateFDet))
testSelector = randomTestSelectorFromSeed 456 `untilCondition` stopAfterSteps 50
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver

data IF = A deriving (Show, Eq, Ord)
data OF = X | Y deriving (Show, Eq, Ord)
data StateFDet = Q0fd deriving (Show, Eq, Ord)
xf :: IOAct i OF
xf = Out X
yf :: IOAct i OF
yf = Out Y
af :: IOAct IF o
af = In A
q0f :: Det StateFDet
q0f = pure Q0fd
tWithX :: StateFDet -> Map.Map (IOAct IF OF) StateFDet
tWithX Q0fd = Map.fromList [(af, Q0fd), (xf, Q0fd)]
impWithX :: IO (Adapter (SuspendedIF IF OF) (Maybe IF))
impWithX = pureAdapter (mkStdGen 123) 0.0 tWithX Q0fd

menuWithY :: [IOAct IF OF]
menuWithY = [af, yf]
tWithY :: StateFDet -> Map.Map (IOAct IF OF) (Det ((), StateFDet))
tWithY = fromJust $ detConcTransFromRel [(Q0fd, af, Q0fd), (Q0fd, yf, Q0fd)]
specWithY :: AutSyntax Det StateFDet (IOAct IF OF) ()
specWithY = automaton q0f menuWithY tWithY

testOutputOutsideAlphabet :: Test
testOutputOutsideAlphabet = TestCase $ do
    imp <- impWithX
    let model = interpretQuiescentInputAttemptConcrete specWithY
    (verdict, ((_, _), _)) <- runTester model testSelector imp
    case verdict of
        Inconclusive _ -> return ()
        _ -> assertFailure $ "Output outside alphabet used, expected inconclusive verdict instead of " ++ show verdict


data StateOT = OTA | OTB | OTC | OTD | OTE | OTF | OTG
  deriving (Eq, Ord, Show)
testOfflineTrace :: Test
testOfflineTrace = TestCase $ do
  let alphOT = ioAlphabet [1 :: Int, 2] [1 :: Int, 2]
      transOT = fromJust $ detConcTransFromRel
        [ (OTA, In 1, OTB)
        , (OTB, Out 1, OTC)
        , (OTC, In 2, OTD)
        , (OTD, In 1, OTE)
        , (OTE, Out 2, OTF)
        , (OTF, Out 1, OTG)
        ]
      initialOT = pure OTA
      specOT = automaton initialOT alphOT transOT
      modelOT = interpretConcrete specOT
      testSelectorOT =
        randomTestSelectorFromSeed 123
  r <- offlineTester modelOT testSelectorOT Nothing
  let r2 = offlineTreeToTrace r
  assertEqual
    "trace through single-path automaton"
    (Just ([In 1, Out 1, In 2, In 1, Out 2, Out 1], (Pass, ())))
    r2

