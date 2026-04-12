{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}

module Test.Lattest.Model.STSTest (
    testSTSHappyFlow,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testSTSTestSelection,
    testLatticeSTS,
    testLatticeSTSQuiescence
    )
where

import Prelude hiding (take)
import Test.HUnit
import Data.Maybe(fromJust)
import qualified Data.Set as Set
import System.Random(mkStdGen)
import qualified Text.RawString.QQ as QQ

import qualified Lattest.Adapter.Adapter as Adapter
import Lattest.Adapter.StandardAdapters(pureAdapter)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(runTester,runSMTTester, Verdict(..))
import Lattest.Model.Automaton(after, afters, stateConf,automaton,interpret,IntrpState(..),Valuation,prettyPrintIntrp,stsTLoc, Valuation)
import Lattest.Model.StandardAutomata(interpretSTS, IOSTS, interpretSTSQuiescentInputAttemptConcrete)
import Lattest.Model.Alphabet(IOAct(..), isOutput, IOSuspAct, Suspended(..), SuspendedIF, SuspendedIFGateValue, asSuspended, δ, SymInteract(..),GateValue(..), ioActAsGateValue, gateValueAsIOAct,toIOGateValue, InputAttempt(..))
import Lattest.Model.BoundedMonad((/\), (\/), FreeLattice, atom, top, bot, NonDet(..),underspecified,forbidden)
import qualified Data.Map as Map
import qualified Control.Exception as Exception
import Lattest.Model.Symbolic.ValExpr.ValExpr
import qualified Lattest.SMT.Config as Config
import qualified Lattest.SMT.SMT as SMT

pvar = (Variable "p" IntType)
qvar = (Variable "q" IntType)
xvar = (Variable "x" IntType)
stsExampleInitAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)

stsExample :: IOSTS NonDet Integer String String
stsExample =
    let p = sVar pvar
        x = sVar xvar
        water = SymInteract (In "water") [pvar]
        ok = SymInteract (Out "ok") [pvar]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = NonDet [0] :: NonDet Integer
        switches = \q -> case q of
            0 -> Map.fromList [(water,NonDet $ Set.singleton (stsTLoc waterGuard waterAssign, 1)),
                                (coffee,NonDet $ Set.singleton (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok,NonDet $ Set.singleton (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches
stsExampleIntrpr = interpretSTS stsExample stsExampleInitAssign

getSTSIntrpState :: Integer ->  Integer -> NonDet (IntrpState Integer)
getSTSIntrpState loc val = NonDet [IntrpState loc $ fromConstantsMap $ Map.singleton (Variable "x" IntType) (Cint val)]

testSTSHappyFlow :: Test
testSTSHappyFlow = TestCase $ do

    assertEqual "\ninitial state " (getSTSIntrpState 0 0) (stateConf stsExampleIntrpr)
    let intrp2 = after stsExampleIntrpr (GateValue (In "water") [Cint 7])
    assertEqual "after water 7: " (getSTSIntrpState 1 7) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (Out "ok") [Cint 7])
    assertEqual "after ok 7: " (getSTSIntrpState 0 7) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (In "water") [Cint 9])
    assertEqual "after water 9: " (getSTSIntrpState 1 16) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (Out "ok") [Cint 16])
    assertEqual "after ok 16: " (getSTSIntrpState 0 16) (stateConf intrp5)
    let intrp6 = after intrp5 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpState 2 16) (stateConf intrp6)
    return()

testErrorThrowingGates :: Test
testErrorThrowingGates = TestCase $ do
    let intrp1 = after stsExampleIntrpr (GateValue (Out "water") [Cint 7])
    assertThrowsError "gate not in STS alphabet" (stateConf $ intrp1)
    let intrp2 = after stsExampleIntrpr (GateValue (In "water") [])
    assertThrowsError "nr of values unequal to nr of parameters" (stateConf $ intrp2)
    let intrp3 = after stsExampleIntrpr (GateValue (In "water") [Cbool True])
    assertThrowsError "type of variable and value do not match" (stateConf $ intrp3)

testSTSUnHappyFlow :: Test
testSTSUnHappyFlow = TestCase $ do
    let intrp3 = after stsExampleIntrpr (GateValue (Out "ok") [Cint 0]) -- output not enabled
    assertEqual "after ok: " forbidden (stateConf intrp3)
    let intrp4 = after stsExampleIntrpr (GateValue (In "water") [Cint 11]) -- value for input does not satisfy guard
    assertEqual "after water 11: " underspecified (stateConf intrp4)
    let intrp5 = after stsExampleIntrpr (GateValue (Out "coffee") []) -- value of variable does not satisfy guard
    assertEqual "after coffee: " forbidden (stateConf intrp5)

assertThrowsError :: String -> a -> IO ()
assertThrowsError expectedError someVal = do
    actualError <- Exception.handle handler $ do
        Exception.evaluate someVal
        return Nothing -- no exception thrown, so no error message
    assertEqual "expected error: " (Just expectedError) actualError
    where
        handler :: Exception.ErrorCall -> IO (Maybe String)
        handler ex = return $ Just $ show ex

testPrintSTS :: Test
testPrintSTS = TestCase $ assertBool failureMessage (expected == actual) -- no assertEquals to avoid printing the unreadable ascii-escaped variant of the tested unicode strings
    where
    failureMessage = "print of STS does not match, expected:" ++ expected ++ "but received:" ++ actual
    actual = "\n" ++ prettyPrintIntrp stsExampleIntrpr ++ "\n" -- newlines before and after to match those of the "expected" below.
    -- fancy quasiquotes to allow direct copy-pasting of the printed expected string into the source code below. With newline at start and end for readability.
    expected = [QQ.r|
current state configuration: [(0,{x:=0})]
initial location configuration: [0]
locations: 0, 1, 2
transitions:
0  ――?"water" [p:Int]⟶  [((((-p+10)) ≥ 0)∧(((p+-1)) ≥ 0), {x:=(p+x)},1)]
0  ――!"coffee" []⟶  [(((x+-15)) ≥ 0, {},2)]
0  ――!"ok" [p:Int]⟶  ⊥
1  ――?"water" [p:Int]⟶  ⊤
1  ――!"coffee" []⟶  ⊥
1  ――!"ok" [p:Int]⟶  [((x) = (p), {},0)]
2  ――?"water" [p:Int]⟶  ⊤
2  ――!"coffee" []⟶  ⊥
2  ――!"ok" [p:Int]⟶  ⊥
|]

data ImpExampleLoc = L0 | L1 | L2 deriving (Eq, Ord, Show)

-- TODO the "x" here is not implemented properly, it should be something like "xvar = (Variable "x" IntType)", see the example at the top of this file
tExampleCorrect (L0, x) = Map.fromList $
    [((GateValue (In "water") [Cint p]), (L1, x+p)) | p <- [1..10]] ++ [((GateValue (Out "coffee") []), (L2, 0)) | x > 15]
tExampleCorrect (L1, x) = Map.fromList $ [((GateValue (Out "ok") [Cint x]), (L0, x))]
tExampleCorrect (L2, _) = Map.fromList $ []
impExampleCorrect :: IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
impExampleCorrect = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> tExampleCorrect) (L0, 0) :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
    Adapter.mapActionsFromSut toIOGateValue imp

testSTSTestSelection :: Test
testSTSTestSelection = TestCase $ do
    let nrSteps = 37
        cfg = Config.changeLog Config.defaultConfig False 
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.05 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impExampleCorrect
    let initAssign = Map.singleton (Variable "x" IntType) (Cint 0)
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef (interpretSTSQuiescentInputAttemptConcrete stsExample stsExampleInitAssign) testSelector imp
    assertEqual "expected conformal trace" [-- FIXME this test case assumes the SMT solver to return 1, but any solution in (1,10) is correct
        inp "water" [Cint 1],
        out "ok" [Cint 1],
        inp "water" [Cint 1],
        out "ok" [Cint 2],
        GateValue δ [],
        inp "water" [Cint 1],
        out "ok" [Cint 3],
        inp "water" [Cint 1],
        out "ok" [Cint 4],
        inp "water" [Cint 1],
        out "ok" [Cint 5],
        GateValue δ [],
        inp "water" [Cint 1],
        out "ok" [Cint 6],
        inp "water" [Cint 1],
        out "ok" [Cint 7],
        inp "water" [Cint 1],
        out "ok" [Cint 8],
        inp "water" [Cint 1],
        out "ok" [Cint 9],
        inp "water" [Cint 1],
        out "ok" [Cint 10],
        inp "water" [Cint 1],
        out "ok" [Cint 11],
        inp "water" [Cint 1],
        out "ok" [Cint 12],
        inp "water" [Cint 1],
        out "ok" [Cint 13],
        inp "water" [Cint 1],
        out "ok" [Cint 14],
        inp "water" [Cint 1],
        out "ok" [Cint 15],
        inp "water" [Cint 1],
        out "ok" [Cint 16],
        out "coffee" [],
        GateValue δ [],
        GateValue δ []
        ] observed
    assertEqual "expected pass " Pass verdict
    where
    inp gate vals = GateValue (In (InputAttempt(gate, True))) vals
    out gate vals = GateValue (Out (OutSusp gate)) vals

{- specification:
                        end(p,q)    
                       〚p+q=x+2〛   
                     ╱——————>•————\
    x:=0            ╱              \
    ———>•—————————>•    end(p,q)    ———>•
         start(p)   ╲   〚p-q=x〛    /!done
         〚1<p<3〛     ╲——————>•————/
          x ≔ p                 
                                    
  parameterized by
  * whether start and end gates are input or output
  * the type of branching from the second state (conjunction or disjunction)
  * whether to split the second state into two, where the branching occurs on the first transition (with equal guards) instead of the second
-}
specParameterized :: (String -> IOAct String String) -> (String -> IOAct String String) -> (forall a.FreeLattice a -> FreeLattice a -> FreeLattice a) -> Bool -> IOSTS FreeLattice Integer String String
specParameterized startType endType comp splitFirst =
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (startType "start") [pvar]
        end = SymInteract (endType "end") [pvar, qvar]
        done = SymInteract (Out "done") []
        initConf = pure 0 :: FreeLattice Integer
        guardStart = 1 .< p .&& p .< 3
        guardEnd1 = p .+ q .== x .+ 2
        guardEnd2 = p .- q .== x
        assignX = assignment [xvar =: p]
        switches =
            if splitFirst
                then \s -> case s of
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1) `comp` pure (stsTLoc guardStart assignX, 2))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd1 noAssignment, 3))]
                        2 -> Map.fromList [(end, pure (stsTLoc guardEnd2 noAssignment, 4))]
                        3 -> Map.fromList [(done, pure (stsTLoc sTrue noAssignment, 5))]
                        4 -> Map.fromList [(done, pure (stsTLoc sTrue noAssignment, 5))]
                        5 -> Map.empty
                else \s -> case s of
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd1 noAssignment, 2) `comp` pure (stsTLoc guardEnd2 noAssignment, 3))]
                        2 -> Map.fromList [(done, pure (stsTLoc sTrue noAssignment, 4))]
                        3 -> Map.fromList [(done, pure (stsTLoc sTrue noAssignment, 4))]
                        4 -> Map.empty
    in automaton initConf (Set.fromList [start, end, done]) switches

{- implementation:
          start(p)   end(p,q)    !done
    ———>•—————————>•—————————>•—————————>•
  parameterized by
  * whether start and end gates are input or output
  * p and q (note, this means that only s specific, single concrete transition start(p) and single concrete transition end(p,q) is defined)
-}
t1 startType endType p1 p2 q2 0 = Map.fromList $ [((GateValue (startType "start") [Cint p1]), 1)]
t1 startType endType p1 p2 q2 1 = Map.fromList $ [((GateValue (endType "end") [Cint p2, Cint q2]), 2)]
t1 startType endType p1 p2 q2 2 = Map.fromList $ [((GateValue (Out "done") []), 3)]
t1 startType endType p1 p2 q2 3 = Map.fromList $ []
impParameterized :: (String -> IOAct String String) -> (String -> IOAct String String) -> Integer -> Integer -> Integer -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
impParameterized startType endType p1 p2 q2 = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> t1 startType endType p1 p2 q2) 0 :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
    Adapter.mapActionsFromSut toIOGateValue imp

testLatticeSTSParameterized' :: String -> Bool -> (forall a.FreeLattice a -> FreeLattice a -> FreeLattice a) -> Bool -> Integer -> Integer -> Integer -> Maybe [SuspendedIFGateValue String String] -> Test
testLatticeSTSParameterized' testName inputThenOut comp splitFirst p1 p2 q2 expectedNonConformalTrace = TestCase $ do
    let (startType, endType, startType', endType') =
            if inputThenOut
                then (In, Out, inp, out)
                else (Out, In, out, inp)
    let nrSteps = 4
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impParameterized startType endType p1 p2 q2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specParameterized startType endType comp splitFirst) stsExampleInitAssign
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef specIntrpr testSelector imp
    
    case expectedNonConformalTrace of
        Nothing -> do
            assertEqual (testName ++ ": expected Pass after " ++ show observed) Pass verdict
            assertEqual (testName ++ ": expected conformal trace") [
                startType' "start" [Cint p1],
                endType' "end" [Cint p2, Cint q2],
                out "done" [],
                GateValue δ []
                ] observed
        Just t -> do
            assertEqual (testName ++ ": expected Fail after " ++ show observed) Fail verdict
            assertEqual (testName ++ ": expected nonconformal trace") t observed
inp gate vals = GateValue (In (InputAttempt(gate, True))) vals
inpf gate vals = GateValue (In (InputAttempt(gate, False))) vals
out gate vals = GateValue (Out (OutSusp gate)) vals

testLatticeSTSParameterized :: String -> Bool -> (forall a.FreeLattice a -> FreeLattice a -> FreeLattice a) -> Integer -> Integer -> Integer -> Maybe [SuspendedIFGateValue String String] -> [Test]
testLatticeSTSParameterized testName inputThenOut comp p1 p2 q2 expectedNonConformalTrace = [
    testLatticeSTSParameterized' testName inputThenOut comp False p1 p2 q2 expectedNonConformalTrace,
    testLatticeSTSParameterized' (testName ++ "'") inputThenOut comp True p1 p2 q2 expectedNonConformalTrace
    ]

testLatticeSTS :: [Test]
testLatticeSTS = concat [
    -- TODO add some cases for quiescence, immediate wrong input failure values, etc.
    testLatticeSTSParameterized "a1" inputThenOutput (\/) 2 2 2 Nothing, -- pass: output (2,2) satisfies the first guard
    testLatticeSTSParameterized "a2" inputThenOutput (\/) 2 4 2 Nothing, -- pass: output (4,2) satisfies the second guard
    testLatticeSTSParameterized "a3" inputThenOutput (\/) 2 3 1 Nothing, -- pass: output (3,1) satisfies both guards
    testLatticeSTSParameterized "a4" inputThenOutput (\/) 2 4 4 (Just [inp "start" [Cint 2], out "end" [Cint 4, Cint 4]]), -- fail: output (4,4) satisfies neither guard
    testLatticeSTSParameterized "a5" inputThenOutput (/\) 2 2 2 (Just [inp "start" [Cint 2], out "end" [Cint 2, Cint 2]]), -- fail: output (2,2) satisfies the first guards, but not both
    testLatticeSTSParameterized "a6" inputThenOutput (/\) 2 4 2 (Just [inp "start" [Cint 2], out "end" [Cint 4, Cint 2]]), -- fail: output (4,2) satisfies the second guards, but not both
    testLatticeSTSParameterized "a7" inputThenOutput (/\) 2 4 4 (Just [inp "start" [Cint 2], out "end" [Cint 4, Cint 4]]), -- fail: output (4,4) satisfies neither guard
    testLatticeSTSParameterized "a8" inputThenOutput (/\) 2 3 1 Nothing, -- pass: output (3,1) satisfies both guards

    testLatticeSTSParameterized "b1" outputThenInput (\/) 2 3 1 Nothing, -- pass: (3,1) is the only input that matches both guards, so is the only specified input overall, thus will be tested and observed
    testLatticeSTSParameterized "b2" outputThenInput (\/) 2 5 5 (Just [out "start" [Cint 2], inpf "end" [Cint 3, Cint 1]]) -- pass: (3,1) is the only input that matches both guards, so is the only specified input overall, thus will be tested but refused
     -- FIXME the next tests are actually unsound: it will pass under the assumption that the test selection (SMT solver) will pick the last two number parameters as input,
     -- but if not, the test case will incorrectly fail. To fix this, change the implementation to accept any (p,q) satisfying any of the guards 〚p+q=4〛 or 〚p-q=2〛
    --testLatticeSTSParameterized "b3" outputThenInput (/\) 2 0 (-2) Nothing, -- pass: (0,-2) is an input that matches one of the guards, so is specified, thus may be tested and in that case will be observed
    --testLatticeSTSParameterized "b4" outputThenInput (/\) 2 5 5 (Just [out "start" [Cint 2], inpf "end" [Cint 0, Cint (-2)]]) -- fail: the tester will pick an input that matches one of the guards, but will be rejected by the implementation
    ]
    where
    inputThenOutput = True
    outputThenInput = False

 {- specification:

    x:=0                               
    ———>•—————————>•———————————>•      
        ?start(p)    !end(p,q)         
         〚1<p<3〛    〚p+q=p+q+x〛        
          x ≔ p                        
                                       
    note, the guard of the second transition is not satisfiable so the second state is quiescent
-}
specQ :: IOSTS FreeLattice Integer String String
specQ =
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (In "start") [pvar]
        end = SymInteract (Out "end") [pvar, qvar]
        initConf = pure 0 :: FreeLattice Integer
        guardStart = 1 .< p .&& p .< 3
        guardEnd = p .+ q .== p .+ q .+ x
        assignX = assignment [xvar =: p]
        switches = \s -> case s of
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd noAssignment, 2))]
                        2 -> Map.empty
    in automaton initConf (Set.fromList [start, end]) switches

{- implementation:
          start(p)
    ———>•—————————>•
  parameterized by
  * whether start gate is input or output
  * p
-}
tq startType p 0 = Map.fromList $ [((GateValue (startType "start") [Cint p]), 1)]
tq startType p 1 = Map.fromList $ []
impQParameterized :: (String -> IOAct String String) -> Integer -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
impQParameterized startType p = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> tq startType p) 0 :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
    Adapter.mapActionsFromSut toIOGateValue imp

testLatticeSTSQuiescentPass :: String -> Bool -> Test
testLatticeSTSQuiescentPass testName splitFirst = TestCase $ do
    let nrSteps = 2
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete specQ stsExampleInitAssign
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef specIntrpr testSelector imp
    
    assertEqual (testName ++ ": expected Pass after " ++ show observed) Pass verdict
    assertEqual (testName ++ ": expected conformal trace") [
                inp "start" [Cint 2],
                GateValue δ []
                ] observed

testLatticeSTSQuiescentFail1 :: String -> Bool -> Test
testLatticeSTSQuiescentFail1 testName splitFirst = TestCase $ do
    let nrSteps = 2
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specParameterized In Out (\/) splitFirst) stsExampleInitAssign
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef specIntrpr testSelector imp
    
    assertEqual (testName ++ ": expected Pass after " ++ show observed) Fail verdict
    assertEqual (testName ++ ": expected nonconformal trace") [
                inp "start" [Cint 2],
                GateValue δ []
                ] observed

testLatticeSTSQuiescentFail2 :: String -> Bool -> Test
testLatticeSTSQuiescentFail2 testName splitFirst = TestCase $ do
    let nrSteps = 2
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impParameterized In Out 2 42 42
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete specQ stsExampleInitAssign
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef specIntrpr testSelector imp
    
    assertEqual (testName ++ ": expected Pass after " ++ show observed) Fail verdict
    assertEqual (testName ++ ": expected nonconformal trace") [
                inp "start" [Cint 2],
                out "end" [Cint 42, Cint 42]
                ] observed


 {- specification:
                       !end(p,q) 
                       〚p+q=x+2〛       
                     ╱——————————\      
    x:=0            ╱            \     
    ———>•—————————>• ) !end(p,q)  ———>•
        ?start(p)   ╲   〚p+q=x〛  /     
         〚1<p<3〛     ╲——————————/      
          x ≔ p                        
                                       
  parameterized by whether to split the second state into two, where the branching occurs on the first transition (with equal guards) instead of the second
-}
specUnimplementableParameterized :: Bool -> IOSTS FreeLattice Integer String String
specUnimplementableParameterized splitFirst =
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (In "start") [pvar]
        end = SymInteract (Out "end") [pvar, qvar]
        initConf = pure 0 :: FreeLattice Integer
        guardStart = 1 .< p .&& p .< 3
        guardEnd1 = p .+ q .== x .+ 2
        guardEnd2 = p .+ q .== x
        assignX = assignment [xvar =: p]
        switches =
            if splitFirst
                then \s -> case s of
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1) /\ pure (stsTLoc guardStart assignX, 2))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd1 noAssignment, 3))]
                        2 -> Map.fromList [(end, pure (stsTLoc guardEnd2 noAssignment, 3))]
                        3 -> Map.empty
                else \s -> case s of
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd1 noAssignment, 2) /\ pure (stsTLoc guardEnd2 noAssignment, 3))]
                        2 -> Map.empty
                        3 -> Map.empty
    in automaton initConf (Set.fromList [start, end]) switches

testLatticeSTSUnimplementable :: String -> Bool -> Test
testLatticeSTSUnimplementable testName splitFirst = TestCase $ do
    let nrSteps = 2
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specUnimplementableParameterized splitFirst) stsExampleInitAssign
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef specIntrpr testSelector imp
    
    assertEqual (testName ++ ": expected Fail after " ++ show observed) Fail verdict
    assertEqual (testName ++ ": expected nonconformal trace") [
                inp "start" [Cint 2],
                GateValue δ []
                ] observed

testLatticeSTSQuiescence :: [Test]
testLatticeSTSQuiescence = [
    testLatticeSTSQuiescentPass "q1" True, -- a quiescent implementation and STS will lead to a pass
    testLatticeSTSQuiescentPass "q2'" False, -- a quiescent implementation and STS will lead to a pass
    testLatticeSTSQuiescentFail1 "q3" True, -- a quiescent implementation will fail against a non-quiescent specification
    testLatticeSTSQuiescentFail1 "q4" False, -- a quiescent implementation will fail against a non-quiescent specification
    testLatticeSTSQuiescentFail2 "q3" True, -- a non-quiescent implementation will fail against a quiescent specification
    testLatticeSTSQuiescentFail2 "q4" False, -- a non-quiescent implementation will fail against a quiescent specification
    testLatticeSTSUnimplementable "u1" True, -- an unimplementable specification (two conjunctive conditions contradicting eachother) is not implemented by a quiescent implementation
    testLatticeSTSUnimplementable "u2'" False -- an unimplementable specification (two conjunctive conditions contradicting eachother) is not implemented by a quiescent implementation
    ]
