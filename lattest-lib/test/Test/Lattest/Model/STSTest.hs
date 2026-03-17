{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Test.Lattest.Model.STSTest (
    testSTSHappyFlow,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testSTSTestSelection,
    testSTSDisnjunction1
    )
where

import Prelude hiding (take)
import Test.HUnit
import Data.Maybe(fromJust)
import qualified Data.Set as Set
import System.Random(mkStdGen)

import qualified Lattest.Adapter.Adapter as Adapter
import Lattest.Adapter.StandardAdapters(pureAdapter)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(runTester,runSMTTester, Verdict(Pass))
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
            0 -> Map.fromList [(water,NonDet [(stsTLoc waterGuard waterAssign, 1)]),
                                (coffee,NonDet [(stsTLoc coffeeGuard noAssignment, 2)])]
            1 -> Map.fromList [(ok,NonDet [(stsTLoc okGuard noAssignment, 0)])]
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
testPrintSTS = TestCase $ do
    assertEqual "print of STS does not match " printSTS $ prettyPrintIntrp stsExampleIntrpr
    where
    {-
    current state configuration: [IntrpState 0 (fromList [(x:Int,0)])]
    initial location configuration: [0]
    locations: 0, 1, 2
    transitions:
    0 ――?"water" [p:Int]⟶ [([[(([(-1,1),(p:Int,1)]) > 0)∧(([(10,1),(p:Int,-1)]) > 0)]] {x:Int:=[(p:Int,1),(x:Int,1)]},1)]
    0 ――!"coffee" []⟶ [([[([(-15,1),(x:Int,1)]) > 0]] {},2)]
    0 ――!"ok" [p:Int]⟶ ⊥
    1 ――?"water" [p:Int]⟶ ⊤
    1 ――!"coffee" []⟶ ⊥
    1 ――!"ok" [p:Int]⟶ [([[(x:Int) = (p:Int)]] {},0)]
    2 ――?"water" [p:Int]⟶ ⊤
    2 ――!"coffee" []⟶ ⊥
    2 ――!"ok" [p:Int]⟶ ⊥
    -}
    printSTS = "current state configuration: [IntrpState 0 [\"(x:Int,0)\"]]\ninitial location configuration: [0]\nlocations: 0, 1, 2\ntransitions:\n0 \8213\8213?\"water\" [p:Int]\10230 [([[(([(p:Int,-1),(10,1)]) > 0)\8743(([(p:Int,1),(-1,1)]) > 0)]] {x:Int:=[(p:Int,1),(x:Int,1)]},1)]\n0 \8213\8213!\"coffee\" []\10230 [([[([(x:Int,1),(-15,1)]) > 0]] {},2)]\n0 \8213\8213!\"ok\" [p:Int]\10230 \8869\n1 \8213\8213?\"water\" [p:Int]\10230 \8868\n1 \8213\8213!\"coffee\" []\10230 \8869\n1 \8213\8213!\"ok\" [p:Int]\10230 [([[(x:Int) = (p:Int)]] {},0)]\n2 \8213\8213?\"water\" [p:Int]\10230 \8868\n2 \8213\8213!\"coffee\" []\10230 \8869\n2 \8213\8213!\"ok\" [p:Int]\10230 \8869"


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

{- stsFDL:
                        end(p,q)    
                       〚p+q=2x-6〛   
                     ╱——————>•      
    x:=0            ╱               
    ———>•—————————>•    end(p,q)    
         start(p)   ╲   〚p-q=x〛     
         〚9<p<11〛    ╲——————>•      
          x ≔ p                     
                                    
  parameterized by
  * whether start and end gates are input or output
  * the type of branching from the second state (conjunction or disjunction)
-}
stsFDL :: (String -> IOAct String String) -> (String -> IOAct String String) -> (forall a.FreeLattice a -> FreeLattice a -> FreeLattice a) -> IOSTS FreeLattice Integer String String
stsFDL startType endType comp =
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (startType "start") [pvar]
        end = SymInteract (endType "end") [pvar, qvar]
        initConf = pure 0 :: FreeLattice Integer
        switches = \s -> case s of
            0 -> Map.fromList [
                    (start, pure (stsTLoc (9 .< p .&& p .< 11) (assignment [xvar =: p]), 1))
                    ]
            1 -> Map.fromList [(end, pure (stsTLoc (p .+ q .== 2 .* x .- 6) noAssignment, 2) `comp` pure (stsTLoc (p .+ q .== x) noAssignment, 3))]
            2 -> Map.empty
            3 -> Map.empty
    in automaton initConf (Set.fromList [start, end]) switches
stsFDLInitAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)
stsFDLIntrpr = interpretSTS (stsFDL In Out (/\)) stsFDLInitAssign

t1 startType endType 0 = Map.fromList $ [((GateValue (startType "start") [Cint 10]), 1)]
t1 startType endType 1 = Map.fromList $ [((GateValue (endType "end") [Cint 4, Cint 6]), 2)]
t1 startType endType 2 = Map.fromList $ []
imp1 :: (String -> IOAct String String) -> (String -> IOAct String String) -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
imp1 startType endType = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> t1 startType endType) 0 :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
    Adapter.mapActionsFromSut toIOGateValue imp

testLatticeSTS :: (String -> IOAct String String) -> (String -> IOAct String String) -> (forall a.FreeLattice a -> FreeLattice a -> FreeLattice a) -> Integer -> Integer -> Integer -> ((String -> IOAct String String) -> (String -> IOAct String String) -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))) -> Test
testLatticeSTS startType endType comp p1 p2 q2 impIO = TestCase $ do
    let nrSteps = 3
        cfg = Config.changeLog Config.defaultConfig True 
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    info <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impIO startType endType
    (verdict, ((observed, maybeMq), maybePrvMq)) <- runSMTTester smtRef (interpretSTSQuiescentInputAttemptConcrete (stsFDL startType endType comp) stsExampleInitAssign) testSelector imp
    assertEqual ("expected pass after " ++ show observed) Pass verdict
    assertEqual "expected conformal trace" [
        inp "start" [Cint p1],
        out "end" [Cint q2, Cint p2],
        GateValue δ []
        ] observed
    where
    inp gate vals = GateValue (In (InputAttempt(gate, True))) vals
    out gate vals = GateValue (Out (OutSusp gate)) vals

testSTSDisnjunction1 = testLatticeSTS In Out (\/) 10 6 4 imp1


