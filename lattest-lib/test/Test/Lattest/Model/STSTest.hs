{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Test.Lattest.Model.STSTest (
    testSTSHappyFlow,
    testSTSHappyFlowFloat,
    testLatticeCoffeeSTS,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testSTSTestSelection,
    testLatticeSTS,
    testLatticeSTSQuiescence,
    testSTSPathCondition,
    testBranchingPathCondition,
    testLinearCoffeeTreeStructure,
    testComplexTreeStructure,
    testComposedCoffeeTreeStructure,
    testConcreteTraceSpecifiedAllowedCorrespondence,
    prop_specifiedAllowedCorrespondence,
    composedCoffeeMachineIntrpr,
    testPrintSeqCompSTS,
    testSeqComposedSTS,
    testSeqComposedAtSTS,
    testSequentiallyAtNonSinkLocation,
    testSequentiallyAtSameAction,
    testPrintSelfSeqComposedSTS,
    testSelfSeqComposed,
    testSelfSeqComposedAt,
    testSelfSeqComposedAtOne
    )
where

import Prelude hiding (take)
import Test.HUnit
import Test.QuickCheck (Gen, Property, forAll, elements, choose, vectorOf, counterexample, (.&&.))
import Data.Maybe(fromJust, isJust, catMaybes)
import qualified Data.Set as Set
import System.Random(mkStdGen)
import Data.String(IsString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import System.FilePath ((</>), takeDirectory)
import System.Directory (createDirectoryIfMissing)
import qualified Text.RawString.QQ as QQ
import qualified Lattest.Adapter.Adapter as Adapter
import Lattest.Adapter.StandardAdapters(pureAdapter)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(runSMTTester, Verdict(..))
import Lattest.Model.Automaton(after, stateConf,automaton,IntrpState(..),prettyPrintIntrp,stsTLoc,STStdest,alphabet,syntacticAutomaton)
import Lattest.Model.StandardAutomata(interpretSTS, IOSTS, STSIntrp, interpretSTSQuiescentInputAttemptConcrete, sequentiallyAt, (|>), selfSequentiallyAt, (|>>))
import Lattest.Model.Alphabet(IOAct(..), Suspended(..), SuspendedIF, SuspendedIFGateValue, δ, SymInteract(..),GateValue(..), gateValueAsIOAct,toIOGateValue, InputAttempt(..), SymGuard, IOSymInteract)
import Lattest.Model.BoundedMonad(Det, BoundedMonad, BooleanConfiguration, (/\), (\/), underspecified, forbidden, FreeLattice, atom, disjunction, isSpecified, isAllowed, specifiedness, Specifiedness(..), ordReturn, (<#>))
import Reference.FreeLatticeSlow(FreeLatticeSlow(..))
import Algebra.Lattice.Free(Free(..))
import Algebra.Lattice.Levitated(Levitated(..))
import Lattest.Model.Symbolic.SolveSTS(interactsToSpecifiedCondition, interactsToAllowedCondition)
import qualified Lattest.Model.Symbolic.SolveSTS as Solve
import Lattest.Model.Symbolic.SolveSymPrim(solveGuard)
import qualified Data.Map as Map
import qualified Control.Exception as Exception
import Lattest.Model.Symbolic.Expr hiding (Var) -- 'Var' would clash with 'Algebra.Lattice.Free.Var' used by prettySeTree
import qualified Lattest.SMT as SMT

pvar :: Variable
pvar = (Variable "p" IntType)
qvar :: Variable
qvar = (Variable "q" IntType)
xvar :: Variable
xvar = (Variable "x" IntType)
stsExampleInitAssign :: Valuation
stsExampleInitAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)

stsExample :: IOSTS Det Integer String String
stsExample =
    let p = sVar pvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        water = SymInteract (In "water") [pvar]
        ok = SymInteract (Out "ok") [pvar]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = return 0
        switches = \q -> case q of
            0 -> Map.fromList [(water, pure (stsTLoc waterGuard waterAssign, 1)),
                                (coffee, pure (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, pure (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches
stsExampleIntrpr :: STSIntrp Det Integer (IOAct String String)
stsExampleIntrpr = interpretSTS stsExample stsExampleInitAssign

getSTSIntrpState :: Integer ->  Integer -> Det (IntrpState Integer)
getSTSIntrpState loc val = pure $ IntrpState loc $ fromConstantsMap $ Map.singleton (Variable "x" IntType) (Cint val)

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
    return ()

testErrorThrowingGates :: Test
testErrorThrowingGates = TestCase $ do
    let intrp1 = after stsExampleIntrpr (GateValue (Out "water") [Cint 7])
    assertThrowsError "gate not in STS alphabet" (stateConf intrp1)
    let intrp2 = after stsExampleIntrpr (GateValue (In "water") [])
    assertThrowsError "nr of values unequal to nr of parameters: 0 values and 1 variables" (stateConf intrp2)
    let intrp3 = after stsExampleIntrpr (GateValue (In "water") [Cbool True])
    assertThrowsError "type of variable and value do not match. Variables: [p:Int], Values: [True]" (stateConf intrp3)

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
        _ <- Exception.evaluate someVal
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
current state configuration: (0,{x:=0})
initial location configuration: 0
locations: 0, 1, 2
transitions:
0  ――?"water" [p:Int]⟶  ((((-p+10)) ≥ 0)∧(((p+-1)) ≥ 0), {x:=(p+x)},1)
0  ――!"coffee" []⟶  (((x+-15)) ≥ 0, {},2)
0  ――!"ok" [p:Int]⟶  -forbidden-
1  ――?"water" [p:Int]⟶  -underspecified-
1  ――!"coffee" []⟶  -forbidden-
1  ――!"ok" [p:Int]⟶  ((x) = (p), {},0)
2  ――?"water" [p:Int]⟶  -underspecified-
2  ――!"coffee" []⟶  -forbidden-
2  ――!"ok" [p:Int]⟶  -forbidden-
|]

data ImpExampleLoc = L0 | L1 | L2 deriving (Eq, Ord, Show)

-- TODO the "x" here is not implemented properly, it should be something like "xvar = (Variable "x" IntType)", see the example at the top of this file
tExampleCorrect :: (Ord i, Ord o, IsString i, IsString o) => (ImpExampleLoc, Integer) -> Map.Map (GateValue (IOAct i o)) (ImpExampleLoc, Integer)
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

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed 456 0.05 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impExampleCorrect
    (verdict, ((observed, _), _)) <- runSMTTester (interpretSTSQuiescentInputAttemptConcrete stsExample stsExampleInitAssign) testSelector imp
    let checkObserved = go 0 0 observed
    let exampleObserved = [
          inp "water" [Cint 1],
          out "ok" [Cint 1],
          inp "water" [Cint 1],
          out "ok" [Cint 2],
          GateValue δ [],
          inp "water" [Cint 1],
          out "ok" [Cint 3],
          inp "water" [Cint 1],
          outL "ok" [Cint 4],
          inpL "water" [Cint 1],
          outL "ok" [Cint 5],
          GateValue δ [],
          inpL "water" [Cint 1],
          outL "ok" [Cint 6],
          inpL "water" [Cint 1],
          outL "ok" [Cint 7],
          inpL "water" [Cint 1],
          outL "ok" [Cint 8],
          inpL "water" [Cint 1],
          outL "ok" [Cint 9],
          inpL "water" [Cint 1],
          outL "ok" [Cint 10],
          inpL "water" [Cint 1],
          outL "ok" [Cint 11],
          inpL "water" [Cint 1],
          outL "ok" [Cint 12],
          inpL "water" [Cint 1],
          outL "ok" [Cint 13],
          inpL "water" [Cint 1],
          outL "ok" [Cint 14],
          inpL "water" [Cint 1],
          outL "ok" [Cint 15],
          inpL "water" [Cint 1],
          outL "ok" [Cint 16],
          outL "coffee" [],
          GateValue δ [],
          GateValue δ []
          ]
    let checkExample = go 0 0 exampleObserved
    assertEqual ("expected conformal trace like " <> show exampleObserved <> ", got " <> show observed) checkObserved checkExample
    assertEqual "expected pass " Pass verdict
    where
    inpL g vals = GateValue (In (InputAttempt (g, True))) vals
    outL g vals = GateValue (Out (OutSusp g)) vals
    go ds waterlevel [] = (ds, waterlevel)
    go ds waterlevel (GateValue (Out Quiescence) []:os) = go (ds+1) waterlevel os
    go ds waterlevel gv@(GateValue x y:os)
      | x == In (InputAttempt ("water", True))
      , [Cint w] <- y = go ds (waterlevel+w) os
      | x == Out (OutSusp "ok")
      , [Cint w] <- y
      , w == waterlevel = go ds waterlevel os
      | x == Out (OutSusp "coffee")
      , [] <- y
      , waterlevel > 15 = go ds waterlevel os
      | otherwise = error $ "wrong gatevalue: " <> show gv

pvarf :: Variable
pvarf = (Variable "p" FloatType)
xvarf :: Variable
xvarf = (Variable "x" FloatType)

stsExampleInitAssignFloat :: Valuation
stsExampleInitAssignFloat = fromConstantsMap $ Map.singleton xvarf (Cfloat (0.0 :: Double))

stsExampleFloat :: IOSTS FreeLattice Integer String String
stsExampleFloat =
    let p = sVar pvarf :: Expr Double
        x = sVar xvarf :: Expr Double
        water = SymInteract (In "water") [pvarf]
        ok = SymInteract (Out "ok") [pvarf]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvarf =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= sConst (14.5 :: Double)
        initConf = disjunction [0] :: FreeLattice Integer
        switches = \case
            0 -> Map.fromList [(water,   disjunction [(stsTLoc waterGuard waterAssign, 1)]),
                                (coffee, disjunction [(stsTLoc coffeeGuard noAssignment, 2)])]
            1 -> Map.fromList [(ok,      disjunction [(stsTLoc okGuard noAssignment, 0)])]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches
stsExampleIntrprFloat :: STSIntrp FreeLattice Integer (IOAct String String)
stsExampleIntrprFloat = interpretSTS stsExampleFloat stsExampleInitAssignFloat

getSTSIntrpStateFloat :: Integer -> Double -> FreeLattice (IntrpState Integer)
getSTSIntrpStateFloat loc val = disjunction [IntrpState loc $ fromConstantsMap $ Map.singleton (Variable "x" FloatType) (Cfloat val)]

testSTSHappyFlowFloat :: Test
testSTSHappyFlowFloat = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpStateFloat 0 0.0) (stateConf stsExampleIntrprFloat)
    let intrp2 = after stsExampleIntrprFloat (GateValue (In "water") [Cfloat (7.5 :: Double)])
    assertEqual "after water 7.5: " (getSTSIntrpStateFloat 1 (7.5 :: Double)) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (Out "ok") [Cfloat 7.5])
    assertEqual "after ok 7.5: " (getSTSIntrpStateFloat 0 (7.5 :: Double)) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (In "water") [Cfloat 8.5])
    assertEqual "after water 8.5: " (getSTSIntrpStateFloat 1 (16.0 :: Double)) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (Out "ok") [Cfloat 16.0])
    assertEqual "after ok 16.0: " (getSTSIntrpStateFloat 0 (16.0 :: Double)) (stateConf intrp5)
    let intrp6 = after intrp5 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpStateFloat 2 (16.0 :: Double)) (stateConf intrp6)
    return ()


stsExample2 :: (IOSTS FreeLattice Integer String String, IOSTS FreeLattice Integer String String)
stsExample2 =
    let p = sVar pvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        water = SymInteract (In "water") [pvar]
        ok = SymInteract (Out "ok") [pvar]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 4
        waterGuard1 = 4 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = atom 0
        switches = \q -> case q of
            0 -> Map.fromList [(water, atom (stsTLoc waterGuard waterAssign, 1) /\ atom (stsTLoc waterGuard1 waterAssign, 2) )]
            1 -> Map.fromList [(ok, atom (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.fromList [(ok, atom (stsTLoc okGuard noAssignment, 0))]
        initConf2 = atom 0 /\ atom 2
        switches2 = \q -> case q of
            0 -> Map.fromList [(water, atom (stsTLoc waterGuard waterAssign, 1))]
            1 -> Map.fromList [(ok, atom (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.fromList [(water, atom (stsTLoc waterGuard1 waterAssign, 3))]
            3 -> Map.fromList [(ok, atom (stsTLoc okGuard noAssignment, 2))]
    in (automaton initConf (Set.fromList [water,ok,coffee]) switches, automaton initConf2 (Set.fromList [water,ok,coffee]) switches2)

stsExampleIntrpr2a :: STSIntrp FreeLattice Integer (IOAct String String)
stsExampleIntrpr2a = interpretSTS (fst stsExample2) stsExampleInitAssign

stsExampleIntrpr2b :: STSIntrp FreeLattice Integer (IOAct String String)
stsExampleIntrpr2b = interpretSTS (snd stsExample2) stsExampleInitAssign

getSTSValuation :: Integer -> Valuation
getSTSValuation val = fromConstantsMap $ Map.singleton (Variable "x" IntType) (Cint val)

getSTSIntrpState2 :: Integer ->  Integer -> FreeLattice (IntrpState Integer)
getSTSIntrpState2 loc val = atom (IntrpState loc $ getSTSValuation val)

testLatticeCoffeeSTS :: Test
testLatticeCoffeeSTS = TestCase $ do
     assertEqual "\ninitial state " (getSTSIntrpState2 0 0) (stateConf stsExampleIntrpr2a)
     assertEqual "\ninitial state " (getSTSIntrpState2 0 0 /\ getSTSIntrpState2 2 0) (stateConf stsExampleIntrpr2b)
     let intrp2a = after stsExampleIntrpr2a (GateValue (In "water") [Cint 3])
     assertEqual "2a after water 3: " (getSTSIntrpState2 1 3) (stateConf intrp2a)
     let intrp2b = after stsExampleIntrpr2b (GateValue (In "water") [Cint 3])
     assertEqual "2b after water 3: " (getSTSIntrpState2 1 3) (stateConf intrp2b)
     let intrp3a = after intrp2a (GateValue (Out "ok") [Cint 3])
     assertEqual "2a after ok 3: " (getSTSIntrpState2 0 3) (stateConf intrp3a)
     let intrp3b = after intrp2b (GateValue (Out "ok") [Cint 3])
     assertEqual "2b after ok 3: " (getSTSIntrpState2 0 3) (stateConf intrp3b)
     let intrp4a = after intrp3a (GateValue (In "water") [Cint 4])
     assertEqual "2a after water 4: " (getSTSIntrpState2 1 7 /\ getSTSIntrpState2 2 7) (stateConf intrp4a)
     let intrp4b = after intrp3b (GateValue (In "water") [Cint 4])
     assertEqual "2b after water 4: "  (getSTSIntrpState2 1 7) (stateConf intrp4b)
     let intrp5a = after intrp4a (GateValue (Out "ok") [Cint 7])
     assertEqual "2a after ok 7: " (getSTSIntrpState2 0 7) (stateConf intrp5a)
     let intrp5b = after intrp4b (GateValue (Out "ok") [Cint 7])
     assertEqual "2b after ok 7: " (getSTSIntrpState2 0 7) (stateConf intrp5b)
     let intrp6a = after intrp5a (GateValue (In "water") [Cint 5])
     assertEqual "2a after water 5: " (getSTSIntrpState2 2 12) (stateConf intrp6a)
     let intrp6b = after intrp5b (GateValue (In "water") [Cint 5])
     assertEqual "2b after water 5: " underspecified (stateConf intrp6b)


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
specParameterized :: (String -> IOAct String String) -> (String -> IOAct String String) -> (forall a.FreeLatticeSlow a -> FreeLatticeSlow a -> FreeLatticeSlow a) -> Bool -> IOSTS FreeLatticeSlow Integer String String
specParameterized startType endType comp splitFirst =
    let p = sVar pvar :: Expr Integer
        q = sVar qvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        start = SymInteract (startType "start") [pvar]
        end = SymInteract (endType "end") [pvar, qvar]
        done = SymInteract (Out "done") []
        initConf = pure 0 :: FreeLatticeSlow Integer
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
t1 :: (Ord i, Ord o, Num a1, Num a2, IsString t1, IsString t2, IsString o, Eq a1) => (t1 -> IOAct i o) -> (t2 -> IOAct i o) -> Integer -> Integer -> Integer -> a1 -> Map.Map (GateValue (IOAct i o)) a2
t1 startType _ p1 _ _ 0 = Map.fromList $ [((GateValue (startType "start") [Cint p1]), 1)]
t1 _ endType _ p2 q2 1 = Map.fromList $ [((GateValue (endType "end") [Cint p2, Cint q2]), 2)]
t1 _ _ _ _ _ 2 = Map.fromList $ [((GateValue (Out "done") []), 3)]
t1 _ _ _ _ _ 3 = Map.fromList $ []
impParameterized :: (String -> IOAct String String) -> (String -> IOAct String String) -> Integer -> Integer -> Integer -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
impParameterized startType endType p1 p2 q2 = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> t1 startType endType p1 p2 q2) (0 :: Integer) :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
    Adapter.mapActionsFromSut toIOGateValue imp

testLatticeSTSParameterized' :: String -> Bool -> (forall a. FreeLatticeSlow a -> FreeLatticeSlow a -> FreeLatticeSlow a) -> Bool -> Integer -> Integer -> Integer -> Maybe [SuspendedIFGateValue String String] -> Test
testLatticeSTSParameterized' testName inputThenOut comp splitFirst p1 p2 q2 expectedNonConformalTrace = TestCase $ do
    let (startType, endType, startType', endType') =
            if inputThenOut
                then (In, Out, inp, out)
                else (Out, In, out, inp)
    let nrSteps = 4

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impParameterized startType endType p1 p2 q2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specParameterized startType endType comp splitFirst) stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester specIntrpr testSelector imp

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
inp :: i -> [Constant] -> GateValue (IOAct (InputAttempt i) o)
inp g vals = GateValue (In (InputAttempt (g, True))) vals
inpf :: i -> [Constant] -> GateValue (IOAct (InputAttempt i) o)
inpf g vals = GateValue (In (InputAttempt (g, False))) vals
out :: o -> [Constant] -> GateValue (IOAct i (Suspended o))
out g vals = GateValue (Out (OutSusp g)) vals

testLatticeSTSParameterized :: String -> Bool -> (forall a. FreeLatticeSlow a -> FreeLatticeSlow a -> FreeLatticeSlow a) -> Integer -> Integer -> Integer -> Maybe [SuspendedIFGateValue String String] -> [Test]
testLatticeSTSParameterized testName inputThenOut comp p1 p2 q2 expectedNonConformalTrace = [
    testLatticeSTSParameterized' testName          inputThenOut comp False p1 p2 q2 expectedNonConformalTrace,
    testLatticeSTSParameterized' (testName ++ "'") inputThenOut comp True  p1 p2 q2 expectedNonConformalTrace
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
specQ :: IOSTS FreeLatticeSlow Integer String String
specQ =
    let p = sVar pvar :: Expr Integer
        q = sVar qvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        start = SymInteract (In "start") [pvar]
        end = SymInteract (Out "end") [pvar, qvar]
        initConf = pure 0 :: FreeLatticeSlow Integer
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
tq :: (Ord g, IsString t, Num a1, Num a2, Eq a1) => (t -> g) -> Integer -> a1 -> Map.Map (GateValue g) a2
tq startType p 0 = Map.fromList $ [((GateValue (startType "start") [Cint p]), 1)]
tq _ _ 1 = Map.fromList $ []
impQParameterized :: (String -> IOAct String String) -> Integer -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
impQParameterized startType p = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> tq startType p) (0 :: Integer) :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
    Adapter.mapActionsFromSut toIOGateValue imp

testLatticeSTSQuiescentPass :: String -> Bool -> Test
testLatticeSTSQuiescentPass testName _ = TestCase $ do
    let nrSteps = 2

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete specQ stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester specIntrpr testSelector imp

    assertEqual (testName ++ ": expected Pass after " ++ show observed) Pass verdict
    assertEqual (testName ++ ": expected conformal trace") [
                inp "start" [Cint 2],
                GateValue δ []
                ] observed

testLatticeSTSQuiescentFail1 :: String -> Bool -> Test
testLatticeSTSQuiescentFail1 testName splitFirst = TestCase $ do
    let nrSteps = 2

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specParameterized In Out (\/) splitFirst) stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester specIntrpr testSelector imp

    assertEqual (testName ++ ": expected Pass after " ++ show observed) Fail verdict
    assertEqual (testName ++ ": expected nonconformal trace") [
                inp "start" [Cint 2],
                GateValue δ []
                ] observed

testLatticeSTSQuiescentFail2 :: String -> Bool -> Test
testLatticeSTSQuiescentFail2 testName _ = TestCase $ do
    let nrSteps = 2

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impParameterized In Out 2 42 42
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete specQ stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester specIntrpr testSelector imp

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
specUnimplementableParameterized :: Bool -> IOSTS FreeLatticeSlow Integer String String
specUnimplementableParameterized splitFirst =
    let p = sVar pvar :: Expr Integer
        q = sVar qvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        start = SymInteract (In "start") [pvar]
        end = SymInteract (Out "end") [pvar, qvar]
        initConf = pure 0 :: FreeLatticeSlow Integer
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

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specUnimplementableParameterized splitFirst) stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester specIntrpr testSelector imp

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

-- ============================================================================
-- Symbolic path-condition / execution-tree tests (merged from feature branch).
-- Ported to the sbv-based backend: the old Lattest.SMT.SMT/Config solver is
-- replaced by Lattest.SMT.runSMT, FreeLattice by the (now CNF) FreeLattice,
-- and the non-normalising free lattice by Reference.FreeLatticeSlow.
-- ============================================================================

p, q, x :: Expr Integer
p = sVar pvar
q = sVar qvar
x = sVar xvar

water, ok, coffee :: SymInteract (IOAct String String)
water = SymInteract (In "water") [pvar]
ok = SymInteract (Out "ok") [pvar]
coffee = SymInteract (Out "coffee") []

-- Interactions and STS for the branching tests, using the CNF lattice monad (FreeLattice).
-- Input variants (unsatisfied guard -> underspecified/top) and output variants (unsatisfied guard -> forbidden/bottom).
gateA = SymInteract (In "a") [pvar, qvar]
gateB = SymInteract (In "b") [pvar, qvar]
gateAo = SymInteract (Out "a") [pvar, qvar]
gateBo = SymInteract (Out "b") [pvar, qvar]

branchInitAssign :: Valuation
branchInitAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)

-- A depth-2 binary-branching STS over the CNF monad:
--   loc 0 --a--> {loc 1, loc 2}   combined with op0
--   loc 1 --b--> {loc 3, loc 4}   combined with op1
--   loc 2 --b--> {loc 5, loc 6}   combined with op2
-- Each branch has exactly two outgoing transitions, combined by either disjunction (\/) or conjunction (/\).
-- The two destination guards at each branch are gp (p>=5) and gq (q>=5) on two independent parameters p and q, so
-- they are orthogonal: all four cells of the value-partition (neither / p-only / q-only / both) are satisfiable and
-- routed differently, and the choice of branch operator is observable in the resulting path condition.
type Branch = FreeLattice (STStdest, Integer) -> FreeLattice (STStdest, Integer) -> FreeLattice (STStdest, Integer)

-- The first-level gate g1 is used at loc 0; the second-level gate g2 at locs 1 and 2. Passing input or output gates
-- selects whether unsatisfied guards fall through to top or to bottom.
branchingSTS :: SymInteract (IOAct String String) -> SymInteract (IOAct String String) -> Branch -> Branch -> Branch -> IOSTS FreeLattice Integer String String
branchingSTS g1 g2 op0 op1 op2 =
    let gp = p .>= 5
        gq = q .>= 5
        asgn = assignment [xvar =: p]
        switches loc = case loc of
            0 -> Map.fromList [(g1, atom (stsTLoc gp asgn, 1) `op0` atom (stsTLoc gq asgn, 2))]
            1 -> Map.fromList [(g2, atom (stsTLoc gp noAssignment, 3) `op1` atom (stsTLoc gq noAssignment, 4))]
            2 -> Map.fromList [(g2, atom (stsTLoc gp noAssignment, 5) `op2` atom (stsTLoc gq noAssignment, 6))]
            _ -> Map.empty
    in automaton (atom 0 :: FreeLattice Integer) (Set.fromList [g1, g2]) switches

branchingIntrpr :: SymInteract (IOAct String String) -> SymInteract (IOAct String String) -> Branch -> Branch -> Branch -> STSIntrp FreeLattice Integer (IOAct String String)
branchingIntrpr g1 g2 op0 op1 op2 = interpretSTS (branchingSTS g1 g2 op0 op1 op2) branchInitAssign

-- Path conditions over the branching STS, exercising disjunctive vs conjunctive branching in the CNF monad, for
-- inputs and outputs. asDualExpr reads the configuration dually, but the input/output distinction is whether an
-- unsatisfied guard falls through to top (underspecified, inputs) or bottom (forbidden, outputs):
--   * for INPUTS a disjunctive (\/) branch requires *both* guards (gp ∧ gq) and a conjunctive (/\) one *either*
--     (gp ∨ gq) -- the operator is dualised, because an unsatisfied alternative becomes top and absorbs the join;
--   * for OUTPUTS it is mirrored -- disjunction yields gp ∨ gq and conjunction gp ∧ gq -- because an unsatisfied
--     alternative becomes bottom, which is absorbed by the join and absorbing for the meet.
testBranchingPathCondition :: Test
testBranchingPathCondition = TestCase $ do
    let disj = (\/) :: Branch
        conj = (/\) :: Branch
        isSat guard = SMT.runSMT $ isJust <$> solveGuard (Set.toList $ freeVars guard) guard
        assertSat lbl g = isSat g >>= assertBool (lbl ++ " should be satisfiable")
        assertUnsat lbl g = isSat g >>= (assertBool (lbl ++ " should be unsatisfiable") . not)
        assertNotTautology lbl g = isSat (sNot g) >>= assertBool (lbl ++ " should not be a tautology")
        -- a ⟹ b iff a ∧ ¬b is unsatisfiable
        assertImplies lbl a b = isSat (a .&& sNot b) >>= (assertBool (lbl ++ ": expected implication") . not)
        assertNotImplies lbl a b = isSat (a .&& sNot b) >>= assertBool (lbl ++ ": expected non-implication")
        combos = [ ("DDD",disj,disj,disj), ("DDC",disj,disj,conj), ("DCD",disj,conj,disj), ("DCC",disj,conj,conj)
                 , ("CDD",conj,disj,disj), ("CDC",conj,disj,conj), ("CCD",conj,conj,disj), ("CCC",conj,conj,conj) ]
    -- 1. Across every combination of branch operators, both traces, and both input/output, the path condition is a
    --    genuine constraint: never collapsing to True (a tautology) nor to False (unsatisfiable).
    sequence_ [ assertSat (kind ++ " " ++ nm ++ " " ++ tn) g >> assertNotTautology (kind ++ " " ++ nm ++ " " ++ tn) g
              | (kind, g1, g2) <- [ ("in", gateA, gateB), ("out", gateAo, gateBo) ]
              , (nm, o0, o1, o2) <- combos
              , (tn, tr) <- [ ("[a]", [g1]), ("[a,b]", [g1, g2]) ]
              , let g = interactsToSpecifiedCondition (branchingIntrpr g1 g2 o0 o1 o2) tr ]
    -- 2. INPUT branch on [a]: disjunction is strictly stronger than conjunction (it requires both guards).
    let inD = interactsToSpecifiedCondition (branchingIntrpr gateA gateB disj disj disj) [gateA]
        inC = interactsToSpecifiedCondition (branchingIntrpr gateA gateB conj conj conj) [gateA]
    assertImplies    "input [a]: disjunction ⟹ conjunction" inD inC
    assertNotImplies "input [a]: conjunction ⇏ disjunction" inC inD
    assertUnsat "input [a] disjunction with p<5 (needs p>=5 AND q>=5)" (inD .&& (p .<= 4))
    assertSat   "input [a] conjunction with p<5 (q>=5 alone suffices)" (inC .&& (p .<= 4))
    -- 3. OUTPUT branch on [a]: mirrored -- conjunction is strictly stronger than disjunction.
    let outD = interactsToSpecifiedCondition (branchingIntrpr gateAo gateBo disj disj disj) [gateAo]
        outC = interactsToSpecifiedCondition (branchingIntrpr gateAo gateBo conj conj conj) [gateAo]
    assertImplies    "output [a]: conjunction ⟹ disjunction" outC outD
    assertNotImplies "output [a]: disjunction ⇏ conjunction" outD outC
    assertUnsat "output [a] conjunction with p<5 (needs p>=5 AND q>=5)" (outC .&& (p .<= 4))
    assertSat   "output [a] disjunction with p<5 (q>=5 alone suffices)" (outD .&& (p .<= 4))
    -- 4. The same input/output contrast one branching level deeper, on trace [a,b].
    let inDAB = interactsToSpecifiedCondition (branchingIntrpr gateA gateB disj disj disj) [gateA, gateB]
        inCAB = interactsToSpecifiedCondition (branchingIntrpr gateA gateB conj conj conj) [gateA, gateB]
        outDAB = interactsToSpecifiedCondition (branchingIntrpr gateAo gateBo disj disj disj) [gateAo, gateBo]
        outCAB = interactsToSpecifiedCondition (branchingIntrpr gateAo gateBo conj conj conj) [gateAo, gateBo]
    assertImplies    "input [a,b]: all-disjunction ⟹ all-conjunction" inDAB inCAB
    assertNotImplies "input [a,b]: all-conjunction ⇏ all-disjunction" inCAB inDAB
    assertImplies    "output [a,b]: all-conjunction ⟹ all-disjunction" outCAB outDAB
    assertNotImplies "output [a,b]: all-disjunction ⇏ all-conjunction" outDAB outCAB

-- A minimal STS for asserting the tree structures directly (rather than via the SMT solver):
--   loc 0 --a[p>=5]--> loc 1   (x := p) ; loc 1 is terminal.
-- One input gate keeps the symbolic-execution tree narrow enough to read.
inGate :: SymInteract (IOAct String String)
inGate = SymInteract (In "a") [pvar]
outGate :: SymInteract (IOAct String String)
outGate = SymInteract (Out "x") [pvar]

treeSTS :: IOSTS FreeLattice Integer String String
treeSTS =
    let switches loc = case loc of
            0 -> Map.fromList [(inGate, ordReturn (stsTLoc (p .>= -20) (assignment [xvar =: p]), 1) /\ ordReturn (stsTLoc (p .<= 20) (assignment [xvar =: p]), 2))]
            1 -> Map.fromList [(outGate, ordReturn (stsTLoc (x .% 2 .== 0) (assignment []), 3) \/ ordReturn (stsTLoc (x .% 3 .== 0) (assignment []), 3))]
            2 -> Map.fromList [(outGate, ordReturn (stsTLoc (x .* p .>= 0) (assignment []), 3))]
            _ -> Map.empty
    in automaton (ordReturn 0 :: FreeLattice Integer) (Set.fromList [inGate, outGate]) switches

treeIntrpr :: STSIntrp FreeLattice Integer (IOAct String String)
treeIntrpr = interpretSTS treeSTS branchInitAssign

-- Pretty-printers for the (infinite) trees, bounded to a maximum depth, rendered as an indented outline.
showGate :: SymInteract (IOAct String String) -> String
showGate (SymInteract (In s) _) = "?" ++ s
showGate (SymInteract (Out s) _) = "!" ++ s

prettySolveTree :: Int -> Solve.SolveTree (IOAct String String) -> String
prettySolveTree maxDepth t0 = unlines (go 0 "" t0)
    where
    go d indent t
        | d > maxDepth = [indent ++ "..."]
        | otherwise =
            let cond = Solve.traceCondition t
                showCond = indent ++ "cond " ++ show cond
            in if cond == sFalse -- the solve tree has conditions that are monononically decreasing as you go down the tree, so False is a sink
                then [showCond]
                else showCond
                        : concatMap (\(act, sub) -> (indent ++ showGate act ++ ":") : go (d + 1) (indent ++ "    ") sub)
                                    (Map.toList (Solve.traceChildren t))

testLinearCoffeeTreeStructure :: Test
testLinearCoffeeTreeStructure = testTreeStructure "linear" stsExampleIntrpr 3

testComplexTreeStructure :: Test
testComplexTreeStructure = testTreeStructure "complex" treeIntrpr 3

milkvar :: Variable
milkvar = (Variable "milk" BoolType)
milk = sVar milkvar
a = SymInteract (In "a") []
b = SymInteract (In "b") [pvar]
tea = SymInteract (Out "tea") [pvar]
espresso = SymInteract (Out "esp") [pvar, milkvar]
take = SymInteract (In "take") []

composedCoffeeMachineAssign :: Valuation
composedCoffeeMachineAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)

composedCoffeeMachine :: IOSTS FreeLatticeSlow String String String
composedCoffeeMachine =
    let initConf = ordReturn "a0" /\ ordReturn "b0" /\ ordReturn "c0" /\ ordReturn "d0":: FreeLatticeSlow String
        asTransition = \q -> (stsTLoc sTrue noAssignment, q)
        switches = \q -> case q of
            "a0" -> Map.fromList [(a, ordReturn (stsTLoc sTrue noAssignment, "a1"))]
            "a1" -> Map.fromList [(tea, ordReturn (stsTLoc (p .== 2) $ noAssignment, "a2"))]
            "b0" -> Map.fromList [(b, ordReturn (stsTLoc sTrue $ assignment [xvar =: p], "b1"))]
            "b1" -> Map.fromList [(espresso, ordReturn (stsTLoc (p .== x) $ noAssignment, "b2"))]
            "c0" -> Map.fromList [(b, ordReturn (stsTLoc sTrue noAssignment, "c1"))]
            "c1" -> Map.fromList [(espresso, ordReturn (stsTLoc (milk) $ noAssignment, "c2"))]
            "d0" -> Map.fromList $ [(water, foldr (/\) underspecified [ordReturn (stsTLoc (x .< 10) $ assignment [xvar =: x .+ p], d) | d <- ["a0", "b0", "c0", "d0"]])] ++ [(input, ordReturn (stsTLoc sTrue noAssignment, "d1")) | input <- [a,b]]
            "d1" -> Map.fromList [(output, ordReturn (stsTLoc sTrue $ assignment [xvar =: x .- p], "d2")) | output <- [tea, espresso]]
            "d2" -> Map.fromList [(take, asTransition <#> initConf)]
            -- terminal locations (a2, b2, c2): map every interaction explicitly to unspecified
            _ -> Map.fromList [(gate, underspecified) | gate <- [water, a, b, tea, espresso, take]]
    in automaton initConf (Set.fromList [water,a,b,tea,espresso,take]) switches
composedCoffeeMachineIntrpr :: STSIntrp FreeLatticeSlow String (IOAct String String)
composedCoffeeMachineIntrpr = interpretSTS composedCoffeeMachine composedCoffeeMachineAssign

testComposedCoffeeTreeStructure :: Test
testComposedCoffeeTreeStructure = testTreeStructure "composed" composedCoffeeMachineIntrpr 3

-- | One step of a concrete trace: a symbolic interaction together with the concrete values for its parameters.
type ConcreteStep = (IOSymInteract String String, [Constant])

-- | The concrete gate value of a step, for feeding to `after`.
stepGateValue :: ConcreteStep -> GateValue (IOAct String String)
stepGateValue (SymInteract g _, vals) = GateValue g vals

-- | Build the valuation that fills the symbolic guards: the parameter `v` of the interaction at trace position `n`
-- appears in the guards as `v_n` (matching `indexVar` in SolveSTS.hs), and is bound here to its concrete value.
traceValuation :: [ConcreteStep] -> Valuation
traceValuation steps = fromConstantsMap $ Map.unions $ zipWith stepConstMap [0..] steps
    where
    stepConstMap n (SymInteract _ vars, vals) = Map.fromList $ zipWith (\var val -> (indexVar n var, val)) vars vals
    indexVar n (Variable name t) = Variable (name ++ "_" ++ show n) t

testConcreteTraceSpecifiedAllowedCorrespondence :: Test
testConcreteTraceSpecifiedAllowedCorrespondence = TestList
    [ correspondenceCase "[water 3]"                         -- neither: input, guard x<10 holds (x=0)
        [(water, [Cint 3])] Indefinite
    , correspondenceCase "[water 3, water 5]"                -- neither: second water still has x=3<10
        [(water, [Cint 3]), (water, [Cint 5])] Indefinite
    , correspondenceCase "[water 12, water 5]"               -- underspecified: second water blocked, x=12>=10
        [(water, [Cint 12]), (water, [Cint 5])] Underspecified
    , correspondenceCase "[water 3, b 4, esp 4 milk]"        -- neither: esp satisfies p=x (4) and milk
        [(water, [Cint 3]), (b, [Cint 4]), (espresso, [Cint 4, Cbool True])] Indefinite
    , correspondenceCase "[water 3, b 4, esp 5 milk]"        -- forbidden: esp output violates p=x (5/=4)
        [(water, [Cint 3]), (b, [Cint 4]), (espresso, [Cint 5, Cbool True])] Forbidden
    , correspondenceCase "[water 3, b 4, esp 4 nomilk]"      -- forbidden: esp output violates milk
        [(water, [Cint 3]), (b, [Cint 4]), (espresso, [Cint 4, Cbool False])] Forbidden
    ]
    where
    correspondenceCase label steps expectedSpecifiedness = TestCase $ do
        let symTrace = fst <$> steps
            gateValues = stepGateValue <$> steps
            valuation = traceValuation steps
            -- (1) semantic verdict: the state configuration after running the concrete trace
            finalConf = stateConf $ foldl after composedCoffeeMachineIntrpr gateValues
            -- (2) symbolic verdict: fill the concrete values into the guards and evaluate to a constant
            specifiedGuard = interactsToSpecifiedCondition composedCoffeeMachineIntrpr symTrace
            allowedGuard = interactsToAllowedCondition composedCoffeeMachineIntrpr symTrace
        -- sanity check: the chosen values really drive the trace to the specifiedness we expect
        assertEqual (label ++ ": concrete specifiedness") expectedSpecifiedness (specifiedness finalConf)
        specifiedVal <- assertEvaluatesToBool (label ++ ": specified guard") (substConst valuation specifiedGuard)
        allowedVal <- assertEvaluatesToBool (label ++ ": allowed guard") (substConst valuation allowedGuard)
        -- the correspondence: specified <-> not underspecified, allowed <-> not forbidden
        assertEqual (label ++ ": specified guard vs. isSpecified") (isSpecified finalConf) specifiedVal
        assertEqual (label ++ ": allowed guard vs. isAllowed") (isAllowed finalConf) allowedVal
    -- a fully-substituted guard must reduce to a constant boolean; anything else means a variable leaked through
    assertEvaluatesToBool :: String -> Expr Bool -> IO Bool
    assertEvaluatesToBool label g = case eval g of
        Right b -> return b
        Left err -> assertFailure (label ++ " did not reduce to a constant: " ++ err ++ " (guard: " ++ show g ++ ")")

-- QuickCheck version of the same correspondence, with the concrete traces *generated* instead of hand-picked.
--
-- The interactions and their symbolic parameters are read from the model's alphabet (not hard-coded), and every
-- parameter is filled with a randomly-chosen value of its declared type. The property is parametric in the model, so
-- any STS interpreter over String gates can be checked; below it is applied to the composed coffee machine, but a
-- future model only needs to be passed to `prop_specifiedAllowedCorrespondence` to be covered.

-- | Generate a concrete value for a symbolic parameter, based only on its declared type. The ranges are deliberately
-- small: the example models are toy examples, so large integers would only slow things down without exercising new
-- behaviour (guards compare against small constants like 2, 10).
genConstantForType :: Variable -> Gen Constant
genConstantForType (Variable _ IntType)    = Cint <$> choose (-5, 20)
genConstantForType (Variable _ BoolType)   = Cbool <$> elements [False, True]
genConstantForType (Variable _ StringType) = Cstring <$> elements ["", "a", "b", "c"]

-- | Generate a concrete trace over a model's alphabet: pick interactions (and hence their symbolic parameters) from
-- the syntactic automaton, then fill in a value for each parameter. Traces are kept short, both because the toy
-- models are shallow and because the non-normalising FreeLatticeSlow configuration grows with the trace length.
genConcreteTrace :: STSIntrp m loc (IOAct String String) -> Gen [ConcreteStep]
genConcreteTrace intrpr = do
    let alph = Set.toList $ alphabet $ syntacticAutomaton intrpr
    len <- choose (0, 4)
    vectorOf len $ do
        interaction@(SymInteract _ vars) <- elements alph
        vals <- traverse genConstantForType vars
        return (interaction, vals)

-- | The correspondence property (see 'testConcreteTraceSpecifiedAllowedCorrespondence' for the full explanation),
-- parametric in the model. For every generated concrete trace: the specified guard evaluates to True exactly when
-- the concrete configuration is specified (not underspecified), and the allowed guard exactly when it is allowed
-- (not forbidden).
prop_specifiedAllowedCorrespondence ::
    (BoundedMonad m, Foldable m, BooleanConfiguration m, (forall a. Ord a => Ord (m a)), Ord loc)
    => STSIntrp m loc (IOAct String String) -> Property
prop_specifiedAllowedCorrespondence intrpr = forAll (genConcreteTrace intrpr) $ \steps ->
    let symTrace = fst <$> steps
        gateValues = stepGateValue <$> steps
        valuation = traceValuation steps
        finalConf = stateConf $ foldl after intrpr gateValues
        specifiedGuard = interactsToSpecifiedCondition intrpr symTrace
        allowedGuard = interactsToAllowedCondition intrpr symTrace
    in counterexample ("trace: " ++ show gateValues) $
            checkGuard "specified" (isSpecified finalConf) (substConst valuation specifiedGuard)
       .&&. checkGuard "allowed"   (isAllowed finalConf)    (substConst valuation allowedGuard)
    where
    checkGuard name expected g = case eval g of
        Right b  -> counterexample (name ++ " guard evaluated to " ++ show b ++ ", expected " ++ show expected) (b == expected)
        Left err -> counterexample (name ++ " guard did not reduce to a constant: " ++ err ++ " (guard: " ++ show g ++ ")") False

goldenDir :: FilePath
goldenDir = "test/expected-test-output"

-- Compare rendered output against a golden file, then always (re)generate it (creating the directory if needed).
-- Returns a failure message if it did not match, or Nothing if it did. A completely missing golden file is
-- (re)generated but reported as a failure, so a freshly created baseline is never silently accepted.
goldenCheck :: String -> FilePath -> String -> IO (Maybe String)
goldenCheck what path actual = do
    existing <- Exception.try (UTF8.toString <$> BS.readFile path) :: IO (Either Exception.IOException String)
    createDirectoryIfMissing True (takeDirectory path)
    BS.writeFile path (UTF8.fromString actual)
    return $ case existing of
        Right expected | expected == actual -> Nothing
                       | otherwise -> Just ("\nprint of " ++ what ++ " does not match, expected:" ++ expected ++ "but received:" ++ actual)
        Left _ -> Just ("\ngolden file " ++ path ++ " for " ++ what ++ " was missing; (re)generated it -- rerun to compare against it")

-- Run all golden checks (so every file is regenerated in one run, even on failure), then fail once if any did not match.
goldenAssert :: [IO (Maybe String)] -> Assertion
goldenAssert checks = do
    failures <- catMaybes <$> sequence checks
    if null failures then return () else assertFailure (concat failures)

testTreeStructure :: (BoundedMonad m, Foldable m, Ord (m (Expr Bool)), BooleanConfiguration m, Ord q) => String -> STSIntrp m q (IOAct String String) -> Int -> Test
testTreeStructure testName stsIntrpr depth = TestCase $ goldenAssert
    [ {-goldenCheck (testName ++ ":symbolicExecutionTree") (goldenDir </> (testName ++ ".exectree.txt")) actualExecTree
    , -}
      goldenCheck (testName ++ ":toSpecifiedTree") (goldenDir </> (testName ++ ".specifiedtree.txt")) actualSpecifiedTree
    , goldenCheck (testName ++ ":toAllowedTree") (goldenDir </> (testName ++ ".allowedtree.txt")) actualAllowedTree
    ]
    where
    --tree = Solve.symbolicExecutionTree stsIntrpr
    --actualExecTree = "\n" ++ prettyExecTree depth tree
    actualSpecifiedTree = "\n" ++ prettySolveTree depth (Solve.toSpecifiedTree stsIntrpr)
    actualAllowedTree = "\n" ++ prettySolveTree depth (Solve.toAllowedTree stsIntrpr)

testSTSPathCondition :: Test
testSTSPathCondition = TestCase $ do
    let -- is the given guard satisfiable, according to the SMT solver?
        isSat guard = SMT.runSMT $ isJust <$> solveGuard (Set.toList $ freeVars guard) guard
        pathCond = interactsToSpecifiedCondition stsExampleIntrpr
        assertSat lbl prefix = isSat (pathCond prefix) >>= assertBool (lbl ++ " should be satisfiable")
        assertUnsat lbl prefix = isSat (pathCond prefix) >>= (assertBool (lbl ++ " should be unsatisfiable") . not)
        -- guards against a regression to True: a tautology's negation is unsatisfiable
        assertNotTautology lbl prefix = isSat (sNot (pathCond prefix)) >>= assertBool (lbl ++ " should not be a tautology")
    -- Build up from a trivial example to the full trace [water, ok, water, ok, coffee]. Every prefix must yield a
    -- meaningful path condition, never collapsing to True (which it did before the symbolic-execution-tree fixes).
    assertSat           "[]" []
    assertUnsat         "[coffee] (coffee cannot be the first action: x starts at 0, guard needs x >= 15)" [coffee]
    assertSat           "[water]" [water]
    assertNotTautology  "[water]" [water]
    assertSat           "[water, ok]" [water, ok]
    assertNotTautology  "[water, ok]" [water, ok]
    assertSat           "[water, ok, water]" [water, ok, water]
    assertNotTautology  "[water, ok, water]" [water, ok, water]
    assertSat           "[water, ok, water, ok]" [water, ok, water, ok]
    assertNotTautology  "[water, ok, water, ok]" [water, ok, water, ok]
    assertSat           "[water, ok, water, ok, coffee]" [water, ok, water, ok, coffee]
    assertNotTautology  "[water, ok, water, ok, coffee]" [water, ok, water, ok, coffee]

stsConjOfDifferentVals :: IOSTS FreeLattice Integer String String
stsConjOfDifferentVals =
    let switches loc = case loc of
            0 -> Map.fromList [(outGate, ordReturn (stsTLoc sTrue (assignment [xvar =: (1 :: Expr Integer)]), 1) /\ ordReturn (stsTLoc sTrue (assignment [xvar =: (2 :: Expr Integer)]), 2))]
            1 -> Map.fromList [(outGate, ordReturn (stsTLoc sTrue (assignment []), 1))]
            2 -> Map.fromList [(outGate, ordReturn (stsTLoc sTrue (assignment []), 2))]
            _ -> Map.empty
    in automaton (ordReturn 0 :: FreeLattice Integer) (Set.fromList [outGate]) switches

getSTSIntrpState' :: Integer ->  Integer -> FreeLattice (IntrpState Integer)
getSTSIntrpState' loc val = ordReturn $ IntrpState loc $ fromConstantsMap $ Map.singleton (Variable "x" IntType) (Cint val)

stsConjOfDifferentValsIntrpr :: STSIntrp FreeLattice Integer (IOAct String String)
stsConjOfDifferentValsIntrpr = interpretSTS treeSTS branchInitAssign

testConjunctionOfDifferentValuations :: Test
testConjunctionOfDifferentValuations = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsConjOfDifferentValsIntrpr)
    let intrp2 = after stsConjOfDifferentValsIntrpr (GateValue (Out "x") [Cint 0])
    assertEqual "after x: " forbidden (stateConf intrp2)


stsExampleFL :: IOSTS FreeLattice Integer String String
stsExampleFL =
    let p = sVar pvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        water = SymInteract (In "water") [pvar]
        ok = SymInteract (Out "ok") [pvar]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = ordReturn 0
        switches = \q -> case q of
            0 -> Map.fromList [(water, ordReturn (stsTLoc waterGuard waterAssign, 1)),
                                (coffee, ordReturn (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, ordReturn (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches

-- Define an STS with two sink locations to sequentially compose with the example STS.
stsPrelude :: IOSTS FreeLattice Integer String String
stsPrelude =
    let p = sVar pvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        startEmpty = SymInteract (In "startEmpty") []
        startWithWater = SymInteract (In "startWithWater") [pvar]
        error = SymInteract (Out "error") []
        waterAssign = assignment [xvar =: x .+ p]
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(startEmpty, ordReturn (stsTLoc sTrue noAssignment, 1)),
                                (startWithWater, ordReturn (stsTLoc sTrue waterAssign, 2)),
                                (error, ordReturn (stsTLoc sTrue noAssignment, 0))]
            1 -> Map.empty
            2 -> Map.empty
            _ -> Map.empty
    in automaton initConf (Set.fromList [startEmpty, startWithWater, error]) switches

stsSeqComposed :: STSIntrp FreeLattice (Either Integer Integer) (IOAct String String)
stsSeqComposed = interpretSTS (stsPrelude |> stsExampleFL) stsExampleInitAssign

stsSeqComposedAt :: STSIntrp FreeLattice (Either Integer Integer) (IOAct String String)
stsSeqComposedAt = interpretSTS (sequentiallyAt stsPrelude [1,2] stsExampleFL) stsExampleInitAssign

stsSeqComposedAtOne :: STSIntrp FreeLattice (Either Integer Integer) (IOAct String String)
stsSeqComposedAtOne = interpretSTS (sequentiallyAt stsPrelude [1] stsExampleFL) stsExampleInitAssign

getSTSIntrpStateEither :: (Either Integer Integer) -> Integer -> FreeLattice (IntrpState (Either Integer Integer))
getSTSIntrpStateEither loc val = ordReturn $ IntrpState loc $ fromConstantsMap $ Map.singleton (Variable "x" IntType) (Cint val)

testPrintSeqCompSTS :: Test
testPrintSeqCompSTS = TestCase $ assertBool failureMessage (expected == actual)
    where
    failureMessage = "print of STS does not match, expected:" ++ expected ++ "but received:" ++ actual
    actual = "\n" ++ prettyPrintIntrp stsSeqComposed ++ "\n"
    expected = [QQ.r|
current state configuration: (Left 0,{x:=0})
initial location configuration: Left 0
locations: Left 0, Left 1, Left 2, Right 0, Right 1, Right 2
transitions:
Left 0  ――?"startEmpty" []⟶  (True, {},Left 1)
Left 0  ――?"startWithWater" [p:Int]⟶  (True, {x:=(p+x)},Left 2)
Left 0  ――?"water" [p:Int]⟶  ⊤
Left 0  ――!"coffee" []⟶  ⊥
Left 0  ――!"error" []⟶  (True, {},Left 0)
Left 0  ――!"ok" [p:Int]⟶  ⊥
Left 1  ――?"startEmpty" []⟶  ⊤
Left 1  ――?"startWithWater" [p:Int]⟶  ⊤
Left 1  ――?"water" [p:Int]⟶  ((((-p+10)) ≥ 0)∧(((p+-1)) ≥ 0), {x:=(p+x)},Right 1)
Left 1  ――!"coffee" []⟶  (((x+-15)) ≥ 0, {},Right 2)
Left 1  ――!"error" []⟶  ⊥
Left 1  ――!"ok" [p:Int]⟶  ⊥
Left 2  ――?"startEmpty" []⟶  ⊤
Left 2  ――?"startWithWater" [p:Int]⟶  ⊤
Left 2  ――?"water" [p:Int]⟶  ((((-p+10)) ≥ 0)∧(((p+-1)) ≥ 0), {x:=(p+x)},Right 1)
Left 2  ――!"coffee" []⟶  (((x+-15)) ≥ 0, {},Right 2)
Left 2  ――!"error" []⟶  ⊥
Left 2  ――!"ok" [p:Int]⟶  ⊥
Right 0  ――?"startEmpty" []⟶  ⊤
Right 0  ――?"startWithWater" [p:Int]⟶  ⊤
Right 0  ――?"water" [p:Int]⟶  ((((-p+10)) ≥ 0)∧(((p+-1)) ≥ 0), {x:=(p+x)},Right 1)
Right 0  ――!"coffee" []⟶  (((x+-15)) ≥ 0, {},Right 2)
Right 0  ――!"error" []⟶  ⊥
Right 0  ――!"ok" [p:Int]⟶  ⊥
Right 1  ――?"startEmpty" []⟶  ⊤
Right 1  ――?"startWithWater" [p:Int]⟶  ⊤
Right 1  ――?"water" [p:Int]⟶  ⊤
Right 1  ――!"coffee" []⟶  ⊥
Right 1  ――!"error" []⟶  ⊥
Right 1  ――!"ok" [p:Int]⟶  ((x) = (p), {},Right 0)
Right 2  ――?"startEmpty" []⟶  ⊤
Right 2  ――?"startWithWater" [p:Int]⟶  ⊤
Right 2  ――?"water" [p:Int]⟶  ⊤
Right 2  ――!"coffee" []⟶  ⊥
Right 2  ――!"error" []⟶  ⊥
Right 2  ――!"ok" [p:Int]⟶  ⊥
|]

-- Using |> and sequentiallyAt should yield the same result.
testSeqComposedSTS :: Test
testSeqComposedSTS = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf stsSeqComposed)
    let intrp1 = after stsSeqComposed (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrp1)
    -- branch 1: startEmpty
    let intrp2 = after intrp1 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpStateEither (Left 1) 0) (stateConf intrp2)
    -- behavior transitions to sts2
    let intrp3 = after intrp2 (GateValue (In "water") [Cint 7])
    assertEqual "after water 7: " (getSTSIntrpStateEither (Right 1) 7) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (Out "ok") [Cint 7])
    assertEqual "after ok 7: " (getSTSIntrpStateEither (Right 0) 7) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (In "water") [Cint 9])
    assertEqual "after water 9: " (getSTSIntrpStateEither (Right 1) 16) (stateConf intrp5)
    let intrp6 = after intrp5 (GateValue (Out "ok") [Cint 16])
    assertEqual "after ok 16: " (getSTSIntrpStateEither (Right 0) 16) (stateConf intrp6)
    let intrp7 = after intrp6 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpStateEither (Right 2) 16) (stateConf intrp7)
    -- branch 2: startWithWater
    let intrp8 = after intrp1 (GateValue (In "startWithWater") [Cint 16])
    assertEqual "after startWithWater: " (getSTSIntrpStateEither (Left 2) 16) (stateConf intrp8)
    let intrp9 = after intrp8 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpStateEither (Right 2) 16) (stateConf intrp9)
    return ()

testSeqComposedAtSTS :: Test
testSeqComposedAtSTS = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf stsSeqComposedAt)
    let intrp1 = after stsSeqComposedAt (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrp1)
    -- branch 1: startEmpty
    let intrp2 = after intrp1 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpStateEither (Left 1) 0) (stateConf intrp2)
    -- behavior transitions to sts2
    let intrp3 = after intrp2 (GateValue (In "water") [Cint 7])
    assertEqual "after water 7: " (getSTSIntrpStateEither (Right 1) 7) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (Out "ok") [Cint 7])
    assertEqual "after ok 7: " (getSTSIntrpStateEither (Right 0) 7) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (In "water") [Cint 9])
    assertEqual "after water 9: " (getSTSIntrpStateEither (Right 1) 16) (stateConf intrp5)
    let intrp6 = after intrp5 (GateValue (Out "ok") [Cint 16])
    assertEqual "after ok 16: " (getSTSIntrpStateEither (Right 0) 16) (stateConf intrp6)
    let intrp7 = after intrp6 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpStateEither (Right 2) 16) (stateConf intrp7)
    -- branch 2: startWithWater
    let intrp8 = after intrp1 (GateValue (In "startWithWater") [Cint 16])
    assertEqual "after startWithWater: " (getSTSIntrpStateEither (Left 2) 16) (stateConf intrp8)
    let intrp9 = after intrp8 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpStateEither (Right 2) 16) (stateConf intrp9)
    return ()

{- |
    Merging at location 0 of stsPrelude, which is not sink. In this example, alphabets are disjoint although
    variables are not.
-}
testSequentiallyAtNonSinkLocation :: Test
testSequentiallyAtNonSinkLocation = TestCase $ do
    let intrpr0 = interpretSTS (sequentiallyAt stsPrelude [0] stsExampleFL) stsExampleInitAssign
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrpr0)
    let intrp1 = after intrpr0 (GateValue (Out "error") [])
    assertEqual "after error, stsPrelude's own transition at location 0 still works: " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrp1)
    let intrp2 = after intrp1 (GateValue (In "water") [Cint 7])
    assertEqual "after water 7, entering stsExample directly from location 0: " (getSTSIntrpStateEither (Right 1) 7) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (Out "ok") [Cint 7])
    assertEqual "after ok 7: " (getSTSIntrpStateEither (Right 0) 7) (stateConf intrp3)
    -- the transition is not allowed; once behavior moves to the second sts, actions in the first one are no longer allowed
    let intrp4 = after intrp3 (GateValue (Out "error") [])
    assertEqual "after error: " forbidden (stateConf intrp4)
    return ()

-- Two STS that share the same input action ("step") but specify different guards for it: [3,5] and [1,3], so they
-- overlap at exactly 3.
stsGuardedA :: IOSTS FreeLattice Integer String String
stsGuardedA =
    let p = sVar pvar :: Expr Integer
        step = SymInteract (In "step") [pvar]
        outA = SymInteract (Out "outA") []
        stepGuard = 3 .<= p .&& p .<= 5
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc stepGuard noAssignment, 1))]
            1 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.empty
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, outA]) switches

stsGuardedB :: IOSTS FreeLattice Integer String String
stsGuardedB =
    let p = sVar pvar :: Expr Integer
        step = SymInteract (In "step") [pvar]
        outA = SymInteract (Out "outA") []
        outB = SymInteract (Out "outB") []
        stepGuard = 1 .<= p .&& p .<= 3
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc stepGuard noAssignment, 1))]
            1 -> Map.fromList [(outB, ordReturn (stsTLoc sTrue noAssignment, 2)), (outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.empty
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, outA, outB]) switches

{- |
    Sequentially composing stsGuardedA and stsGuardedB at location 0 of stsGuardedA, which already has a "step"
    transition: stsGuardedA's own "step" (guarded by [3,5]) and stsGuardedB's copied "step" (guarded by [1,3]) are
    both genuinely specified, so they are conjuncted with '(/\)'. Where only one guard holds, that branch's
    destination is used as-is (the other branch reduces to 'underspecified', the identity of '(/\)'); where both
    guards hold (value 3), the merged configuration requires both destinations at once.
-}
testSequentiallyAtSameAction :: Test
testSequentiallyAtSameAction = TestCase $ do
    let intrpr0 = interpretSTS (sequentiallyAt stsGuardedA [0] stsGuardedB) stsExampleInitAssign
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrpr0)
    let intrp1 = after intrpr0 (GateValue (In "step") [Cint 4])
    assertEqual "after step 4, only stsGuardedA's guard holds: " (getSTSIntrpStateEither (Left 1) 0) (stateConf intrp1)
    let intrp2 = after intrpr0 (GateValue (In "step") [Cint 1])
    assertEqual "after step 1, only stsGuardedB's guard holds: " (getSTSIntrpStateEither (Right 1) 0) (stateConf intrp2)
    -- satisfies both guards: the merged configuration conjunctively requires both destinations
    let intrp3 = after intrpr0 (GateValue (In "step") [Cint 3])
    assertEqual "after step 3, both guards hold: "
        (getSTSIntrpStateEither (Left 1) 0 /\ getSTSIntrpStateEither (Right 1) 0) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (Out "outA") [])
    assertEqual "after outA: "
        (getSTSIntrpStateEither (Left 2) 0 /\ getSTSIntrpStateEither (Right 2) 0) (stateConf intrp4)
    let intrp5 = after intrp3 (GateValue (Out "outB") [])
    assertEqual "after outB: " forbidden (stateConf intrp5) -- only allowed by one of the automata
    return ()

{- |
    'stsPrelude' composed with itself via 'selfSequentiallyAt'\/'(|>>)'
-}
stsSelfSeqComposed :: STSIntrp FreeLattice Integer (IOAct String String)
stsSelfSeqComposed = interpretSTS (stsPrelude |>> stsPrelude) stsExampleInitAssign

stsSelfSeqComposedAt :: STSIntrp FreeLattice Integer (IOAct String String)
stsSelfSeqComposedAt = interpretSTS (selfSequentiallyAt stsPrelude [1,2] stsPrelude) stsExampleInitAssign

stsSelfSeqComposedAtOne :: STSIntrp FreeLattice Integer (IOAct String String)
stsSelfSeqComposedAtOne = interpretSTS (selfSequentiallyAt stsPrelude [1] stsPrelude) stsExampleInitAssign

testSelfSeqComposed :: Test
testSelfSeqComposed = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsSelfSeqComposed)
    let intrp1 = after stsSelfSeqComposed (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpState' 0 0) (stateConf intrp1)
    let intrp2 = after intrp1 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpState' 1 0) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpState' 0 0) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (In "startWithWater") [Cint 7])
    assertEqual "after startWithWater 7: " (getSTSIntrpState' 2 7) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpState' 1 7) (stateConf intrp5)
    return ()

-- sequentially composing with |>> and selfSequentiallyAt (pointing to all sink locations) should yield the same result.
testSelfSeqComposedAt :: Test
testSelfSeqComposedAt = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsSelfSeqComposed)
    let intrp1 = after stsSelfSeqComposed (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpState' 0 0) (stateConf intrp1)
    let intrp2 = after intrp1 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpState' 1 0) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpState' 0 0) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (In "startWithWater") [Cint 7])
    assertEqual "after startWithWater 7: " (getSTSIntrpState' 2 7) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpState' 1 7) (stateConf intrp5)
    return ()

testSelfSeqComposedAtOne :: Test
testSelfSeqComposedAtOne = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsSelfSeqComposedAtOne)
    let intrp1 = after stsSelfSeqComposedAtOne (GateValue (Out "error") [])
    assertEqual "after error: " (getSTSIntrpState' 0 0) (stateConf intrp1)
    let intrp2 = after intrp1 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpState' 1 0) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (In "startEmpty") [])
    assertEqual "after startEmpty: " (getSTSIntrpState' 1 0) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (In "startWithWater") [Cint 7])
    assertEqual "after startWithWater 7: " (getSTSIntrpState' 2 7) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (Out "error") [])
    assertEqual "after startEmpty: " forbidden (stateConf intrp5)
    return ()

testPrintSelfSeqComposedSTS :: Test
testPrintSelfSeqComposedSTS = TestCase $ assertBool failureMessage (expected == actual)
    where
    failureMessage = "print of STS does not match, expected:" ++ expected ++ "but received:" ++ actual
    actual = "\n" ++ prettyPrintIntrp stsSelfSeqComposed ++ "\n"
    expected = [QQ.r|
current state configuration: (0,{x:=0})
initial location configuration: 0
locations: 0, 1, 2
transitions:
0  ――?"startEmpty" []⟶  (True, {},1)
0  ――?"startWithWater" [p:Int]⟶  (True, {x:=(p+x)},2)
0  ――!"error" []⟶  (True, {},0)
1  ――?"startEmpty" []⟶  (True, {},1)
1  ――?"startWithWater" [p:Int]⟶  (True, {x:=(p+x)},2)
1  ――!"error" []⟶  (True, {},0)
2  ――?"startEmpty" []⟶  (True, {},1)
2  ――?"startWithWater" [p:Int]⟶  (True, {x:=(p+x)},2)
2  ――!"error" []⟶  (True, {},0)
|]
