{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Test.Lattest.Model.STSTest (
    testSTSHappyFlow,
    testSTSHappyFlowLists,
    testSTSHappyFlowFloat,
    testLatticeCoffeeSTS,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testSTSTestSelection,
    testSTSDataSelectionGuardedInput,
    testLatticeSTS,
    testLatticeSTSQuiescence,
    testSTSPathCondition,
    testBranchingPathCondition,
    testComposedSeTreeStructure,
    testComposedPathCondition,
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
    testSelfSeqComposedAtOne,
    testConjunctionGuardedSTS,
    testDisjunctionGuardedSTS,
    testConjunctionAllGuardedSTS,
    testDisjunctionAllGuardedSTS,
    testPrintTriDisj,
    testErrorDisjOfSTSWithMultpInitStates,
    testPrintPrependOutputChecksDisj,
    testPrintPrependOutputChecksConj,
    testPrependOutputChecksDisj,
    testPrependOutputChecksConj
    )
where

import Prelude hiding (take)
import Data.Constraint.Extras (Has(..))
import Data.GADT.Compare (GEq(..))
import Data.Type.Equality ((:~:)(..))
import Test.HUnit
import Data.Dependent.Sum
import Test.QuickCheck (Gen, Property, forAll, elements, choose, vectorOf, counterexample, (.&&.))
import Data.Maybe(isJust, catMaybes)
import qualified Data.Set as Set
import System.Random(mkStdGen)
import Data.String(IsString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import System.FilePath ((</>), takeDirectory)
import System.Directory (createDirectoryIfMissing)
import qualified Text.RawString.QQ as QQ
import qualified Lattest.Adapter.Adapter as Adapter
import Lattest.Adapter.StandardAdapters(pureAdapter, pureMealyAdapter)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(runSMTTester, Verdict(..))
import Lattest.Model.Automaton(after, After, AutIntrpr, stateConf,automaton,IntrpState(..),prettyPrintIntrp,stsTLoc,STStdest,alphabet,syntacticAutomaton,prependOutputChecks,CheckLoc(..))
import Lattest.Model.StandardAutomata(interpretSTS, IOSTS, STSIntrp, interpretSTSQuiescentInputAttemptConcrete, sequentiallyAt, (|>), selfSequentiallyAt, (|>>), (//\\), (\\//), conjunctionAll, disjunctionAll)
import Lattest.Model.Alphabet(IOAct(..), Suspended(..), SuspendedIF, SuspendedIFGateValue, δ, SymInteract(..),GateValue(..), gateValueAsIOAct,toIOGateValue, InputAttempt(..), IOSymInteract)
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
import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum (DSum(..))
 -- 'Var' would clash with 'Algebra.Lattice.Free.Var' used by prettySeTree
import qualified Lattest.SMT as SMT

pvar :: Variable Integer
pvar = Variable "p" IntType
qvar :: Variable Integer
qvar = Variable "q" IntType
xvar :: Variable Integer
xvar = Variable "x" IntType

stsExampleInitAssign :: Valuation
stsExampleInitAssign = Valuation $ DMap.singleton xvar (Val 0)

stsExample :: IOSTS Det Integer String String
stsExample =
    let p = sVar pvar
        x = sVar xvar
        water = SymInteract (In "water") [Some pvar]
        ok = SymInteract (Out "ok") [Some pvar]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = return 0
        switches = \case
            0 -> Map.fromList [(water, pure (stsTLoc waterGuard waterAssign, 1)),
                                (coffee, pure (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, pure (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches
stsExampleIntrpr :: STSIntrp Det Integer (IOAct String String)
stsExampleIntrpr = interpretSTS stsExample stsExampleInitAssign

getSTSIntrpState :: Integer ->  Integer -> Det (IntrpState Integer)
getSTSIntrpState loc val = pure $ IntrpState loc $ Valuation $ DMap.singleton (Variable "x" IntType) (Val val)

{- |
    Takes a tuple of description, STS model, gate-parameter value pair and expected state and computes
    STS `after` interaction, asserting that the resulting state configuration matches the expected one.
-}
assertAfter :: (After m loc q t tdest act, Ord (m q), Ord q, Show (m q)) =>
    String -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (AutIntrpr m loc q t tdest act)
assertAfter msg intrp act expected = do
    let intrp' = after intrp act
    assertEqual msg expected (stateConf intrp')
    return intrp'

testSTSHappyFlow :: Test
testSTSHappyFlow = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState 0 0) (stateConf stsExampleIntrpr)
    intrp2 <- assertAfter "after water 7: " stsExampleIntrpr (GateValue (In "water") [Some $ CInt 7]) (getSTSIntrpState 1 7)
    intrp3 <- assertAfter "after ok 7: " intrp2 (GateValue (Out "ok") [Some $ CInt 7]) (getSTSIntrpState 0 7)
    intrp4 <- assertAfter "after water 9: " intrp3 (GateValue (In "water") [Some $ CInt 9]) (getSTSIntrpState 1 16)
    intrp5 <- assertAfter "after ok 16: " intrp4 (GateValue (Out "ok") [Some $ CInt 16]) (getSTSIntrpState 0 16)
    _ <- assertAfter "after coffee: " intrp5 (GateValue (Out "coffee") []) (getSTSIntrpState 2 16)
    return ()

pvar' :: Variable [Integer]
pvar' = Variable "p" $ ListType IntType
xvar' :: Variable [[Integer]]
xvar' = Variable "x" $ ListType $ ListType IntType
mapvar1 :: Variable [Integer]
mapvar1 = Variable "map1" $ ListType IntType
mapvar2 :: Variable Integer
mapvar2 = Variable "map2" IntType

stsExampleInitAssign' :: Valuation
stsExampleInitAssign' = Valuation $ DMap.singleton xvar' (Val [[1,2,3],[4,5,6]])

stsExample' :: IOSTS Det Integer String String
stsExample' =
    let p = sVar pvar'
        x = sVar xvar'
        water = SymInteract (In "water") [Some pvar']
        ok = SymInteract (Out "ok") [Some pvar']
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .< sLength p .&& sLength p .<= 10
        waterAssign = assignment [xvar' =: sMap mapvar1 (sMap mapvar2 (sLength p + sVar mapvar2) $ sVar mapvar1) x] -- map (map (+length p)) x
        okGuard = sHead (sHead x) .== sLength p
        coffeeGuard = sHead (sHead x) .>= 15
        initConf = return 0
        switches = \case
            0 -> Map.fromList [(water, pure (stsTLoc waterGuard waterAssign, 1)),
                                (coffee, pure (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, pure (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches
stsExampleIntrpr' :: STSIntrp Det Integer (IOAct String String)
stsExampleIntrpr' = interpretSTS stsExample' stsExampleInitAssign'

getSTSIntrpState'' :: Integer -> [[Integer]] -> Det (IntrpState Integer)
getSTSIntrpState'' loc val = pure $ IntrpState loc $ Valuation $ DMap.singleton (Variable "x" $ ListType $ ListType IntType) (Val val)

testSTSHappyFlowLists :: Test
testSTSHappyFlowLists = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState'' 0 [[1,2,3],[4,5,6]]) (stateConf stsExampleIntrpr')
    let intrp2 = after stsExampleIntrpr' (GateValue (In "water") [list @Integer [1,2,3,4,5,6,7]])
    assertEqual "after water 7: " (getSTSIntrpState'' 1 [[8,9,10],[11,12,13]]) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (Out "ok") [list @Integer [1,2,3,4,5,6,7,8]])
    assertEqual "after ok 7: " (getSTSIntrpState'' 0 [[8,9,10],[11,12,13]]) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (In "water") [list @Integer [1,2,3,4,5,6,7,8,9]])
    assertEqual "after water 9: " (getSTSIntrpState'' 1 [[17,18,19],[20,21,22]]) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (Out "ok") [list @Integer [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]])
    assertEqual "after ok 16: " (getSTSIntrpState'' 0 [[17,18,19],[20,21,22]]) (stateConf intrp5)
    let intrp6 = after intrp5 (GateValue (Out "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpState'' 2 [[17,18,19],[20,21,22]]) (stateConf intrp6)
    return ()

testErrorThrowingGates :: Test
testErrorThrowingGates = TestCase $ do
    let intrp1 = after stsExampleIntrpr (GateValue (Out "water") [int 7])
    assertThrowsError "gate not in STS alphabet" (stateConf intrp1)
    let intrp2 = after stsExampleIntrpr (GateValue (In "water") [])
    assertThrowsError "nr of values unequal to nr of parameters: 0 values and 1 variables" (stateConf intrp2)
    let intrp3 = after stsExampleIntrpr (GateValue (In "water") [bool True])
    assertThrowsError "type of variable and value do not match. Variables: [p:Int], Values: [True]" (stateConf intrp3)

testSTSUnHappyFlow :: Test
testSTSUnHappyFlow = TestCase $ do
    _ <- assertAfter "after ok: " stsExampleIntrpr (GateValue (Out "ok") [Some $ CInt 0]) forbidden -- output not enabled
    _ <- assertAfter "after water 11: " stsExampleIntrpr (GateValue (In "water") [Some $ CInt 11]) underspecified -- value for input does not satisfy guard
    _ <- assertAfter "after coffee: " stsExampleIntrpr (GateValue (Out "coffee") []) forbidden -- value of variable does not satisfy guard
    return ()

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
    [(GateValue (In "water") [int p], (L1, x+p)) | p <- [1..10]] ++ [(GateValue (Out "coffee") [], (L2, 0)) | x > 15]
tExampleCorrect (L1, x) = Map.fromList  [(GateValue (Out "ok") [int x], (L0, x))]
tExampleCorrect (L2, _) = mempty
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
        -- TODO: inp, out seem to be the same as inpL, outL?
          inp "water" [int 1],
          out "ok"    [int 1],
          inp "water" [int 1],
          out "ok"    [int 2],
          GateValue δ [],
          inp "water" [int 1],
          out "ok"    [int 3],
          inp "water" [int 1],
          outL "ok"   [int 4],
          inpL "water" [int 1],
          outL "ok"    [int 5],
          GateValue δ [],
          inpL "water" [int 1],
          outL "ok"    [int 6],
          inpL "water" [int 1],
          outL "ok"    [int 7],
          inpL "water" [int 1],
          outL "ok"    [int 8],
          inpL "water" [int 1],
          outL "ok"    [int 9],
          inpL "water" [int 1],
          outL "ok"    [int 10],
          inpL "water" [int 1],
          outL "ok"    [int 11],
          inpL "water" [int 1],
          outL "ok"    [int 12],
          inpL "water" [int 1],
          outL "ok"    [int 13],
          inpL "water" [int 1],
          outL "ok"    [int 14],
          inpL "water" [int 1],
          outL "ok"    [int 15],
          inpL "water" [int 1],
          outL "ok"    [int 16],
          outL "coffee" [],
          GateValue δ [],
          GateValue δ []
          ]
    let checkExample = go 0 0 exampleObserved
    assertEqual ("expected conformal trace like " <> show exampleObserved <> ", got " <> show observed) checkObserved checkExample
    assertEqual "expected pass " Pass verdict
    where
    inpL g = GateValue (In (InputAttempt (g, True)))
    outL g = GateValue (Out (OutSusp g))
    go :: Int -> Integer -> [SuspendedIFGateValue String String] -> (Int, Integer)
    go ds waterlevel [] = (ds, waterlevel)
    go ds waterlevel (GateValue (Out Quiescence) []:os) = go (ds+1) waterlevel os
    go ds waterlevel gv@(GateValue x y:os)
      | x == In (InputAttempt ("water", True))
      , [Some (CInt w)] <- y = go ds (waterlevel + w) os
      | x == Out (OutSusp "ok")
      , [Some (CInt w)] <- y
      , w == waterlevel = go ds waterlevel os
      | x == Out (OutSusp "coffee")
      , [] <- y
      , waterlevel > 15 = go ds waterlevel os
      | otherwise = error $ "wrong gatevalue: " <> show gv

pvarf :: Variable Double
pvarf = Variable "p" FloatType
xvarf :: Variable Double
xvarf = Variable "x" FloatType

stsExampleInitAssignFloat :: Valuation
stsExampleInitAssignFloat = Valuation $ DMap.singleton xvarf (Val 0.0)

stsExampleFloat :: IOSTS FreeLattice Integer String String
stsExampleFloat =
    let p = sVar pvarf :: Expr Double
        x = sVar xvarf :: Expr Double
        water = SymInteract (In "water") [Some pvarf]
        ok = SymInteract (Out "ok") [Some pvarf]
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
getSTSIntrpStateFloat loc val = disjunction [IntrpState loc $ Valuation $ DMap.singleton (Variable "x" FloatType) (Val val)]

testSTSHappyFlowFloat :: Test
testSTSHappyFlowFloat = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpStateFloat 0 0.0) (stateConf stsExampleIntrprFloat)
    intrp2 <- assertAfter "after water 7.5: " stsExampleIntrprFloat (GateValue (In "water") [Some $ CFloat (7.5 :: Double)]) (getSTSIntrpStateFloat 1 (7.5 :: Double))
    intrp3 <- assertAfter "after ok 7.5: " intrp2 (GateValue (Out "ok") [Some $ CFloat 7.5]) (getSTSIntrpStateFloat 0 (7.5 :: Double))
    intrp4 <- assertAfter "after water 8.5: " intrp3 (GateValue (In "water") [Some $ CFloat 8.5]) (getSTSIntrpStateFloat 1 (16.0 :: Double))
    intrp5 <- assertAfter "after ok 16.0: " intrp4 (GateValue (Out "ok") [Some $ CFloat 16.0]) (getSTSIntrpStateFloat 0 (16.0 :: Double))
    _ <- assertAfter "after coffee: " intrp5 (GateValue (Out "coffee") []) (getSTSIntrpStateFloat 2 (16.0 :: Double))
    return ()


stsExample2 :: (IOSTS FreeLattice Integer String String, IOSTS FreeLattice Integer String String)
stsExample2 =
    let p = sVar pvar
        x = sVar xvar
        water = SymInteract (In "water") [Some pvar]
        ok = SymInteract (Out "ok") [Some pvar]
        coffee = SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 4
        waterGuard1 = 4 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        initConf = atom 0
        switches = \case
            0 -> Map.fromList [(water, atom (stsTLoc waterGuard waterAssign, 1) /\ atom (stsTLoc waterGuard1 waterAssign, 2) )]
            1 -> Map.fromList [(ok, atom (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.fromList [(ok, atom (stsTLoc okGuard noAssignment, 0))]
        initConf2 = atom 0 /\ atom 2
        switches2 = \case
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
getSTSValuation val = Valuation $ DMap.singleton (Variable "x" IntType) (Val val)

getSTSIntrpState2 :: Integer ->  Integer -> FreeLattice (IntrpState Integer)
getSTSIntrpState2 loc val = atom (IntrpState loc $ getSTSValuation val)

-- NOTE: Automaton a conjuncts the switches that start from the initial location, while automaton b 
-- conjuncts the initial states.
testLatticeCoffeeSTS :: Test
testLatticeCoffeeSTS = TestCase $ do
     assertEqual "\ninitial state " (getSTSIntrpState2 0 0) (stateConf stsExampleIntrpr2a)
     assertEqual "\ninitial state " (getSTSIntrpState2 0 0 /\ getSTSIntrpState2 2 0) (stateConf stsExampleIntrpr2b)
     intrp2a <- assertAfter "2a after water 3: " stsExampleIntrpr2a (GateValue (In "water") [Some $ CInt 3]) (getSTSIntrpState2 1 3)
     intrp2b <- assertAfter "2b after water 3: " stsExampleIntrpr2b (GateValue (In "water") [Some $ CInt 3]) (getSTSIntrpState2 1 3)
     intrp3a <- assertAfter "2a after ok 3: " intrp2a (GateValue (Out "ok") [Some $ CInt 3]) (getSTSIntrpState2 0 3)
     intrp3b <- assertAfter "2b after ok 3: " intrp2b (GateValue (Out "ok") [Some $ CInt 3]) (getSTSIntrpState2 0 3)
     intrp4a <- assertAfter "3a after water 4: " intrp3a (GateValue (In "water") [Some $ CInt 4]) (getSTSIntrpState2 1 7 /\ getSTSIntrpState2 2 7)
     -- NOTE: Merging only the initial states drops transitions that loop back to the initial state.
     intrp4b <- assertAfter "3b after water 4: " intrp3b (GateValue (In "water") [Some $ CInt 4]) (getSTSIntrpState2 1 7)
     intrp5a <- assertAfter "4a after ok 7: " intrp4a (GateValue (Out "ok") [Some $ CInt 7]) (getSTSIntrpState2 0 7)
     intrp5b <- assertAfter "4b after ok 7: " intrp4b (GateValue (Out "ok") [Some $ CInt 7]) (getSTSIntrpState2 0 7)
     _ <- assertAfter "5a after water 5: " intrp5a (GateValue (In "water") [Some $ CInt 5]) (getSTSIntrpState2 2 12)
     _ <- assertAfter "5b after water 5: " intrp5b (GateValue (In "water") [Some $ CInt 5]) underspecified
     return ()


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
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (startType "start") [Some pvar]
        end = SymInteract (endType "end") [Some pvar, Some qvar]
        done = SymInteract (Out "done") []
        initConf = pure 0 :: FreeLatticeSlow Integer
        guardStart = 1 .< p .&& p .< 3
        guardEnd1 = p .+ q .== x .+ 2
        guardEnd2 = p .- q .== x
        assignX = assignment [xvar =: p]
        switches =
            if splitFirst
                then \case
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1) `comp` pure (stsTLoc guardStart assignX, 2))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd1 noAssignment, 3))]
                        2 -> Map.fromList [(end, pure (stsTLoc guardEnd2 noAssignment, 4))]
                        3 -> Map.fromList [(done, pure (stsTLoc sTrue noAssignment, 5))]
                        4 -> Map.fromList [(done, pure (stsTLoc sTrue noAssignment, 5))]
                        5 -> Map.empty
                else \case
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
t1 startType _ p1 _ _ 0 = Map.fromList [(GateValue (startType "start") [int p1], 1)]
t1 _ endType _ p2 q2 1 = Map.fromList [(GateValue (endType "end") [int p2, int q2], 2)]
t1 _ _ _ _ _ 2 = Map.fromList [(GateValue (Out "done") [], 3)]
t1 _ _ _ _ _ 3 = Map.empty
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
                startType' "start" [int p1],
                endType' "end" [int p2, int q2],
                out "done" [],
                GateValue δ []
                ] observed
        Just t -> do
            assertEqual (testName ++ ": expected Fail after " ++ show observed) Fail verdict
            assertEqual (testName ++ ": expected nonconformal trace") t observed
inp :: i -> [Some Constant] -> GateValue (IOAct (InputAttempt i) o)
inp g = GateValue (In (InputAttempt (g, True)))
inpf :: i -> [Some Constant] -> GateValue (IOAct (InputAttempt i) o)
inpf g = GateValue (In (InputAttempt (g, False)))
out :: o -> [Some Constant] -> GateValue (IOAct i (Suspended o))
out g = GateValue (Out (OutSusp g))

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
    testLatticeSTSParameterized "a4" inputThenOutput (\/) 2 4 4 (Just [inp "start" [int 2], out "end" [int 4, int 4]]), -- fail: output (4,4) satisfies neither guard
    testLatticeSTSParameterized "a5" inputThenOutput (/\) 2 2 2 (Just [inp "start" [int 2], out "end" [int 2, int 2]]), -- fail: output (2,2) satisfies the first guards, but not both
    testLatticeSTSParameterized "a6" inputThenOutput (/\) 2 4 2 (Just [inp "start" [int 2], out "end" [int 4, int 2]]), -- fail: output (4,2) satisfies the second guards, but not both
    testLatticeSTSParameterized "a7" inputThenOutput (/\) 2 4 4 (Just [inp "start" [int 2], out "end" [int 4, int 4]]), -- fail: output (4,4) satisfies neither guard
    testLatticeSTSParameterized "a8" inputThenOutput (/\) 2 3 1 Nothing, -- pass: output (3,1) satisfies both guards

    testLatticeSTSParameterized "b1" outputThenInput (\/) 2 3 1 Nothing, -- pass: (3,1) is the only input that matches both guards, so is the only specified input overall, thus will be tested and observed
    testLatticeSTSParameterized "b2" outputThenInput (\/) 2 5 5 (Just [out "start" [int 2], inpf "end" [int 3, int 1]]) -- pass: (3,1) is the only input that matches both guards, so is the only specified input overall, thus will be tested but refused
     -- FIXME the next tests are actually unsound: it will pass under the assumption that the test selection (SMT solver) will pick the last two number parameters as input,
     -- but if not, the test case will incorrectly fail. To fix this, change the implementation to accept any (p,q) satisfying any of the guards 〚p+q=4〛 or 〚p-q=2〛
    --testLatticeSTSParameterized "b3" outputThenInput (/\) 2 0 (-2) Nothing, -- pass: (0,-2) is an input that matches one of the guards, so is specified, thus may be tested and in that case will be observed
    --testLatticeSTSParameterized "b4" outputThenInput (/\) 2 5 5 (Just [out "start" [int 2], inpf "end" [int 0, CInt (-2)]]) -- fail: the tester will pick an input that matches one of the guards, but will be rejected by the implementation
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
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (In "start") [Some pvar]
        end = SymInteract (Out "end") [Some pvar, Some qvar]
        initConf = pure 0 :: FreeLatticeSlow Integer
        guardStart = 1 .< p .&& p .< 3
        guardEnd = p .+ q .== p .+ q .+ x
        assignX = assignment [xvar =: p]
        switches = \case
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
tq startType p 0 = Map.fromList [(GateValue (startType "start") [int p], 1)]
tq _ _ 1 = Map.empty
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
                inp "start" [int 2],
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
                inp "start" [int 2],
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
                inp "start" [int 2],
                out "end" [int 42, int 42]
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
    let p = sVar pvar
        q = sVar qvar
        x = sVar xvar
        start = SymInteract (In "start") [Some pvar]
        end = SymInteract (Out "end") [Some pvar, Some qvar]
        initConf = pure 0 :: FreeLatticeSlow Integer
        guardStart = 1 .< p .&& p .< 3
        guardEnd1 = p .+ q .== x .+ 2
        guardEnd2 = p .+ q .== x
        assignX = assignment [xvar =: p]
        switches =
            if splitFirst
                then \case
                        0 -> Map.fromList [(start, pure (stsTLoc guardStart assignX, 1) /\ pure (stsTLoc guardStart assignX, 2))]
                        1 -> Map.fromList [(end, pure (stsTLoc guardEnd1 noAssignment, 3))]
                        2 -> Map.fromList [(end, pure (stsTLoc guardEnd2 noAssignment, 3))]
                        3 -> Map.empty
                else \case
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
                inp "start" [int 2],
                GateValue δ []
                ] observed

{- |
    End-to-end regression test for the data test selector picking input values that violate a guard.
-}
data Divisibility = Prime | Divisible deriving (Eq, Ord, Show)

ivar :: Variable Integer
ivar = Variable "i" IntType
jvar :: Variable Integer
jvar = Variable "j" IntType

guardedInputSTS :: IOSTS Det Bool Divisibility ()
guardedInputSTS =
    let i = sVar ivar :: Expr Integer
        j = sVar jvar :: Expr Integer
        echo = SymInteract (Out ()) [Some jvar]
        echoAssign = assignment [ivar =: 1 .+ j]
        yes = SymInteract (In Prime) [Some jvar]
        yesGuard = i .% 2 .== 0 .&& j .== i .- 1
        yesAssign = assignment [ivar =: i .+ j]
        no = SymInteract (In Divisible) [Some jvar]
        noGuard = i .% 2 .== 1 .&& j .== i .- 1
        noAssign = assignment [ivar =: i .+ j]
        initConf = return False
        switches True = Map.singleton echo $ pure (stsTLoc sTrue echoAssign, False)
        switches False = Map.fromList
            [ (yes, pure (stsTLoc yesGuard yesAssign, True))
            , (no,  pure (stsTLoc noGuard  noAssign,  True))]
    in automaton initConf (Set.fromList [echo, yes, no]) switches

guardedInputInitAssign :: Valuation
guardedInputInitAssign = Valuation $ DMap.singleton ivar (Val 42)

guardedInputModel :: STSIntrp Det Bool (IOAct Divisibility ())
guardedInputModel = interpretSTS guardedInputSTS guardedInputInitAssign

testSTSDataSelectionGuardedInput :: Test
testSTSDataSelectionGuardedInput = TestCase $ do
    -- simple adapter that echos its input and then emits an output carrying the same value
    adap <- pureMealyAdapter
        (\() _ -> ())
        (\_ (GateValue m d) -> [GateValue (In m) d, GateValue (Out ()) d])
        ()
    let nrSteps = 2
        randomSeed = 456
        testSelector = randomDataTestSelectorFromSeed randomSeed `untilCondition` stopAfterSteps nrSteps
                        `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    (verdict, ((observed, _), _)) <- runSMTTester guardedInputModel testSelector adap
    assertEqual ("expected the selector to pick the only guard-satisfying input ?Prime [41], got " <> show observed)
        [ GateValue (In Prime) [Some $ CInt 41]
        , GateValue (Out ()) [Some $ CInt 41]
        ] observed
    assertEqual ("expected Pass after " <> show observed) Pass verdict

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

-- TODO: put these in a let or where
p, q, x :: Expr Integer
p = sVar pvar
q = sVar qvar
x = sVar xvar
water, ok, coffee :: SymInteract (IOAct String String)
water = SymInteract (In "water") [Some pvar]
ok = SymInteract (Out "ok") [Some pvar]
coffee = SymInteract (Out "coffee") []

-- Interactions and STS for the branching tests, using the CNF lattice monad (FreeLattice).
-- Input variants (unsatisfied guard -> underspecified/top) and output variants (unsatisfied guard -> forbidden/bottom).
gateA = SymInteract (In "a") [Some pvar, Some qvar]
gateB = SymInteract (In "b") [Some pvar, Some qvar]
gateAo = SymInteract (Out "a") [Some pvar, Some qvar]
gateBo = SymInteract (Out "b") [Some pvar, Some qvar]

branchInitAssign :: Valuation
branchInitAssign = Valuation $ DMap.singleton xvar (Val 0)

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
inGate = SymInteract (In "a") [Some pvar]
outGate :: SymInteract (IOAct String String)
outGate = SymInteract (Out "x") [Some pvar]

treeSTS :: IOSTS FreeLattice Integer String String
treeSTS =
    let switches loc = case loc of
            0 -> Map.fromList [(inGate, ordReturn (stsTLoc (p .>= -20) (assignment [xvar =: p]), 1) /\ ordReturn (stsTLoc (p .<= 20) (assignment [xvar =: p]), 2))]
            1 -> Map.fromList [(outGate, ordReturn (stsTLoc (x .% 2 .== 0) (assignment []), 3) \/ ordReturn (stsTLoc (x .% 3 .== 0) (assignment []), 3))]
            2 -> Map.fromList [(outGate, ordReturn (stsTLoc (x .* p .>= 0) (assignment []), 3))]
            _ -> Map.empty
    in automaton (ordReturn 0 :: FreeLattice Integer) (Set.fromList [inGate, outGate]) switches

milkvar :: Variable Bool
milkvar = (Variable "milk" BoolType)
milk = sVar milkvar
a,b,tea,espresso,take :: SymInteract (IOAct String String)
a = SymInteract (In "a") []
b = SymInteract (In "b") [Some pvar]
tea = SymInteract (Out "tea") [Some pvar]
espresso = SymInteract (Out "esp") [Some pvar, Some milkvar]
take = SymInteract (In "take") []

composedCoffeeMachineAssign :: Valuation
composedCoffeeMachineAssign = Valuation $ DMap.singleton xvar (Val 0)

composedCoffeeMachine :: IOSTS FreeLatticeSlow String String String
composedCoffeeMachine =
    let initConf = ordReturn "a0" /\ ordReturn "b0" /\ ordReturn "c0" /\ ordReturn "d0":: FreeLatticeSlow String
        asTransition = \q -> (stsTLoc sTrue noAssignment, q)
        switches = \q -> case q of
            "a0" -> Map.fromList [(a, ordReturn (stsTLoc (x .>= 2) noAssignment, "a1"))]
            "a1" -> Map.fromList [(tea, ordReturn (stsTLoc (p .== 2) $ noAssignment, "a2"))]
            "b0" -> Map.fromList [(b, ordReturn (stsTLoc (x .>= p) $ assignment [xvar =: p], "b1"))] -- this one's tricky: in state b0, x was the amount of water still available. In state b1, it becomes the requested size of the coffee
            "b1" -> Map.fromList [(espresso, ordReturn (stsTLoc (p .== x) $ noAssignment, "b2"))]
            "c0" -> Map.fromList [(b, ordReturn (stsTLoc (x .>= p) noAssignment, "c1"))] -- guard duplicated from b0, so c0 (the milk aspect) does not accept an order that b0 would leave underspecified
            "c1" -> Map.fromList [(espresso, ordReturn (stsTLoc (milk) $ noAssignment, "c2"))]
            -- the a/b transitions duplicate a0/b0's guards, so d0 (the loop-back branch) does not accept an order that a0/b0 would leave underspecified
            "d0" -> Map.fromList $ [(water, foldr (/\) underspecified [ordReturn (stsTLoc (x .< 10) $ assignment [xvar =: x .+ p], d) | d <- ["a0", "b0", "c0", "d0"]])] ++ [(a, ordReturn (stsTLoc (x .>= 2) noAssignment, "d1")), (b, ordReturn (stsTLoc (x .>= p) noAssignment, "d1"))]
            "d1" -> Map.fromList [(output, ordReturn (stsTLoc sTrue $ assignment [xvar =: x .- p], "d2")) | output <- [tea, espresso]]
            "d2" -> Map.fromList [(take, asTransition <#> initConf)]
            -- terminal locations (a2, b2, c2): map every interaction explicitly to unspecified
            _ -> Map.fromList [(gate, underspecified) | gate <- [water, a, b, tea, espresso, take]]
    in automaton initConf (Set.fromList [water,a,b,tea,espresso,take]) switches
composedCoffeeMachineIntrpr :: STSIntrp FreeLatticeSlow String (IOAct String String)
composedCoffeeMachineIntrpr = interpretSTS composedCoffeeMachine composedCoffeeMachineAssign

-- Pretty-print the entire current intermediate symbolic-execution tree (`Solve.seTree`), up to a given depth. The
-- configuration monad is fixed to `FreeLatticeSlow` so that we can render its ∧/∨/⊤/⊥ structure directly (no
-- normalization or deduplication), interleaved with the step / if-then-else structure of the tree.
prettySeTree :: Int
             -> FreeLatticeSlow (Solve.SETree FreeLatticeSlow (IOSymInteract String String))
             -> String
prettySeTree depth t0 = unlines ("configuration:" : goConf "  " (goTree depth) t0)
    where
    goTree :: Int -> String -> Solve.SETree FreeLatticeSlow (IOSymInteract String String) -> [String]
    goTree d ind (Solve.SETree cs)
        | d <= 0    = [ind ++ "… (depth limit)"]
        | otherwise = concatMap (goEntry d ind) (Map.toList cs)
    goEntry :: Int -> String -> (IOSymInteract String String, FreeLatticeSlow (Solve.SEIte (FreeLatticeSlow (Solve.SETree FreeLatticeSlow (IOSymInteract String String))))) -> [String]
    goEntry d ind (i, medge) =
        (ind ++ "step " ++ show i ++ ", branches:") : goConf (ind ++ "  ") (goIte (d-1)) medge
    goIte :: Int -> String -> Solve.SEIte (FreeLatticeSlow (Solve.SETree FreeLatticeSlow (IOSymInteract String String))) -> [String]
    goIte d ind (Solve.SEIte g thn els) =
           [ind ++ "if " ++ show g ++ " then"]
        ++ goConf (ind ++ "    ") (goTree d) thn
        ++ [ind ++ "else:"]
        ++ goConf (ind ++ "    ") (goTree d) els
    -- render a FreeLatticeSlow layer, recursing into each atom via `sub`. Chains of the same operator are flattened
    -- into an n-ary ∧/∨, but no merging of equal subtrees happens.
    goConf :: String -> (String -> x -> [String]) -> FreeLatticeSlow x -> [String]
    goConf ind _   (FreeLatticeSlow Top)    = [ind ++ "⊤ (underspecified)"]
    goConf ind _   (FreeLatticeSlow Bottom) = [ind ++ "⊥ (forbidden)"]
    goConf ind sub (FreeLatticeSlow (Levitate free)) = goFree ind sub free
    goFree ind sub (Algebra.Lattice.Free.Var e) = sub ind e
    goFree ind sub free@(_ :/\: _) =
        let conjuncts = meets free
        in (ind ++ "∧ (" ++ show (length conjuncts) ++ " conjuncts):")
           : concatMap (goOperand ind sub "conjunct") (zip [1 :: Int ..] conjuncts)
    goFree ind sub free@(_ :\/: _) =
        let disjuncts = joins free
        in (ind ++ "∨ (" ++ show (length disjuncts) ++ " disjuncts):")
           : concatMap (goOperand ind sub "disjunct") (zip [1 :: Int ..] disjuncts)
    -- Delimit each operand of an n-ary ∧/∨ with its own header, so the (multi-line) subtrees of sibling conjuncts
    -- do not visually run together.
    goOperand :: String -> (String -> x -> [String]) -> String -> (Int, Free x) -> [String]
    goOperand ind sub label (k, operand) =
        (ind ++ "  " ++ label ++ " " ++ show k ++ ":") : goFree (ind ++ "    ") sub operand
    meets (x :/\: y) = meets x ++ meets y
    meets other      = [other]
    joins (x :\/: y) = joins x ++ joins y
    joins other      = [other]

-- Show the entire intermediate tree structure (`Solve.seTree`) for the composed coffee machine up to depth 3, as a
-- single golden test. The same tree folds (via `Solve.treeToGuard asDualExpr`/`asExpr`) to the specified/allowed guards.
testComposedSeTreeStructure :: Bool -> Test
testComposedSeTreeStructure regenerate = TestCase $ goldenAssert
    [ goldenCheck regenerate "composed:seTree" (goldenDir </> "composed.setree.txt")
        ("\n" ++ prettySeTree 3 (Solve.seTree composedCoffeeMachineIntrpr))
    ]

-- Snapshot the accumulated symbolic path condition (the actual formula, with SSA-indexed parameters) that
-- `interactsToSpecifiedCondition` (asDualExpr) and `interactsToAllowedCondition` (asExpr) produce, for *every* trace
-- over the composed coffee machine's alphabet up to length 3. One symbolic guard per (condition, trace) encodes all
-- concrete valuations at once, complementing the pointwise checks in testConcreteTraceSpecifiedAllowedCorrespondence.
-- The transition function is total (missing gates map to the implicit location), so every alphabet trace has a guard.
testComposedPathCondition :: Bool -> Test
testComposedPathCondition regenerate = TestCase $ goldenAssert
    [ goldenCheck regenerate "composed:pathCondition" (goldenDir </> "composed.pathcondition.txt")
        ("\n" ++ concatMap render traces)
    ]
    where
    alph = Set.toList $ alphabet $ syntacticAutomaton composedCoffeeMachineIntrpr
    -- all traces over the alphabet up to length 3 (sequence . replicate n = all n-length combinations)
    traces = concatMap (\n -> sequence (replicate n alph)) [0 .. 3 :: Int]
    render tr = unlines
        [ "=== " ++ show tr ++ " ==="
        , "specified: " ++ show (interactsToSpecifiedCondition composedCoffeeMachineIntrpr tr)
        , "allowed:   " ++ show (interactsToAllowedCondition composedCoffeeMachineIntrpr tr)
        , "" ]

-- | One step of a concrete trace: a symbolic interaction together with the concrete values for its parameters.
type ConcreteStep = (IOSymInteract String String, [Some Constant])

-- | The concrete gate value of a step, for feeding to `after`.
stepGateValue :: ConcreteStep -> GateValue (IOAct String String)
stepGateValue (SymInteract g _, vals) = GateValue g vals

-- | Build the valuation that fills the symbolic guards: the parameter `v` of the interaction at trace position `n`
-- appears in the guards as `v_n` (matching `indexVar` in SolveSTS.hs), and is bound here to its concrete value.
traceValuation :: [ConcreteStep] -> Valuation
traceValuation steps = Valuation $ DMap.unions $ zipWith stepConstMap [0..] steps
    where
    stepConstMap :: Int -> ConcreteStep -> DMap.DMap Variable Val
    stepConstMap n (SymInteract _ vars, vals) = DMap.fromList $ zipWith (\(Some var) (Some (Constant t val)) -> has @ExprType var $ case geq (typeOf' var) t of
      Just r@Refl -> indexVar n var :=> withExprConstraints t (Val val)) vars vals
    indexVar 0 var = var
    indexVar n (Variable name t) = Variable (name ++ "_" ++ show n) t

testConcreteTraceSpecifiedAllowedCorrespondence :: Test
testConcreteTraceSpecifiedAllowedCorrespondence = TestList
    [ correspondenceCase "[water 3]"                         -- neither: input, guard x<10 holds (x=0)
        [(water, [Some $ CInt 3])] Indefinite
    , correspondenceCase "[water 3, water 5]"                -- neither: second water still has x=3<10
        [(water, [Some $ CInt 3]), (water, [Some $ CInt 5])] Indefinite
    , correspondenceCase "[water 12, water 5]"               -- underspecified: second water blocked, x=12>=10
        [(water, [Some $ CInt 12]), (water, [Some $ CInt 5])] Underspecified
    , correspondenceCase "[water 6, b 4, esp 4 milk]"        -- neither: esp satisfies p=x (4) and milk
        [(water, [Some $ CInt 6]), (b, [Some $ CInt 4]), (espresso, [Some $ CInt 4, Some $ CBool True])] Indefinite
    , correspondenceCase "[water 6, b 4, esp 5 milk]"        -- forbidden: esp output violates p=x (5/=4)
        [(water, [Some $ CInt 6]), (b, [Some $ CInt 4]), (espresso, [Some $ CInt 5, Some $ CBool True])] Forbidden
    , correspondenceCase "[water 6, b 4, esp 4 nomilk]"      -- forbidden: esp output violates milk
        [(water, [Some $ CInt 6]), (b, [Some $ CInt 4]), (espresso, [Some $ CInt 4, Some $ CBool False])] Forbidden
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
genConstantForType :: Variable a -> Gen (Constant a)
genConstantForType (Variable _ IntType)    = CInt <$> choose (-5, 20)
genConstantForType (Variable _ BoolType)   = CBool <$> elements [False, True]
genConstantForType (Variable _ CharType)   = CChar <$> elements ['a', 'b', 'c']
genConstantForType _ = error "not used at other types"

-- | Generate a concrete trace over a model's alphabet: pick interactions (and hence their symbolic parameters) from
-- the syntactic automaton, then fill in a value for each parameter. Traces are kept short, both because the toy
-- models are shallow and because the non-normalising FreeLatticeSlow configuration grows with the trace length.
genConcreteTrace :: STSIntrp m loc (IOAct String String) -> Gen [ConcreteStep]
genConcreteTrace intrpr = do
    let alph = Set.toList $ alphabet $ syntacticAutomaton intrpr
    len <- choose (0, 4)
    vectorOf len $ do
        interaction@(SymInteract _ vars) <- elements alph
        vals <- traverse (\(Some v) -> Some <$> genConstantForType v) vars
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

-- Compare rendered output against a golden file. Returns a failure message if it did not match, or Nothing if it did.
--
-- In compare mode (@regenerate == False@, the default) the golden file is only read, never written, so running the
-- test suite has no side-effects. A missing golden file is reported as a failure with a hint on how to create it.
--
-- In regenerate mode (@regenerate == True@) the golden file is (over)written (creating the directory if needed) and
-- the check always passes. Enable this by running the test suite with @--regenerate-golden-files@.
goldenCheck :: Bool -> String -> FilePath -> String -> IO (Maybe String)
goldenCheck regenerate what path actual
    | regenerate = do
        createDirectoryIfMissing True (takeDirectory path)
        BS.writeFile path (UTF8.fromString actual)
        return Nothing
    | otherwise = do
        existing <- Exception.try (UTF8.toString <$> BS.readFile path) :: IO (Either Exception.IOException String)
        return $ case existing of
            Right expected | expected == actual -> Nothing
                           | otherwise -> Just ("\nprint of " ++ what ++ " does not match, expected:" ++ expected ++ "but received:" ++ actual ++ "\n(run the test suite with --regenerate-golden-files to update the golden files)")
            Left _ -> Just ("\ngolden file " ++ path ++ " for " ++ what ++ " is missing; run the test suite with --regenerate-golden-files to (re)generate it")

-- Run all golden checks (so every file is regenerated in one run, even on failure), then fail once if any did not match.
goldenAssert :: [IO (Maybe String)] -> Assertion
goldenAssert checks = do
    failures <- catMaybes <$> sequence checks
    if null failures then return () else assertFailure (concat failures)


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
getSTSIntrpState' loc val = ordReturn $ IntrpState loc $ Valuation $ DMap.singleton (Variable "x" IntType) (Val val)

stsConjOfDifferentValsIntrpr :: STSIntrp FreeLattice Integer (IOAct String String)
stsConjOfDifferentValsIntrpr = interpretSTS treeSTS branchInitAssign

testConjunctionOfDifferentValuations :: Test
testConjunctionOfDifferentValuations = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsConjOfDifferentValsIntrpr)
    _ <- assertAfter "after x: " stsConjOfDifferentValsIntrpr (GateValue (Out "x") [Some $ CInt 0]) forbidden
    return ()

-----------------------------
-- Sequential composition
-----------------------------

stsExampleFL :: IOSTS FreeLattice Integer String String
stsExampleFL =
    let p = sVar pvar :: Expr Integer
        x = sVar xvar :: Expr Integer
        water = SymInteract (In "water") [Some pvar]
        ok = SymInteract (Out "ok") [Some pvar]
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
        startWithWater = SymInteract (In "startWithWater") [Some pvar]
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
getSTSIntrpStateEither loc val = ordReturn $ IntrpState loc $ Valuation $ DMap.singleton (Variable "x" IntType) (Val val)

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
    intrp1 <- assertAfter "after error: " stsSeqComposed (GateValue (Out "error") []) (getSTSIntrpStateEither (Left 0) 0)
    -- branch 1: startEmpty
    intrp2 <- assertAfter "after startEmpty: " intrp1 (GateValue (In "startEmpty") []) (getSTSIntrpStateEither (Left 1) 0)
    -- behavior transitions to sts2
    intrp3 <- assertAfter "after water 7: " intrp2 (GateValue (In "water") [Some $ CInt 7]) (getSTSIntrpStateEither (Right 1) 7)
    intrp4 <- assertAfter "after ok 7: " intrp3 (GateValue (Out "ok") [Some $ CInt 7]) (getSTSIntrpStateEither (Right 0) 7)
    intrp5 <- assertAfter "after water 9: " intrp4 (GateValue (In "water") [Some $ CInt 9]) (getSTSIntrpStateEither (Right 1) 16)
    intrp6 <- assertAfter "after ok 16: " intrp5 (GateValue (Out "ok") [Some $ CInt 16]) (getSTSIntrpStateEither (Right 0) 16)
    _ <- assertAfter "after coffee: " intrp6 (GateValue (Out "coffee") []) (getSTSIntrpStateEither (Right 2) 16)
    -- branch 2: startWithWater
    intrp8 <- assertAfter "after startWithWater: " intrp1 (GateValue (In "startWithWater") [Some $ CInt 16]) (getSTSIntrpStateEither (Left 2) 16)
    _ <- assertAfter "after coffee: " intrp8 (GateValue (Out "coffee") []) (getSTSIntrpStateEither (Right 2) 16)
    return ()

testSeqComposedAtSTS :: Test
testSeqComposedAtSTS = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf stsSeqComposedAt)
    intrp1 <- assertAfter "after error: " stsSeqComposedAt (GateValue (Out "error") []) (getSTSIntrpStateEither (Left 0) 0)
    -- branch 1: startEmpty
    intrp2 <- assertAfter "after startEmpty: " intrp1 (GateValue (In "startEmpty") []) (getSTSIntrpStateEither (Left 1) 0)
    -- behavior transitions to sts2
    intrp3 <- assertAfter "after water 7: " intrp2 (GateValue (In "water") [Some $ CInt 7]) (getSTSIntrpStateEither (Right 1) 7)
    intrp4 <- assertAfter "after ok 7: " intrp3 (GateValue (Out "ok") [Some $ CInt 7]) (getSTSIntrpStateEither (Right 0) 7)
    intrp5 <- assertAfter "after water 9: " intrp4 (GateValue (In "water") [Some $ CInt 9]) (getSTSIntrpStateEither (Right 1) 16)
    intrp6 <- assertAfter "after ok 16: " intrp5 (GateValue (Out "ok") [Some $ CInt 16]) (getSTSIntrpStateEither (Right 0) 16)
    _ <- assertAfter "after coffee: " intrp6 (GateValue (Out "coffee") []) (getSTSIntrpStateEither (Right 2) 16)
    -- branch 2: startWithWater
    intrp8 <- assertAfter "after startWithWater: " intrp1 (GateValue (In "startWithWater") [Some $ CInt 16]) (getSTSIntrpStateEither (Left 2) 16)
    _ <- assertAfter "after coffee: " intrp8 (GateValue (Out "coffee") []) (getSTSIntrpStateEither (Right 2) 16)
    return ()

{- |
    Merging at location 0 of stsPrelude, which is not sink. In this example, alphabets are disjoint although
    variables are not.
-}
testSequentiallyAtNonSinkLocation :: Test
testSequentiallyAtNonSinkLocation = TestCase $ do
    let intrpr0 = interpretSTS (sequentiallyAt stsPrelude [0] stsExampleFL) stsExampleInitAssign
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrpr0)
    intrp1 <- assertAfter "after error, stsPrelude's own transition at location 0 still works: " intrpr0 (GateValue (Out "error") []) (getSTSIntrpStateEither (Left 0) 0)
    intrp2 <- assertAfter "after water 7, entering stsExample directly from location 0: " intrp1 (GateValue (In "water") [Some $ CInt 7]) (getSTSIntrpStateEither (Right 1) 7)
    intrp3 <- assertAfter "after ok 7: " intrp2 (GateValue (Out "ok") [Some $ CInt 7]) (getSTSIntrpStateEither (Right 0) 7)
    -- the transition is not allowed; once behavior moves to the second sts, actions in the first one are no longer allowed
    _ <- assertAfter "after error: " intrp3 (GateValue (Out "error") []) forbidden
    return ()

-- Two STS that share the same input action ("step") but specify different guards for it: [3,5] and [1,3], so they
-- overlap at exactly 3.
stsGuardedA :: IOSTS FreeLattice Integer String String
stsGuardedA =
    let p = sVar pvar :: Expr Integer
        step = SymInteract (In "step") [Some pvar]
        stepA = SymInteract (In "stepA") []
        outA = SymInteract (Out "outA") []
        outC = SymInteract (Out "outC") [Some pvar]
        outGuardA = 1 .<= p .&& p .<= 2
        stepGuard = 3 .<= p .&& p .<= 5
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc stepGuard noAssignment, 1)), (stepA, ordReturn (stsTLoc sTrue noAssignment, 0))]
            1 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.fromList [(outC, ordReturn (stsTLoc outGuardA noAssignment, 0))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, stepA, outA, outC]) switches

stsGuardedB :: IOSTS FreeLattice Integer String String
stsGuardedB =
    let p = sVar pvar :: Expr Integer
        step = SymInteract (In "step") [Some pvar]
        stepB = SymInteract (In "stepB") []
        outA = SymInteract (Out "outA") []
        outB = SymInteract (Out "outB") []
        outC = SymInteract (Out "outC") [Some pvar]
        outGuardB = 2 .<= p .&& p .<= 3 -- overlaps with outGuardA at 2
        stepGuard = 1 .<= p .&& p .<= 3
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc stepGuard noAssignment, 1)), (stepB, ordReturn (stsTLoc sTrue noAssignment, 0))]
            1 -> Map.fromList [(outB, ordReturn (stsTLoc sTrue noAssignment, 2)), (outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.fromList [(outC, ordReturn (stsTLoc outGuardB noAssignment, 0))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, stepB, outA, outB, outC]) switches

{- |
    Sequentially composing stsGuardedA and stsGuardedB at location 0 of stsGuardedA, which already has a "step"
    transition: stsGuardedA's own "step" (guarded by [3,5]) and stsGuardedB's copied "step" (guarded by [1,3]) are
    both specified, so they are conjuncted with /\.
-}
testSequentiallyAtSameAction :: Test
testSequentiallyAtSameAction = TestCase $ do
    let intrpr0 = interpretSTS (sequentiallyAt stsGuardedA [0] stsGuardedB) stsExampleInitAssign
    assertEqual "\ninitial state " (getSTSIntrpStateEither (Left 0) 0) (stateConf intrpr0)
    _ <- assertAfter "after step 4, only A's guard holds: " intrpr0 (GateValue (In "step") [Some $ CInt 4]) (getSTSIntrpStateEither (Left 1) 0)
    _ <- assertAfter "after step 1, only B's guard holds: " intrpr0 (GateValue (In "step") [Some $ CInt 1]) (getSTSIntrpStateEither (Right 1) 0)
    -- satisfies both guards: the merged configuration conjunctively requires both destinations
    intrp3 <- assertAfter "after step 3, both guards hold: " intrpr0 (GateValue (In "step") [Some $ CInt 3])
        (getSTSIntrpStateEither (Left 1) 0 /\ getSTSIntrpStateEither (Right 1) 0)
    _ <- assertAfter "after outA: " intrp3 (GateValue (Out "outA") [])
        (getSTSIntrpStateEither (Left 2) 0 /\ getSTSIntrpStateEither (Right 2) 0)
    _ <- assertAfter "after outB: " intrp3 (GateValue (Out "outB") []) forbidden -- only allowed by one of the automata
    return ()

stsSelfSeqComposed :: STSIntrp FreeLattice Integer (IOAct String String)
stsSelfSeqComposed = interpretSTS (stsPrelude |>> stsPrelude) stsExampleInitAssign

-- Equivalent to |>> as both 1 and 2 are sink locations.
stsSelfSeqComposedAt :: STSIntrp FreeLattice Integer (IOAct String String)
stsSelfSeqComposedAt = interpretSTS (selfSequentiallyAt stsPrelude [1,2] stsPrelude) stsExampleInitAssign

-- Only one of the sink locations are selected
stsSelfSeqComposedAtOne :: STSIntrp FreeLattice Integer (IOAct String String)
stsSelfSeqComposedAtOne = interpretSTS (selfSequentiallyAt stsPrelude [1] stsPrelude) stsExampleInitAssign

testSelfSeqComposed :: Test
testSelfSeqComposed = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsSelfSeqComposed)
    intrp1 <- assertAfter "after error: " stsSelfSeqComposed (GateValue (Out "error") []) (getSTSIntrpState' 0 0)
    intrp2 <- assertAfter "after startEmpty: " intrp1 (GateValue (In "startEmpty") []) (getSTSIntrpState' 1 0)
    intrp3 <- assertAfter "after error: " intrp2 (GateValue (Out "error") []) (getSTSIntrpState' 0 0)
    intrp4 <- assertAfter "after startWithWater 7: " intrp3 (GateValue (In "startWithWater") [Some $ CInt 7]) (getSTSIntrpState' 2 7)
    _ <- assertAfter "after startEmpty: " intrp4 (GateValue (In "startEmpty") []) (getSTSIntrpState' 1 7)
    return ()

-- sequentially composing with |>> and selfSequentiallyAt (pointing to all sink locations) should yield the same result.
testSelfSeqComposedAt :: Test
testSelfSeqComposedAt = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsSelfSeqComposed)
    intrp1 <- assertAfter "after error: " stsSelfSeqComposed (GateValue (Out "error") []) (getSTSIntrpState' 0 0)
    intrp2 <- assertAfter "after startEmpty: " intrp1 (GateValue (In "startEmpty") []) (getSTSIntrpState' 1 0)
    intrp3 <- assertAfter "after error: " intrp2 (GateValue (Out "error") []) (getSTSIntrpState' 0 0)
    intrp4 <- assertAfter "after startWithWater 7: " intrp3 (GateValue (In "startWithWater") [Some $ CInt 7]) (getSTSIntrpState' 2 7)
    _ <- assertAfter "after startEmpty: " intrp4 (GateValue (In "startEmpty") []) (getSTSIntrpState' 1 7)
    return ()

testSelfSeqComposedAtOne :: Test
testSelfSeqComposedAtOne = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState' 0 0) (stateConf stsSelfSeqComposedAtOne)
    intrp1 <- assertAfter "after error: " stsSelfSeqComposedAtOne (GateValue (Out "error") []) (getSTSIntrpState' 0 0)
    intrp2 <- assertAfter "after startEmpty: " intrp1 (GateValue (In "startEmpty") []) (getSTSIntrpState' 1 0)
    intrp3 <- assertAfter "after startEmpty: " intrp2 (GateValue (In "startEmpty") []) (getSTSIntrpState' 1 0)
    intrp4 <- assertAfter "after startWithWater 7: " intrp3 (GateValue (In "startWithWater") [Some $ CInt 7]) (getSTSIntrpState' 2 7)
    -- Sequentially composed only at location 1, so 2 remains sink.
    _ <- assertAfter "after startEmpty: " intrp4 (GateValue (Out "error") []) forbidden
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

-----------------------------------
-- Conjunction/disjunction helpers
-----------------------------------

stsConjGuarded :: STSIntrp FreeLattice (Either Integer Integer) (IOAct String String)
stsConjGuarded = interpretSTS (stsGuardedA //\\ stsGuardedB) stsExampleInitAssign

stsDisjGuarded :: STSIntrp FreeLattice (Either Integer Integer) (IOAct String String)
stsDisjGuarded = interpretSTS (stsGuardedA \\// stsGuardedB) stsExampleInitAssign

testConjunctionGuardedSTS :: Test
testConjunctionGuardedSTS = TestCase $ do
    let conjInitState = getSTSIntrpStateEither (Left 0) 0 /\ getSTSIntrpStateEither (Right 0) 0
    assertEqual "\ninitial state " conjInitState (stateConf stsConjGuarded)
    _ <- assertAfter "after outA: " stsConjGuarded (GateValue (In "stepA") []) conjInitState
    -- only stsGuardedA's guard holds
    _ <- assertAfter "after step 4, only stsGuardedA's guard holds: " stsConjGuarded (GateValue (In "step") [Some $ CInt 4]) (getSTSIntrpStateEither (Left 1) 0)
    -- only B's guard holds
    _ <- assertAfter "after step 1, only B's guard holds: " stsConjGuarded (GateValue (In "step") [Some $ CInt 1]) (getSTSIntrpStateEither (Right 1) 0)
    -- both guards hold: conjunction of both destinations
    intrp3 <- assertAfter "after step 3, both guards hold: " stsConjGuarded (GateValue (In "step") [Some $ CInt 3])
        (getSTSIntrpStateEither (Left 1) 0 /\ getSTSIntrpStateEither (Right 1) 0)
    -- outA is allowed by both
    intrp4 <- assertAfter "after outA: " intrp3 (GateValue (Out "outA") [])
        (getSTSIntrpStateEither (Left 2) 0 /\ getSTSIntrpStateEither (Right 2) 0)
    -- only the overlapping value for outC (2) is allowed
    _ <- assertAfter "after outC 2: " intrp4 (GateValue (Out "outC") [Some $ CInt 2])
        (getSTSIntrpStateEither (Left 0) 0 /\ getSTSIntrpStateEither (Right 0) 0)
    _ <- assertAfter "after outC 3: " intrp4 (GateValue (Out "outC") [Some $ CInt 3]) forbidden
    _ <- assertAfter "after outC 1: " intrp4 (GateValue (Out "outC") [Some $ CInt 1]) forbidden
    -- outB is only allowed by B, so the conjunction forbids it
    _ <- assertAfter "after outB: " intrp3 (GateValue (Out "outB") []) forbidden
    return ()


testDisjunctionGuardedSTS :: Test
testDisjunctionGuardedSTS = TestCase $ do
    let disjInitState = getSTSIntrpStateEither (Left 0) 0 \/ getSTSIntrpStateEither (Right 0) 0
    assertEqual "\ninitial state " disjInitState (stateConf stsDisjGuarded)
    -- only defined for B
    _ <- assertAfter "after step 4: " stsDisjGuarded (GateValue (In "step") [Some $ CInt 4]) underspecified
    -- only defined for A
    _ <- assertAfter "after step 1: " stsDisjGuarded (GateValue (In "step") [Some $ CInt 1]) underspecified
    -- both guards hold
    intrp3 <- assertAfter "after step 3, both guards hold: " stsDisjGuarded (GateValue (In "step") [Some $ CInt 3])
        (getSTSIntrpStateEither (Left 1) 0 \/ getSTSIntrpStateEither (Right 1) 0)
    -- outB is only allowed by B (still allowed by the disjunction):
    _ <- assertAfter "after outB: " intrp3 (GateValue (Out "outB") []) (getSTSIntrpStateEither (Right 2) 0)
    -- outA is allowed by both
    intrp5 <- assertAfter "after outA: " intrp3 (GateValue (Out "outA") [])
        (getSTSIntrpStateEither (Left 2) 0 \/ getSTSIntrpStateEither (Right 2) 0)
    -- only the overlapping value for outC (2) is allowed
    _ <- assertAfter "after outC 2: " intrp5 (GateValue (Out "outC") [Some $ CInt 2]) disjInitState
    _ <- assertAfter "after outC 3: " intrp5 (GateValue (Out "outC") [Some $ CInt 3]) disjInitState
    _ <- assertAfter "after outC 1: " intrp5 (GateValue (Out "outC") [Some $ CInt 1]) disjInitState
    return ()

stsGuardedC :: IOSTS FreeLattice Integer String String
stsGuardedC =
    let p = sVar pvar :: Expr Integer
        step = SymInteract (In "step") [Some pvar]
        stepC = SymInteract (In "stepC") []
        outA = SymInteract (Out "outA") []
        outD = SymInteract (Out "outD") []
        outC = SymInteract (Out "outC") [Some pvar]
        outGuardC = 2 .== p
        stepGuard = 2 .<= p .&& p .<= 4
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc stepGuard noAssignment, 1)), (stepC, ordReturn (stsTLoc sTrue noAssignment, 0))]
            1 -> Map.fromList [(outD, ordReturn (stsTLoc sTrue noAssignment, 2)), (outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.fromList [(outC, ordReturn (stsTLoc outGuardC noAssignment, 0))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, stepC, outA, outD, outC]) switches

getSTSIntrpStateLabeled :: String -> Integer -> Integer -> FreeLattice (IntrpState (String, Integer))
getSTSIntrpStateLabeled k loc val = ordReturn $ IntrpState (k, loc) $ Valuation $ DMap.singleton (Variable "x" IntType) (Val val)

stsConjGuardedAll :: STSIntrp FreeLattice (String, Integer) (IOAct String String)
stsConjGuardedAll = interpretSTS (conjunctionAll [("A", stsGuardedA), ("B", stsGuardedB), ("C", stsGuardedC)]) stsExampleInitAssign

stsDisjGuardedAll :: STSIntrp FreeLattice (String, Integer) (IOAct String String)
stsDisjGuardedAll = interpretSTS (disjunctionAll [("A", stsGuardedA), ("B", stsGuardedB), ("C", stsGuardedC)]) stsExampleInitAssign

testConjunctionAllGuardedSTS :: Test
testConjunctionAllGuardedSTS = TestCase $ do
    let conjInitState = getSTSIntrpStateLabeled "A" 0 0 /\ getSTSIntrpStateLabeled "B" 0 0 /\ getSTSIntrpStateLabeled "C" 0 0
    assertEqual "\ninitial state " conjInitState (stateConf stsConjGuardedAll)
    -- only specified at A, still allowed
    _ <- assertAfter "after stepA: " stsConjGuardedAll (GateValue (In "stepA") []) conjInitState
    -- only A's guard holds
    _ <- assertAfter "after step 5, only A's guard holds: " stsConjGuardedAll (GateValue (In "step") [Some $ CInt 5]) (getSTSIntrpStateLabeled "A" 1 0)
    -- only A and C's guards hold
    _ <- assertAfter "after step 4, A and C's guards hold: " stsConjGuardedAll (GateValue (In "step") [Some $ CInt 4])
        (getSTSIntrpStateLabeled "A" 1 0 /\ getSTSIntrpStateLabeled "C" 1 0)
    -- all three guards hold: genuine three-way conjunction of all destinations
    intrp3 <- assertAfter "after step 3, all three guards hold: " stsConjGuardedAll (GateValue (In "step") [Some $ CInt 3])
        (getSTSIntrpStateLabeled "A" 1 0 /\ getSTSIntrpStateLabeled "B" 1 0 /\ getSTSIntrpStateLabeled "C" 1 0)
    -- outA is allowed by all three
    intrp4 <- assertAfter "after outA: " intrp3 (GateValue (Out "outA") [])
        (getSTSIntrpStateLabeled "A" 2 0 /\ getSTSIntrpStateLabeled "B" 2 0 /\ getSTSIntrpStateLabeled "C" 2 0)
    -- only the overlapping value for outC (2) is allowed; back to the composed initial state
    _ <- assertAfter "after outC 2: " intrp4 (GateValue (Out "outC") [Some $ CInt 2]) conjInitState
    _ <- assertAfter "after outC 3: " intrp4 (GateValue (Out "outC") [Some $ CInt 3]) forbidden -- only B's guard holds, forbidden
    _ <- assertAfter "after outC 1: " intrp4 (GateValue (Out "outC") [Some $ CInt 1]) forbidden -- only A's guard holds, forbidden
    -- outB is only allowed by B, outD is only allowed by C: the conjunction forbids both
    _ <- assertAfter "after outB: " intrp3 (GateValue (Out "outB") []) forbidden
    _ <- assertAfter "after outD: " intrp3 (GateValue (Out "outD") []) forbidden
    return ()

testDisjunctionAllGuardedSTS :: Test
testDisjunctionAllGuardedSTS = TestCase $ do
    let disjInitState = getSTSIntrpStateLabeled "A" 0 0 \/ getSTSIntrpStateLabeled "B" 0 0 \/ getSTSIntrpStateLabeled "C" 0 0
    assertEqual "\ninitial state " disjInitState (stateConf stsDisjGuardedAll)
    _ <- assertAfter "after step 5: " stsDisjGuardedAll (GateValue (In "step") [Some $ CInt 5]) underspecified -- only A's guard holds
    _ <- assertAfter "after step 4: " stsDisjGuardedAll (GateValue (In "step") [Some $ CInt 4]) underspecified -- B's guard fails
    -- all three guards hold
    intrp3 <- assertAfter "after step 3, all three guards hold: " stsDisjGuardedAll (GateValue (In "step") [Some $ CInt 3])
        (getSTSIntrpStateLabeled "A" 1 0 \/ getSTSIntrpStateLabeled "B" 1 0 \/ getSTSIntrpStateLabeled "C" 1 0)
    -- outA is allowed by all three
    intrp4 <- assertAfter "after outA: " intrp3 (GateValue (Out "outA") [])
        (getSTSIntrpStateLabeled "A" 2 0 \/ getSTSIntrpStateLabeled "B" 2 0 \/ getSTSIntrpStateLabeled "C" 2 0)
    -- All outputs that are defined for at least one of the automata are allowed
    _ <- assertAfter "after outB: " intrp3 (GateValue (Out "outB") []) (getSTSIntrpStateLabeled "B" 2 0)
    _ <- assertAfter "after outD: " intrp3 (GateValue (Out "outD") []) (getSTSIntrpStateLabeled "C" 2 0)
    -- All values for outC are allowed, regardless of which guards hold
    _ <- assertAfter "after outC 2: " intrp4 (GateValue (Out "outC") [Some $ CInt 2]) disjInitState -- all guards hold
    _ <- assertAfter "after outC 3: " intrp4 (GateValue (Out "outC") [Some $ CInt 3]) disjInitState -- only B's guard holds
    _ <- assertAfter "after outC 1: " intrp4 (GateValue (Out "outC") [Some $ CInt 1]) disjInitState -- only A's guard holds
    return ()

stsTriangle0 :: IOSTS FreeLattice Integer String String
stsTriangle0 =
    let p = sVar pvar :: Expr Integer
        outA = SymInteract (Out "outA") []
        outB = SymInteract (Out "outB") []
        outC = SymInteract (Out "outC") []
        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            1 -> Map.fromList [(outC, ordReturn (stsTLoc sTrue noAssignment, 0))]
            2 -> Map.fromList [(outB, ordReturn (stsTLoc sTrue noAssignment, 1))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [outA, outB, outC]) switches

stsTriangle1 :: IOSTS FreeLattice Integer String String
stsTriangle1 =
    let p = sVar pvar :: Expr Integer
        outA = SymInteract (Out "outA") []
        outB = SymInteract (Out "outB") []
        outC = SymInteract (Out "outC") []
        initConf = ordReturn 1
        switches q = case q of
            0 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            1 -> Map.fromList [(outC, ordReturn (stsTLoc sTrue noAssignment, 0))]
            2 -> Map.fromList [(outB, ordReturn (stsTLoc sTrue noAssignment, 1))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [outA, outB, outC]) switches

stsDisjTri :: STSIntrp FreeLattice (Either Integer Integer) (IOAct String String)
stsDisjTri = interpretSTS (stsTriangle0 \\// stsTriangle1) stsExampleInitAssign

stsDisjAllTri :: STSIntrp FreeLattice (String, Integer) (IOAct String String)
stsDisjAllTri = interpretSTS (disjunctionAll [("tri0", stsTriangle0), ("tri1", stsTriangle1)]) stsExampleInitAssign

testPrintTriDisj :: Test
testPrintTriDisj = TestCase $ do
    let model = (interpretSTS stsTriangle0 stsExampleInitAssign)
    assertBool failureMessageDA (expectedDA == actualDA)
    assertBool failureMessageD (expectedD == actualD)
        where
        failureMessageDA = "print of STS does not match, expected:" ++ expectedDA ++ "but received:" ++ actualDA
        failureMessageD = "print of STS does not match, expected:" ++ expectedD ++ "but received:" ++ actualD
        actualDA = "\n" ++ prettyPrintIntrp stsDisjAllTri ++ "\n"
        actualD = "\n" ++ prettyPrintIntrp stsDisjTri ++ "\n"
        expectedD = [QQ.r|
current state configuration: (Left 0,{x:=0}) ∨ (Right 1,{x:=0})
initial location configuration: Left 0 ∨ Right 1
locations: Left 0, Left 1, Left 2, Right 0, Right 1, Right 2
transitions:
Left 0  ――!"outA" []⟶  (True, {},Left 2)
Left 0  ――!"outB" []⟶  ⊥
Left 0  ――!"outC" []⟶  ⊥
Left 1  ――!"outA" []⟶  ⊥
Left 1  ――!"outB" []⟶  ⊥
Left 1  ――!"outC" []⟶  (True, {},Left 0) ∨ (True, {},Right 1)
Left 2  ――!"outA" []⟶  ⊥
Left 2  ――!"outB" []⟶  (True, {},Left 1)
Left 2  ――!"outC" []⟶  ⊥
Right 0  ――!"outA" []⟶  (True, {},Right 2)
Right 0  ――!"outB" []⟶  ⊥
Right 0  ――!"outC" []⟶  ⊥
Right 1  ――!"outA" []⟶  ⊥
Right 1  ――!"outB" []⟶  ⊥
Right 1  ――!"outC" []⟶  (True, {},Right 0)
Right 2  ――!"outA" []⟶  ⊥
Right 2  ――!"outB" []⟶  (True, {},Left 0) ∨ (True, {},Right 1)
Right 2  ――!"outC" []⟶  ⊥
|]
        expectedDA = [QQ.r|
current state configuration: (("tri0",0),{x:=0}) ∨ (("tri1",1),{x:=0})
initial location configuration: ("tri0",0) ∨ ("tri1",1)
locations: ("tri0",0), ("tri0",1), ("tri0",2), ("tri1",0), ("tri1",1), ("tri1",2)
transitions:
("tri0",0)  ――!"outA" []⟶  (True, {},("tri0",2))
("tri0",0)  ――!"outB" []⟶  ⊥
("tri0",0)  ――!"outC" []⟶  ⊥
("tri0",1)  ――!"outA" []⟶  ⊥
("tri0",1)  ――!"outB" []⟶  ⊥
("tri0",1)  ――!"outC" []⟶  (True, {},("tri0",0)) ∨ (True, {},("tri1",1))
("tri0",2)  ――!"outA" []⟶  ⊥
("tri0",2)  ――!"outB" []⟶  (True, {},("tri0",1))
("tri0",2)  ――!"outC" []⟶  ⊥
("tri1",0)  ――!"outA" []⟶  (True, {},("tri1",2))
("tri1",0)  ――!"outB" []⟶  ⊥
("tri1",0)  ――!"outC" []⟶  ⊥
("tri1",1)  ――!"outA" []⟶  ⊥
("tri1",1)  ――!"outB" []⟶  ⊥
("tri1",1)  ――!"outC" []⟶  (True, {},("tri1",0))
("tri1",2)  ――!"outA" []⟶  ⊥
("tri1",2)  ――!"outB" []⟶  (True, {},("tri0",0)) ∨ (True, {},("tri1",1))
("tri1",2)  ――!"outC" []⟶  ⊥
|]        

stsTriangle1or2 :: IOSTS FreeLattice Integer String String
stsTriangle1or2 =
    let p = sVar pvar :: Expr Integer
        outA = SymInteract (Out "outA") []
        outB = SymInteract (Out "outB") []
        outC = SymInteract (Out "outC") []
        initConf = ordReturn 1 \/ ordReturn 2
        switches q = case q of
            0 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            1 -> Map.fromList [(outC, ordReturn (stsTLoc sTrue noAssignment, 0))]
            2 -> Map.fromList [(outB, ordReturn (stsTLoc sTrue noAssignment, 1))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [outA, outB, outC]) switches

-- STS1 \\// STS2, where STS1 has initial state 0 and STS2 has initial states 1 and 2
testErrorDisjOfSTSWithMultpInitStates :: Test
testErrorDisjOfSTSWithMultpInitStates = TestCase $
    assertThrowsError
        "composeGeneric: the initial state of the automaton(s) is not atomic, which is currently not supported"
        (stsTriangle0 \\// stsTriangle1or2)

-----------------------------------
-- prependOutputChecks
-----------------------------------

startGate = SymInteract (In "start") []
o1Gate = SymInteract (Out "o1") []
o2Gate = SymInteract (Out "o2") [Some pvar]
resetGate = SymInteract (In "reset") []

stsPrependChecks :: IOSTS FreeLattice Integer String String
stsPrependChecks =
    let initConf = ordReturn 0
        p = sVar pvar :: Expr Integer
        out2aGuard = 6 .>= p .&& p .>= 4
        out2bGuard = 4 .>= p .&& p .>= 2
        out2cGuard = 2 .>= p .&& p .>= 0
        switches q = case q of
            0 -> Map.fromList [(startGate, ordReturn (stsTLoc sTrue noAssignment, 1)),
                            (o2Gate, ordReturn (stsTLoc out2aGuard noAssignment, 2) \/ ordReturn (stsTLoc out2bGuard noAssignment, 2))]
            1 -> Map.fromList [(o1Gate, ordReturn (stsTLoc sTrue noAssignment, 2)),
                               (o2Gate, ordReturn (stsTLoc out2bGuard noAssignment, 3))]
            2 -> Map.fromList [(o2Gate, ordReturn (stsTLoc out2cGuard noAssignment, 3)), (resetGate, ordReturn (stsTLoc sTrue noAssignment, 0))]
            3 -> Map.empty
            _ -> Map.empty
    in automaton initConf (Set.fromList [startGate, o1Gate, o2Gate, resetGate]) switches

stsPrependChecksDisj :: IOSTS FreeLattice (CheckLoc Integer (IOSymInteract String String)) String String
stsPrependChecksDisj = prependOutputChecks (\/) ("check_" ++) stsPrependChecks

stsPrependChecksDisjIntrpr :: STSIntrp FreeLattice (CheckLoc Integer (IOSymInteract String String)) (IOAct String String)
stsPrependChecksDisjIntrpr = interpretSTS stsPrependChecksDisj stsExampleInitAssign

getStableOrPendingState :: CheckLoc Integer (IOSymInteract String String) -> Integer -> FreeLattice (IntrpState (CheckLoc Integer (IOSymInteract String String)))
getStableOrPendingState loc val = ordReturn $ IntrpState loc $ Valuation $ DMap.singleton (Variable "x" IntType) (Val val)

testPrintPrependOutputChecksDisj :: Test
testPrintPrependOutputChecksDisj = TestCase $ assertBool failureMessage (expected == actual)
    where
    failureMessage = "print of STS does not match, expected:" ++ expected ++ "but received:" ++ actual
    actual = "\n" ++ prettyPrintIntrp stsPrependChecksDisjIntrpr ++ "\n"
    expected = [QQ.r|
current state configuration: (0,{x:=0})
initial location configuration: 0
locations: 0, 1, 2, 3, pending !"o2" [p:Int] -> 2, pending !"o1" [] -> 2, pending !"o2" [p:Int] -> 3, pending !"o2" [p:Int] -> 3
transitions:
0  ――?"check_o1" []⟶  ⊥
0  ――?"check_o2" []⟶  (True, {},pending !"o2" [p:Int] -> 2)
0  ――?"reset" []⟶  ⊤
0  ――?"start" []⟶  (True, {},1)
0  ――!"o1" []⟶  ⊥
0  ――!"o2" [p:Int]⟶  ⊥
1  ――?"check_o1" []⟶  (True, {},pending !"o1" [] -> 2)
1  ――?"check_o2" []⟶  (True, {},pending !"o2" [p:Int] -> 3)
1  ――?"reset" []⟶  ⊤
1  ――?"start" []⟶  ⊤
1  ――!"o1" []⟶  ⊥
1  ――!"o2" [p:Int]⟶  ⊥
2  ――?"check_o1" []⟶  ⊥
2  ――?"check_o2" []⟶  (True, {},pending !"o2" [p:Int] -> 3)
2  ――?"reset" []⟶  (True, {},0)
2  ――?"start" []⟶  ⊤
2  ――!"o1" []⟶  ⊥
2  ――!"o2" [p:Int]⟶  ⊥
3  ――?"check_o1" []⟶  ⊥
3  ――?"check_o2" []⟶  ⊥
3  ――?"reset" []⟶  ⊤
3  ――?"start" []⟶  ⊤
3  ――!"o1" []⟶  ⊥
3  ――!"o2" [p:Int]⟶  ⊥
pending !"o2" [p:Int] -> 2  ――?"check_o1" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――?"check_o2" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――?"reset" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――?"start" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――!"o1" []⟶  ⊥
pending !"o2" [p:Int] -> 2  ――!"o2" [p:Int]⟶  ((((-p+4)) ≥ 0)∧(((p+-2)) ≥ 0), {},2) ∨ ((((-p+6)) ≥ 0)∧(((p+-4)) ≥ 0), {},2)
pending !"o1" [] -> 2  ――?"check_o1" []⟶  ⊤
pending !"o1" [] -> 2  ――?"check_o2" []⟶  ⊤
pending !"o1" [] -> 2  ――?"reset" []⟶  ⊤
pending !"o1" [] -> 2  ――?"start" []⟶  ⊤
pending !"o1" [] -> 2  ――!"o1" []⟶  (True, {},2)
pending !"o1" [] -> 2  ――!"o2" [p:Int]⟶  ⊥
pending !"o2" [p:Int] -> 3  ――?"check_o1" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"check_o2" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"reset" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"start" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――!"o1" []⟶  ⊥
pending !"o2" [p:Int] -> 3  ――!"o2" [p:Int]⟶  ((((-p+4)) ≥ 0)∧(((p+-2)) ≥ 0), {},3)
pending !"o2" [p:Int] -> 3  ――?"check_o1" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"check_o2" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"reset" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"start" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――!"o1" []⟶  ⊥
pending !"o2" [p:Int] -> 3  ――!"o2" [p:Int]⟶  (((p) ≥ 0)∧(((-p+2)) ≥ 0), {},3)
|]

testPrependOutputChecksDisj :: Test
testPrependOutputChecksDisj = TestCase $ do
    let s = getStableOrPendingState
    assertEqual "\ninitial state " (s (Stable 0) 0) (stateConf stsPrependChecksDisjIntrpr)
    -- First case: same output gate, same initial location, same target location
    intrp0 <- assertAfter "after check_o2: " stsPrependChecksDisjIntrpr (GateValue (In "check_o2") []) (s (Pending 0 o2Gate 2) 0)
    _ <- assertAfter "after o2 (meets only guard a): " intrp0 (GateValue (Out "o2") [Some $ CInt 6]) (s (Stable 2) 0)
    _ <- assertAfter "after o2 (meets both guards): " intrp0 (GateValue (Out "o2") [Some $ CInt 4]) (s (Stable 2) 0)
    _ <- assertAfter "after o2 (meets only guard b): " intrp0 (GateValue (Out "o2") [Some $ CInt 2]) (s (Stable 2) 0)
    _ <- assertAfter "after o2 (meets no guard): " intrp0 (GateValue (Out "o2") [Some $ CInt 48]) forbidden
    intrp1 <- assertAfter "after start: " stsPrependChecksDisjIntrpr (GateValue (In "start") []) (s (Stable 1) 0)
    -- Second case: outputs with different gates. If one is checked, the other is forbidden
    _ <- assertAfter "after o1: " intrp1 (GateValue (Out "o1") []) forbidden
    intrp2 <- assertAfter "after check_o1: " intrp1 (GateValue (In "check_o1") []) (s (Pending 1 o1Gate 2) 0)
    -- while pending, only the checked output is available: every other output stays forbidden
    _ <- assertAfter "o2 while pending o1: " intrp2 (GateValue (Out "o2") [Some $ CInt 0]) forbidden
    _ <- assertAfter "next while pending o1: " intrp2 (GateValue (In "reset") []) underspecified
    _ <- assertAfter "check_o2 while pending o1: " intrp2 (GateValue (In "check_o2") []) underspecified
    intrp3 <- assertAfter "after o1: " intrp2 (GateValue (Out "o1") []) (s (Stable 2) 0)
    -- location 2's own switches are back, unchanged
    _ <- assertAfter "after next: " intrp3 (GateValue (In "reset") []) (s (Stable 0) 0)
    intrp4 <- assertAfter "after check_o2: " intrp3 (GateValue (In "check_o2") []) (s (Pending 2 o2Gate 3) 0)
    -- Third case: outputs with the same gate and same target location, but different initial location
    _ <- assertAfter "after o2 (meets only guard b): " intrp4 (GateValue (Out "o2") [Some $ CInt 4]) forbidden
    _ <- assertAfter "after o2 (meets both guards): " intrp4 (GateValue (Out "o2") [Some $ CInt 2]) (s (Stable 3) 0)
    _ <- assertAfter "after o2 (meets only guard c): " intrp4 (GateValue (Out "o2") [Some $ CInt 0]) (s (Stable 3) 0)
    return ()

stsPrependChecksConj :: IOSTS FreeLattice (CheckLoc Integer (IOSymInteract String String)) String String
stsPrependChecksConj = prependOutputChecks (/\) ("check_" ++) stsPrependChecks

stsPrependChecksConjIntrpr :: STSIntrp FreeLattice (CheckLoc Integer (IOSymInteract String String)) (IOAct String String)
stsPrependChecksConjIntrpr = interpretSTS stsPrependChecksConj stsExampleInitAssign

testPrintPrependOutputChecksConj :: Test
testPrintPrependOutputChecksConj = TestCase $ assertBool failureMessage (expected == actual)
    where
    failureMessage = "print of STS does not match, expected:" ++ expected ++ "but received:" ++ actual
    actual = "\n" ++ prettyPrintIntrp stsPrependChecksConjIntrpr ++ "\n"
    expected = [QQ.r|
current state configuration: (0,{x:=0})
initial location configuration: 0
locations: 0, 1, 2, 3, pending !"o2" [p:Int] -> 2, pending !"o1" [] -> 2, pending !"o2" [p:Int] -> 3, pending !"o2" [p:Int] -> 3
transitions:
0  ――?"check_o1" []⟶  ⊥
0  ――?"check_o2" []⟶  (True, {},pending !"o2" [p:Int] -> 2)
0  ――?"reset" []⟶  ⊤
0  ――?"start" []⟶  (True, {},1)
0  ――!"o1" []⟶  ⊥
0  ――!"o2" [p:Int]⟶  ⊥
1  ――?"check_o1" []⟶  (True, {},pending !"o1" [] -> 2)
1  ――?"check_o2" []⟶  (True, {},pending !"o2" [p:Int] -> 3)
1  ――?"reset" []⟶  ⊤
1  ――?"start" []⟶  ⊤
1  ――!"o1" []⟶  ⊥
1  ――!"o2" [p:Int]⟶  ⊥
2  ――?"check_o1" []⟶  ⊥
2  ――?"check_o2" []⟶  (True, {},pending !"o2" [p:Int] -> 3)
2  ――?"reset" []⟶  (True, {},0)
2  ――?"start" []⟶  ⊤
2  ――!"o1" []⟶  ⊥
2  ――!"o2" [p:Int]⟶  ⊥
3  ――?"check_o1" []⟶  ⊥
3  ――?"check_o2" []⟶  ⊥
3  ――?"reset" []⟶  ⊤
3  ――?"start" []⟶  ⊤
3  ――!"o1" []⟶  ⊥
3  ――!"o2" [p:Int]⟶  ⊥
pending !"o2" [p:Int] -> 2  ――?"check_o1" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――?"check_o2" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――?"reset" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――?"start" []⟶  ⊤
pending !"o2" [p:Int] -> 2  ――!"o1" []⟶  ⊥
pending !"o2" [p:Int] -> 2  ――!"o2" [p:Int]⟶  ((((-p+4)) ≥ 0)∧(((p+-2)) ≥ 0), {},2) ∧ ((((-p+6)) ≥ 0)∧(((p+-4)) ≥ 0), {},2)
pending !"o1" [] -> 2  ――?"check_o1" []⟶  ⊤
pending !"o1" [] -> 2  ――?"check_o2" []⟶  ⊤
pending !"o1" [] -> 2  ――?"reset" []⟶  ⊤
pending !"o1" [] -> 2  ――?"start" []⟶  ⊤
pending !"o1" [] -> 2  ――!"o1" []⟶  (True, {},2)
pending !"o1" [] -> 2  ――!"o2" [p:Int]⟶  ⊥
pending !"o2" [p:Int] -> 3  ――?"check_o1" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"check_o2" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"reset" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"start" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――!"o1" []⟶  ⊥
pending !"o2" [p:Int] -> 3  ――!"o2" [p:Int]⟶  ((((-p+4)) ≥ 0)∧(((p+-2)) ≥ 0), {},3)
pending !"o2" [p:Int] -> 3  ――?"check_o1" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"check_o2" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"reset" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――?"start" []⟶  ⊤
pending !"o2" [p:Int] -> 3  ――!"o1" []⟶  ⊥
pending !"o2" [p:Int] -> 3  ――!"o2" [p:Int]⟶  (((p) ≥ 0)∧(((-p+2)) ≥ 0), {},3)
|]

testPrependOutputChecksConj :: Test
testPrependOutputChecksConj = TestCase $ do
    let s = getStableOrPendingState
    assertEqual "\ninitial state " (s (Stable 0) 0) (stateConf stsPrependChecksConjIntrpr)
    -- First case: same output gate, same initial location, same target location
    intrp0 <- assertAfter "after check_o2: " stsPrependChecksConjIntrpr (GateValue (In "check_o2") []) (s (Pending 0 o2Gate 2) 0)
    _ <- assertAfter "after o2 (meets only guard a): " intrp0 (GateValue (Out "o2") [Some $ CInt 6]) forbidden
    _ <- assertAfter "after o2 (meets both guards): " intrp0 (GateValue (Out "o2") [Some $ CInt 4]) (s (Stable 2) 0)
    _ <- assertAfter "after o2 (meets only guard b): " intrp0 (GateValue (Out "o2") [Some $ CInt 2]) forbidden
    _ <- assertAfter "after o2 (meets no guard): " intrp0 (GateValue (Out "o2") [Some $ CInt 48]) forbidden
    intrp1 <- assertAfter "after start: " stsPrependChecksConjIntrpr (GateValue (In "start") []) (s (Stable 1) 0)
    -- Second case: outputs with different gates. If one is checked, the other is forbidden
    _ <- assertAfter "after o1: " intrp1 (GateValue (Out "o1") []) forbidden
    intrp2 <- assertAfter "after check_o1: " intrp1 (GateValue (In "check_o1") []) (s (Pending 1 o1Gate 2) 0)
    -- while pending, only the checked output is available: every other output stays forbidden
    _ <- assertAfter "o2 while pending o1: " intrp2 (GateValue (Out "o2") [Some $ CInt 0]) forbidden
    _ <- assertAfter "next while pending o1: " intrp2 (GateValue (In "reset") []) underspecified
    _ <- assertAfter "check_o2 while pending o1: " intrp2 (GateValue (In "check_o2") []) underspecified
    intrp3 <- assertAfter "after o1: " intrp2 (GateValue (Out "o1") []) (s (Stable 2) 0)
    -- location 2's own switches are back, unchanged
    _ <- assertAfter "after next: " intrp3 (GateValue (In "reset") []) (s (Stable 0) 0)
    intrp4 <- assertAfter "after check_o2: " intrp3 (GateValue (In "check_o2") []) (s (Pending 2 o2Gate 3) 0)
    -- Third case: outputs with the same gate and same target location, but different initial location
    _ <- assertAfter "after o2 (meets only guard b): " intrp4 (GateValue (Out "o2") [Some $ CInt 4]) forbidden
    _ <- assertAfter "after o2 (meets both guards): " intrp4 (GateValue (Out "o2") [Some $ CInt 2]) (s (Stable 3) 0)
    _ <- assertAfter "after o2 (meets only guard c): " intrp4 (GateValue (Out "o2") [Some $ CInt 0]) (s (Stable 3) 0)
    return ()
