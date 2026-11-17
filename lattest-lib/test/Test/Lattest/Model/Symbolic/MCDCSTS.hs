{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

module Test.Lattest.Model.Symbolic.MCDCSTS (
    mcdcSTSTests
    )
where

import Test.HUnit
import Data.List(isInfixOf)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Some (Some (..))
import qualified Control.Exception as Exception
import qualified Text.RawString.QQ as QQ
import Lattest.Model.Automaton(automaton, stsTLoc, prettyPrintIntrp)
import Lattest.Model.StandardAutomata(interpretSTS, IOSTS)
import Lattest.Model.Alphabet(IOAct(..), SymInteract(..), GateValue(..))
import Lattest.Model.BoundedMonad((/\), underspecified, FreeLattice, atom)
import Lattest.Model.Symbolic.Expr
import Lattest.Model.Symbolic.MCDCSTS(completeMCDC, completeMCDCWith)
import Test.Lattest.Util.STSTestUtils(pvar, qvar, xvar, stsExampleInitAssign, stsExampleInitAssignWith, getSTSIntrpState2, atLoc, assertAfter)

mcdcSTSTests :: [Test]
mcdcSTSTests =
    [ testCompleteMCDC
    , testCompleteMCDCConjunction
    , testCompleteMCDCDependentAtoms
    , testCompleteMCDCExclusiveAtoms
    , testCompleteMCDCTuple
    , testCompleteMCDCList
    , testCompleteMCDCListLengths
    , testCompleteMCDCListForall
    , testCompleteMCDCListExists
    , testCompleteMCDCErrors
    , testCompleteMCDCListErrors
    , testCompleteMCDCConfiguration
    , testCompleteMCDCLocationVariable
    ]

-- | STS with one switch per given guard on its input gate, the n-th of them leading to location n.
stsExampleMCDC :: [Expr Bool] -> IOSTS FreeLattice Integer String String
stsExampleMCDC guards =
    let water = SymInteract (In "water") [Some pvar, Some qvar]
        ok = SymInteract (Out "ok") []
        switches = \case
            0 -> Map.fromList [(water, foldr1 (/\) [atom (stsTLoc guard noAssignment, loc) | (guard, loc) <- zip guards [1..]])]
            _ -> Map.empty
    in automaton (atom 0) (Set.fromList [water, ok]) switches

listVar :: Variable [(Integer, Integer)]
listVar = Variable "listOfPair" (ListType (TupleType IntType IntType))

-- | Stands for the element of 'listVar' that a condition is evaluated on.
elemVar :: Variable (Integer, Integer)
elemVar = Variable "a" (TupleType IntType IntType)

testCompleteMCDC :: Test
testCompleteMCDC = TestCase $ do
    let p = sVar pvar .> 1
        q = sVar qvar .> 1
        sts = stsExampleMCDC [p .|| q, sNot p .&& sNot q]
        water vals = GateValue (In "water") (map (Some . CInt) vals)
    completedSTS <- completeMCDC sts ["water"]
    let completed = interpretSTS completedSTS stsExampleInitAssign
    _ <- assertAfter "after water 2 0: " completed (water [2, 0]) (getSTSIntrpState2 1 0)
    _ <- assertAfter "after water 0 2: " completed (water [0, 2]) (getSTSIntrpState2 1 0)
    _ <- assertAfter "after water 0 0: " completed (water [0, 0]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "after water 2 2: " completed (water [2, 2]) underspecified -- not an MC/DC row of p || q
    nonCompletedSTS <- completeMCDC sts [] -- gate not listed, so not completed
    let nonCompleted = interpretSTS nonCompletedSTS stsExampleInitAssign
    _ <- assertAfter "nonCompleted after water 2 2: " nonCompleted (water [2, 2]) (getSTSIntrpState2 1 0)
    return ()

testCompleteMCDCConjunction :: Test
testCompleteMCDCConjunction = TestCase $ do
    let p = sVar pvar .> 1
        q = sVar qvar .> 1
        sts = stsExampleMCDC [p .&& q, sNot p .|| sNot q] -- the second switch covers both false rows of p && q
        water vals = GateValue (In "water") (map (Some . CInt) vals)
    completedSTS <- completeMCDC sts ["water"]
    let completed = interpretSTS completedSTS stsExampleInitAssign
    _ <- assertAfter "after water 2 2: " completed (water [2, 2]) (getSTSIntrpState2 1 0)
    _ <- assertAfter "after water 0 2: " completed (water [0, 2]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "after water 2 0: " completed (water [2, 0]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "after water 0 0: " completed (water [0, 0]) underspecified -- not an MC/DC row of p && q
    return ()

-- The atoms of the guards are not independent: the row not (p > 5) && p > 10 has no solution. This is not an error,
-- and the other rows are split as usual.
testCompleteMCDCDependentAtoms :: Test
testCompleteMCDCDependentAtoms = TestCase $ do
    let p5 = sVar pvar .> 5
        p10 = sVar pvar .> 10
        guardAnd = p5 .&& p10
        guardNand = sNot p5 .|| sNot p10
        sts = stsExampleMCDC [guardAnd, guardNand]
        water vals = GateValue (In "water") (map (Some . CInt) vals)
    completedSTS <- completeMCDC sts ["water"]
    let completed = interpretSTS completedSTS stsExampleInitAssign
    _ <- assertAfter "after water 11 0: " completed (water [11, 0]) (getSTSIntrpState2 1 0)
    _ <- assertAfter "after water 7 0: " completed (water [7, 0]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "after water 0 0: " completed (water [0, 0]) underspecified -- not an MC/DC row of not p5 || not p10
    return ()

-- The atoms of the guards are not independent: at most one of p == 1, p < 0 and p > 5 can hold. No MC/DC row has two
-- of them, so each row has a solution and no value is underspecified.
testCompleteMCDCExclusiveAtoms :: Test
testCompleteMCDCExclusiveAtoms = TestCase $ do
    let p = sVar pvar
        sts = stsExampleMCDC [p .== 1 .|| p .< 0 .|| p .> 5, sNot (p .== 1) .&& p .>= 0 .&& p .<= 5]
        water vals = GateValue (In "water") (map (Some . CInt) vals)
    completedSTS <- completeMCDC sts ["water"]
    let completed = interpretSTS completedSTS stsExampleInitAssign
    _ <- assertAfter "after water 1 0: " completed (water [1, 0]) (getSTSIntrpState2 1 0) -- only p == 1 holds
    _ <- assertAfter "after water -1 0: " completed (water [-1, 0]) (getSTSIntrpState2 1 0) -- only p < 0 holds
    _ <- assertAfter "after water 6 0: " completed (water [6, 0]) (getSTSIntrpState2 1 0) -- only p > 5 holds
    _ <- assertAfter "after water 3 0: " completed (water [3, 0]) (getSTSIntrpState2 2 0) -- none of them hold
    return ()

pairVar :: Variable (Integer, Integer)
pairVar = Variable "pair" (TupleType IntType IntType)

stsExampleMCDC2 :: IOSTS FreeLattice Integer String String
stsExampleMCDC2 =
    let pair = sVar pairVar
        water = SymInteract (In "water") [Some pairVar]
        ok = SymInteract (Out "ok") []
        guardOr = sFirst pair .== 0 .|| sSecond pair .< 0 .|| sSecond pair .> 2
        guardNand = sNot (sFirst pair .== 0) .&& (sSecond pair .>= 0) .&& (sSecond pair .<= 2)
        switches = \case
            0 -> Map.fromList [(water, atom (stsTLoc guardOr noAssignment, 1) /\ atom (stsTLoc guardNand noAssignment, 2))]
            1 -> Map.fromList [(ok, atom (stsTLoc sTrue noAssignment, 3))]
            _ -> Map.empty
    in automaton (atom 0) (Set.fromList [water, ok]) switches

testCompleteMCDCTuple :: Test
testCompleteMCDCTuple = TestCase $ do
    let water a b = GateValue (In "water") [Some $ CTuple a b IntType IntType]
    completedSTS <- completeMCDC stsExampleMCDC2 ["water"]
    let completed = interpretSTS completedSTS emptyValuation
    _ <- assertAfter "after water (1,5): " completed (water 1 5) (atLoc 1) -- only snd > 2 holds
    _ <- assertAfter "after water (1,-1): " completed (water 1 (-1)) (atLoc 1) -- only snd < 0 holds
    _ <- assertAfter "after water (0,1): " completed (water 0 1) (atLoc 1) -- only fst == 0 holds
    _ <- assertAfter "after water (0,5): " completed (water 0 5) underspecified -- two conditions hold, not an MC/DC row
    _ <- assertAfter "nonCompleted after water (0,5): " (interpretSTS stsExampleMCDC2 emptyValuation) (water 0 5) (atLoc 1)
    let actual = "\n" ++ prettyPrintIntrp completed ++ "\n" -- newlines before and after to match those of the "expected" below.
    assertBool ("print of completed STS does not match, expected:" ++ expected ++ "but received:" ++ actual) (expected == actual)
    where
    expected = [QQ.r|
current state configuration: (0,{})
initial location configuration: 0
locations: 0, 1, 2, 3
transitions:
0  ――?"water" [pair:(Int, Int)]⟶  (((fst pair) = 0)∧((2+-snd pair) ≥ 0)∧((snd pair) ≥ 0), {},1) ∧ (((2+-snd pair) ≥ 0)∧((snd pair) ≥ 0)∧(¬((fst pair) = 0)), {},2) ∧ (((2+-snd pair) ≥ 0)∧(¬((fst pair) = 0))∧(¬((snd pair) ≥ 0)), {},1) ∧ (((snd pair) ≥ 0)∧(¬((fst pair) = 0))∧(¬((2+-snd pair) ≥ 0)), {},1)
0  ――!"ok" []⟶  ⊥
1  ――?"water" [pair:(Int, Int)]⟶  ⊤
1  ――!"ok" []⟶  (True, {},3)
2  ――?"water" [pair:(Int, Int)]⟶  ⊤
2  ――!"ok" []⟶  ⊥
3  ――?"water" [pair:(Int, Int)]⟶  ⊤
3  ――!"ok" []⟶  ⊥
|]

-- | Assert the location reached by the given list of pairs, or that the list is underspecified, in the given
-- completed STS.
assertMCDCLists :: IOSTS FreeLattice Integer String String -> [([(Integer, Integer)], Maybe Integer)] -> IO ()
assertMCDCLists completedSTS expectations = do
    let water pairs = GateValue (In "water") [Some $ CList pairs (TupleType IntType IntType)]
        expected = maybe underspecified atLoc
        completed = interpretSTS completedSTS emptyValuation
    sequence_ [assertAfter ("after water " ++ show pairs ++ ": ") completed (water pairs) (expected loc) | (pairs, loc) <- expectations]


-- | The elements of a list of pairs with a zero as first value are counted: none of them leads to location 1,
-- exactly one of them to location 2, and two or more to location 3.
stsExampleMCDCCount :: IOSTS FreeLattice Integer String String
stsExampleMCDCCount =
    let zeros = sLength (sFilter elemVar (sFirst (sVar elemVar) .== 0) (sVar listVar))
        water = SymInteract (In "water") [Some listVar]
        ok = SymInteract (Out "ok") []
        switches = \case
            0 -> Map.fromList [(water, atom (stsTLoc (zeros .== 0) noAssignment, 1) /\ atom (stsTLoc (zeros .== 1) noAssignment, 2)
                                    /\ atom (stsTLoc (zeros .>= 2) noAssignment, 3))]
            1 -> Map.fromList [(ok, atom (stsTLoc sTrue noAssignment, 4))]
            _ -> Map.empty
    in automaton (atom 0) (Set.fromList [water, ok]) switches

-- A list is opened for each length: every element is an atom of a count, and the length is not an atom. Below, z is
-- an element with a zero and n is one without.
testCompleteMCDCList :: Test
testCompleteMCDCList = TestCase $ do
    completedSTS <- completeMCDC stsExampleMCDCCount ["water"]
    assertMCDCLists completedSTS
        [ ([], Just 1) -- for the empty list, the counts are constants
        , ([(1,1)], Just 1)
        , ([(0,1)], Just 2)
        , ([(1,1), (1,1)], Just 1)
        , ([(0,1), (1,1)], Just 2) -- exactly one: each element is the one
        , ([(1,1), (0,1)], Just 2)
        , ([(0,1), (0,1)], Just 3)
        , ([(1,1), (1,1), (1,1)], Just 1)
        , ([(0,1), (1,1), (1,1)], Just 2)
        , ([(1,1), (0,1), (1,1)], Just 2)
        , ([(1,1), (1,1), (0,1)], Just 2)
        -- two or more of z z z: one other element is z while an element varies. The rows are z z n and n z z; their
        -- false rows are n z n and z n n.
        , ([(0,1), (0,1), (1,1)], Just 3)
        , ([(1,1), (0,1), (0,1)], Just 3)
        , ([(0,1), (1,1), (0,1)], Nothing)
        , ([(0,1), (0,1), (0,1)], Nothing)
        , ([(1,1), (1,1), (1,1), (1,1)], Nothing) -- not one of the default list lengths
        ]

-- Only the given list lengths are opened.
testCompleteMCDCListLengths :: Test
testCompleteMCDCListLengths = TestCase $ do
    completedSTS <- completeMCDCWith [1, 4] stsExampleMCDCCount ["water"]
    assertMCDCLists completedSTS
        [ ([], Nothing)
        , ([(0,1)], Just 2)
        , ([(1,1), (1,1)], Nothing)
        , ([(1,1), (1,1), (1,1), (1,1)], Just 1)
        , ([(1,1), (1,1), (0,1), (1,1)], Just 2)
        , ([(0,1), (0,1), (1,1), (1,1)], Just 3)
        ]


-- | A condition holds for all elements of a list of pairs (location 1) or not (location 2). 
-- The condition is on the variable 'elemVar'.
stsExampleMCDCForall :: Expr Bool -> IOSTS FreeLattice Integer String String
stsExampleMCDCForall cond =
    let iterator = Variable "forallIterator" BoolType
        accumulator = Variable "forallAccumulator" BoolType
        forAll = sFoldr iterator accumulator (sVar iterator .&& sVar accumulator) sTrue (sMap elemVar cond (sVar listVar))
        water = SymInteract (In "water") [Some listVar]
        switches = \case
            0 -> Map.fromList [(water, atom (stsTLoc forAll noAssignment, 1) /\ atom (stsTLoc (sNot forAll) noAssignment, 2))]
            _ -> Map.empty
    in automaton (atom 0) (Set.singleton water) switches

-- | A condition holds for some element of a list of pairs (location 1) or for none (location 2). 
-- The condition is on the variable 'elemVar'.
stsExampleMCDCExists :: Expr Bool -> IOSTS FreeLattice Integer String String
stsExampleMCDCExists cond =
    let iterator = Variable "existsIterator" BoolType
        accumulator = Variable "existsAccumulator" BoolType
        exists = sFoldr iterator accumulator (sVar iterator .|| sVar accumulator) sFalse (sMap elemVar cond (sVar listVar))
        water = SymInteract (In "water") [Some listVar]
        switches = \case
            0 -> Map.fromList [(water, atom (stsTLoc exists noAssignment, 1) /\ atom (stsTLoc (sNot exists) noAssignment, 2))]
            _ -> Map.empty
    in automaton (atom 0) (Set.singleton water) switches

-- The atoms of the condition are separate atoms for each element of the list: on a false row of "for all elements",
-- one atom of one element is false.
testCompleteMCDCListForall :: Test
testCompleteMCDCListForall = TestCase $ do
    let a = sVar elemVar
    completedSTS <- completeMCDCWith [2] (stsExampleMCDCForall (sFirst a .== 0 .&& sSecond a .>= 0)) ["water"]
    assertMCDCLists completedSTS
        [ ([(0,1), (0,1)], Just 1)
        , ([(1,1), (0,1)], Just 2) -- the first value of the first element
        , ([(0,-1), (0,1)], Just 2) -- the second value of the first element
        , ([(0,1), (1,1)], Just 2)
        , ([(0,1), (0,-1)], Just 2)
        , ([(1,-1), (0,1)], Nothing) -- two atoms are false
        , ([(1,1), (1,1)], Nothing)
        , ([(0,1)], Nothing) -- not one of the given list lengths
        , ([(0,1), (0,1), (0,1)], Nothing)
        ]

testCompleteMCDCListExists :: Test
testCompleteMCDCListExists = TestCase $ do
    completedSTS <- completeMCDCWith [2] (stsExampleMCDCExists (sFirst (sVar elemVar) .== 0)) ["water"]
    assertMCDCLists completedSTS
        [ ([(0,1), (1,1)], Just 1)
        , ([(1,1), (0,1)], Just 1)
        , ([(1,1), (1,1)], Just 2)
        , ([(0,1), (0,1)], Nothing) -- not an MC/DC row: no single element decides
        ]

testCompleteMCDCErrors :: Test
testCompleteMCDCErrors = TestCase $ do
    let p = sVar pvar .> 1
        q = sVar qvar .> 1
        assertError expectedError guards = do
            result <- Exception.try $ completeMCDC (stsExampleMCDC guards) ["water"]
            case result of
                Left (Exception.ErrorCall actualError) -> assertBool actualError (expectedError `isInfixOf` actualError)
                Right _ -> assertFailure $ "expected error: " ++ expectedError
    -- a false row that is not covered by any other switch is a warning, not an error
    mapM_ (\guards -> completeMCDC (stsExampleMCDC guards) ["water"]) [[p .&& q], [p .|| q], [p .&& q, sNot p]]
    assertError "are not disjoint" [p, sVar pvar .> 0]
    assertError "is a tautology" [sVar qvar .== 1 .|| sVar pvar .> 0 .|| sVar pvar .< 5] -- not (p > 0) && not (p < 5) has no solution

testCompleteMCDCListErrors :: Test
testCompleteMCDCListErrors = TestCase $ do
    let list = sVar listVar
        a = sVar elemVar
        count cond = sLength (sFilter elemVar cond list)
        p = sFirst a .== 0
        q = sSecond a .>= 0
        length2 = sLength list .== 2
        water = SymInteract (In "water") [Some listVar]
        sts guards = automaton (atom 0) (Set.singleton water) $ \case
            0 -> Map.fromList [(water, foldr1 (/\) [atom (stsTLoc guard noAssignment, loc) | (guard, loc) <- zip guards [1..]])]
            _ -> Map.empty
        assertError expectedError guards = do
            result <- Exception.try $ completeMCDC (sts guards :: IOSTS FreeLattice Integer String String) ["water"]
            case result of
                Left (Exception.ErrorCall actualError) -> assertBool actualError (expectedError `isInfixOf` actualError)
                Right _ -> assertFailure $ "expected error: " ++ expectedError
    -- a count can not be compared with a parameter or a location variable
    assertError "can only be compared with constants and list lengths" [count p .== sVar xvar]
    -- the condition on the elements has to be singular as well
    assertError "not a singular Boolean expression" [length2 .&& count (p .&& (q .|| p)) .== 0]
    -- a false row that is not covered by any other switch is a warning, not an error
    _ <- completeMCDC (sts [length2 .&& count p .== 0] :: IOSTS FreeLattice Integer String String) ["water"] -- lists of another length
    _ <- completeMCDC (sts [length2 .&& count p .== 0, sNot length2] :: IOSTS FreeLattice Integer String String) ["water"] -- lists with an element satisfying p
    -- on the empty list, no element satisfying p is the same as all of them
    assertError "are not disjoint" [sLength list .<= 2 .&& count p .== 0, sLength list .<= 2 .&& count p .== sLength list]

-- The initial configuration is a conjunction of two locations, each with one switch on the input gate. The false rows
-- of a guard are covered by the guard at the other location of the configuration.
testCompleteMCDCConfiguration :: Test
testCompleteMCDCConfiguration = TestCase $ do
    let p = sVar pvar .> 1
        q = sVar qvar .> 1
        water = SymInteract (In "water") [Some pvar, Some qvar]
        sts :: Expr Bool -> Expr Bool -> IOSTS FreeLattice Integer String String
        sts guard0 guard1 = automaton (atom 0 /\ atom 1) (Set.singleton water) $ \case
            0 -> Map.fromList [(water, atom (stsTLoc guard0 noAssignment, 2))]
            1 -> Map.fromList [(water, atom (stsTLoc guard1 noAssignment, 3))]
            _ -> Map.empty
        waterVals vals = GateValue (In "water") (map (Some . CInt) vals)
    completedSTS <- completeMCDC (sts (p .&& q) (sNot p .|| sNot q)) ["water"]
    let completed = interpretSTS completedSTS stsExampleInitAssign
    _ <- assertAfter "after water 2 2: " completed (waterVals [2, 2]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "after water 0 2: " completed (waterVals [0, 2]) (getSTSIntrpState2 3 0)
    _ <- assertAfter "after water 0 0: " completed (waterVals [0, 0]) underspecified -- not an MC/DC row of p && q
    -- guards of different locations may overlap
    _ <- completeMCDC (sts (p .&& q) (sNot p .|| sNot q .|| sVar pvar .> 5)) ["water"]
    -- the other location covers only one of the two false rows: a warning, and p && not q is underspecified
    uncoveredSTS <- completeMCDC (sts (p .&& q) (sNot p)) ["water"]
    let uncovered = interpretSTS uncoveredSTS stsExampleInitAssign
    _ <- assertAfter "uncovered after water 2 0: " uncovered (waterVals [2, 0]) underspecified
    return ()

-- An atom compares a gate parameter with a location variable: p > x. The split keeps the atom symbolic, so the values
-- on an MC/DC row depend on the value of x in the current state.
testCompleteMCDCLocationVariable :: Test
testCompleteMCDCLocationVariable = TestCase $ do
    let px = sVar pvar .> sVar xvar
        q = sVar qvar .> 1
        water vals = GateValue (In "water") (map (Some . CInt) vals)
    completedSTS <- completeMCDC (stsExampleMCDC [px .&& q, sNot px .|| sNot q]) ["water"]
    let completedX0 = interpretSTS completedSTS stsExampleInitAssign -- x == 0
    _ <- assertAfter "x = 0, after water 1 2: " completedX0 (water [1, 2]) (getSTSIntrpState2 1 0)
    _ <- assertAfter "x = 0, after water 0 2: " completedX0 (water [0, 2]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "x = 0, after water 1 0: " completedX0 (water [1, 0]) (getSTSIntrpState2 2 0)
    _ <- assertAfter "x = 0, after water 0 0: " completedX0 (water [0, 0]) underspecified -- not an MC/DC row of px && q
    let completedX1 = interpretSTS completedSTS (stsExampleInitAssignWith 1) -- x == 1
    _ <- assertAfter "x = 1, after water 2 2: " completedX1 (water [2, 2]) (getSTSIntrpState2 1 1)
    _ <- assertAfter "x = 1, after water 1 2: " completedX1 (water [1, 2]) (getSTSIntrpState2 2 1) -- p > x no longer holds
    _ <- assertAfter "x = 1, after water 1 0: " completedX1 (water [1, 0]) underspecified
    return ()

