{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Test.Lattest.Model.STSTest (
    testSTSHappyFlow,
    testErrorThrowingGates,
    testSTSUnHappyFlow,
    testPrintSTS,
    testSTSTestSelection,
    testLatticeSTS,
    testLatticeSTSQuiescence,
    testLinearCoffeeTreeStructure,
    testComplexTreeStructure,
    testComposedCoffeeTreeStructure,
    testComposedSeTreeStructure,
    testConcreteTraceSpecifiedAllowedCorrespondence,
    prop_specifiedAllowedCorrespondence,
    composedCoffeeMachineIntrpr
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

import qualified Lattest.Adapter.Adapter as Adapter
import Lattest.Adapter.StandardAdapters(pureAdapter)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(runSMTTester, Verdict(..))
import Lattest.Model.Automaton(after, stateConf,automaton,IntrpState(..),prettyPrintIntrp,stsTLoc,STStdest,alphabet,syntacticAutomaton)
import Lattest.Model.StandardAutomata(interpretSTS, IOSTS, STSIntrp, interpretSTSQuiescentInputAttemptConcrete)
import Lattest.Model.Alphabet(IOAct(..), Suspended(..), SuspendedIF, SuspendedIFGateValue, δ, SymInteract(..),GateValue(..), gateValueAsIOAct,toIOGateValue, InputAttempt(..), SymGuard, IOSymInteract)
import Lattest.Model.BoundedMonad(BoundedMonad, BooleanConfiguration, (/\), (\/), FreeLattice(..), FreeLatticeCNF(..), atom, NonDet(..), nonDet, underspecified,forbidden,isForbidden,isUnderspecified,isSpecified,isAllowed,specifiedness,Specifiedness(..), ordReturn, (<#>), BoundedConfiguration)
import Algebra.Lattice.Free(Free(..))
import Algebra.Lattice.Levitated(Levitated(..))
import Lattest.Model.Symbolic.SolveSTS(interactsToSpecifiedCondition, interactsToAllowedCondition)
import qualified Lattest.Model.Symbolic.SolveSTS as Solve
import Lattest.Model.Symbolic.SolveSymPrim(solveGuard)
import Data.List(intercalate)
import Data.Foldable(toList)
import qualified Data.Map as Map
import qualified Control.Exception as Exception
import Lattest.Model.Symbolic.Expr hiding (Var) -- 'Var' would clash with 'Algebra.Lattice.Free.Var' used by prettySeTree
import qualified Lattest.SMT.Config as Config
import qualified Lattest.SMT.SMT as SMT

pvar :: Variable
pvar = (Variable "p" IntType)
p = sVar pvar
qvar :: Variable
qvar = (Variable "q" IntType)
q = sVar qvar
xvar :: Variable
xvar = (Variable "x" IntType)
x = sVar xvar
stsExampleInitAssign :: Valuation
stsExampleInitAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)

water = SymInteract (In "water") [pvar]
ok = SymInteract (Out "ok") [pvar]
coffee = SymInteract (Out "coffee") []

{-
               !coffee
       x=0     [x>=15] 
       --> 0 ----------> 2
          / ^
?water(p) | | !ok(p)
[1<=p<=10]| |  [p=x]
  x:=x+p  | |
          v /
           1
-}
stsExample :: IOSTS NonDet Integer String String
stsExample =
    let waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = nonDet [0] :: NonDet Integer
        switches = \q -> case q of
            0 -> Map.fromList [(water,NonDet $ Set.singleton (stsTLoc waterGuard waterAssign, 1)),
                                (coffee,NonDet $ Set.singleton (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok,NonDet $ Set.singleton (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches
stsExampleIntrpr :: STSIntrp NonDet Integer (IOAct String String)
stsExampleIntrpr = interpretSTS stsExample stsExampleInitAssign

-- Interactions and STS for the branching tests, using the CNF lattice monad (FreeLatticeCNF).
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
type Branch = FreeLatticeCNF (STStdest, Integer) -> FreeLatticeCNF (STStdest, Integer) -> FreeLatticeCNF (STStdest, Integer)

-- The first-level gate g1 is used at loc 0; the second-level gate g2 at locs 1 and 2. Passing input or output gates
-- selects whether unsatisfied guards fall through to top or to bottom.
branchingSTS :: SymInteract (IOAct String String) -> SymInteract (IOAct String String) -> Branch -> Branch -> Branch -> IOSTS FreeLatticeCNF Integer String String
branchingSTS g1 g2 op0 op1 op2 =
    let gp = p .>= 5
        gq = q .>= 5
        asgn = assignment [xvar =: p]
        switches loc = case loc of
            0 -> Map.fromList [(g1, atom (stsTLoc gp asgn, 1) `op0` atom (stsTLoc gq asgn, 2))]
            1 -> Map.fromList [(g2, atom (stsTLoc gp noAssignment, 3) `op1` atom (stsTLoc gq noAssignment, 4))]
            2 -> Map.fromList [(g2, atom (stsTLoc gp noAssignment, 5) `op2` atom (stsTLoc gq noAssignment, 6))]
            _ -> Map.empty
    in automaton (atom 0 :: FreeLatticeCNF Integer) (Set.fromList [g1, g2]) switches

branchingIntrpr :: SymInteract (IOAct String String) -> SymInteract (IOAct String String) -> Branch -> Branch -> Branch -> STSIntrp FreeLatticeCNF Integer (IOAct String String)
branchingIntrpr g1 g2 op0 op1 op2 = interpretSTS (branchingSTS g1 g2 op0 op1 op2) branchInitAssign

-- A minimal STS for asserting the tree structures directly (rather than via the SMT solver):
--   loc 0 --a[p>=5]--> loc 1   (x := p) ; loc 1 is terminal.
-- One input gate keeps the symbolic-execution tree narrow enough to read.
inGate :: SymInteract (IOAct String String)
inGate = SymInteract (In "a") [pvar]
outGate :: SymInteract (IOAct String String)
outGate = SymInteract (Out "x") [pvar]

treeSTS :: IOSTS FreeLatticeCNF Integer String String
treeSTS =
    let switches loc = case loc of
            0 -> Map.fromList [(inGate, ordReturn (stsTLoc (p .>= -20) (assignment [xvar =: p]), 1) /\ ordReturn (stsTLoc (p .<= 20) (assignment [xvar =: p]), 2))]
            1 -> Map.fromList [(outGate, ordReturn (stsTLoc (x .% 2 .== 0) (assignment []), 3) \/ ordReturn (stsTLoc (x .% 3 .== 0) (assignment []), 3))]
            2 -> Map.fromList [(outGate, ordReturn (stsTLoc (x .* p .>= 0) (assignment []), 3))]
            _ -> Map.empty
    in automaton (ordReturn 0 :: FreeLatticeCNF Integer) (Set.fromList [inGate, outGate]) switches

treeIntrpr :: STSIntrp FreeLatticeCNF Integer (IOAct String String)
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

composedCoffeeMachine :: IOSTS FreeLattice String String String
composedCoffeeMachine =
    let initConf = ordReturn "a0" /\ ordReturn "b0" /\ ordReturn "c0" /\ ordReturn "d0":: FreeLattice String
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
composedCoffeeMachineIntrpr :: STSIntrp FreeLattice String (IOAct String String)
composedCoffeeMachineIntrpr = interpretSTS composedCoffeeMachine composedCoffeeMachineAssign

testComposedCoffeeTreeStructure :: Test
testComposedCoffeeTreeStructure = testTreeStructure "composed" composedCoffeeMachineIntrpr 3

-- Pretty-print the intermediate symbolic-execution tree (`Solve.SeTree`) as an indented outline. The monad is fixed
-- to `FreeLattice` (the composed coffee machine's configuration monad) so that we can render its ∧/∨/⊤/⊥ structure
-- directly, interleaved with the sequence/if-then-else structure of the tree. Unlike the CNF representation, the free
-- lattice does not normalise or deduplicate, so structurally-equal subtrees are *not* merged: the shape of the tree
-- follows the trace one-to-one. This shows the intermediate structure *before* it is folded (by `Solve.foldSeTree`)
-- into a single, hard-to-read boolean guard.
prettySeTree :: Solve.SeTree FreeLattice -> String
prettySeTree t0 = unlines (goTree "" t0)
    where
    goTree ind (Solve.SeLeaf g)  = [ind ++ "leaf: " ++ show g]
    goTree ind (Solve.SeConf c)  = (ind ++ "configuration:") : goConf (ind ++ "  ") goTree c
    goTree ind (Solve.SeSeq assign b) = (ind ++ "step [subst: " ++ show assign ++ "], branches:") : goConf (ind ++ "  ") goBranch b
    goBranch ind (Solve.SeIte g thn els) =
           [ind ++ "if " ++ show g ++ " then"]
        ++ goTree (ind ++ "    ") thn
        ++ [ind ++ "else: " ++ show els]
    -- render a FreeLattice layer, recursing into each atom via `sub`. Chains of the same operator are flattened into an
    -- n-ary ∧/∨ so the output lines up with the CNF renderer, but no merging of equal subtrees happens.
    goConf :: String -> (String -> x -> [String]) -> FreeLattice x -> [String]
    goConf ind _   (FreeLattice Top)    = [ind ++ "⊤ (underspecified)"]
    goConf ind _   (FreeLattice Bottom) = [ind ++ "⊥ (forbidden)"]
    goConf ind sub (FreeLattice (Levitate free)) = goFree ind sub free
    goFree ind sub (Var e) = sub ind e
    goFree ind sub free@(_ :/\: _) =
        let conjuncts = meets free
        in (ind ++ "∧ (" ++ show (length conjuncts) ++ " conjuncts):")
           : concatMap (goFree (ind ++ "  ") sub) conjuncts
    goFree ind sub free@(_ :\/: _) =
        let disjuncts = joins free
        in (ind ++ "∨ (" ++ show (length disjuncts) ++ " disjuncts):")
           : concatMap (goFree (ind ++ "  ") sub) disjuncts
    meets (x :/\: y) = meets x ++ meets y
    meets other      = [other]
    joins (x :\/: y) = joins x ++ joins y
    joins other      = [other]

-- Show the intermediate tree-like structure for the trace ?water !b ?esp on the composed coffee machine, as a golden
-- test. The same tree folds (via `Solve.foldSeTree asDualExpr`/`asExpr`) to the specified/allowed guards.
testComposedSeTreeStructure :: Test
testComposedSeTreeStructure = TestCase $ goldenAssert
    [ goldenCheck "composed:interactsToSeTree [water]" (goldenDir </> "composed.setree.water.txt")
        ("\n" ++ prettySeTree (Solve.interactsToSeTree composedCoffeeMachineIntrpr [water])),
        goldenCheck "composed:interactsToSeTree [water,b]" (goldenDir </> "composed.setree.water.b.txt")
        ("\n" ++ prettySeTree (Solve.interactsToSeTree composedCoffeeMachineIntrpr [water, b])),
        goldenCheck "composed:interactsToSeTree [water,b,espresso]" (goldenDir </> "composed.setree.water.b.espresso.txt")
        ("\n" ++ prettySeTree (Solve.interactsToSeTree composedCoffeeMachineIntrpr [water, b, espresso]))
    ]

-- Concrete-trace correspondence between the semantic model and the symbolic guards.
--
-- Uses the same model as `testComposedCoffeeTreeStructure` (the composed coffee machine) and the same traces as
-- `testComposedSeTreeStructure` (?water, ?water?b, ?water?b?esp and a couple of variations), but with concrete
-- parameter values filled in so the traces become concrete. For each concrete trace two independently-computed
-- verdicts are compared:
--
--   (1) SEMANTIC: run the *concrete* trace through the model with `after` (as in `testSTSHappyFlow`) and inspect the
--       resulting state configuration -- is it forbidden, underspecified, or neither (indefinite)?
--   (2) SYMBOLIC: substitute the concrete parameter values (indexed per trace position, matching the `_n` naming of
--       the symbolic guards) into the specified guard (`interactsToSpecifiedCondition`, asDualExpr) and the allowed
--       guard (`interactsToAllowedCondition`, asExpr), and evaluate each to a concrete True/False.
--
-- The two must correspond: `asDualExpr`/specified means "not underspecified" and `asExpr`/allowed means "not
-- forbidden", so the specified guard evaluates to True iff the concrete configuration is specified, and the allowed
-- guard to True iff the concrete configuration is allowed.

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
-- models are shallow and because the non-normalising FreeLattice configuration grows with the trace length.
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

testTreeStructure :: (BoundedMonad m, Foldable m, (forall a. Ord a => Ord (m a)), BooleanConfiguration m, Ord q) => String -> STSIntrp m q (IOAct String String) -> Int -> Test
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

getSTSIntrpState :: Integer ->  Integer -> NonDet (IntrpState Integer)
getSTSIntrpState loc val = nonDet [IntrpState loc $ fromConstantsMap $ Map.singleton (Variable "x" IntType) (Cint val)]

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
        _ <- Exception.evaluate someVal
        return Nothing -- no exception thrown, so no error message
    assertEqual "expected error: " (Just expectedError) actualError
    where
        handler :: Exception.ErrorCall -> IO (Maybe String)
        handler ex = return $ Just $ show ex

testPrintSTS :: Test
testPrintSTS = TestCase $ goldenAssert [ goldenCheck "printSTS" (goldenDir </> "printSTS.txt") actual ]
    where
    actual = "\n" ++ prettyPrintIntrp stsExampleIntrpr ++ "\n" -- newlines before and after to match those of the golden file.

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
        cfg = Config.changeLog Config.defaultConfig False 
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    _ <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.05 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impExampleCorrect
    (verdict, ((observed, _), _)) <- runSMTTester smtRef (interpretSTSQuiescentInputAttemptConcrete stsExample stsExampleInitAssign) testSelector imp
    assertEqual "expected conformal trace" [-- FIXME this test case assumes the SMT solver to return 1, but any solution in (1,10) is correct
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
        ] observed
    assertEqual "expected pass " Pass verdict
    where
    inpL g vals = GateValue (In (InputAttempt(g, True))) vals
    outL g vals = GateValue (Out (OutSusp g)) vals

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
    let start = SymInteract (startType "start") [pvar]
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
t1 :: (Ord i, Ord o, Num a1, Num a2, IsString t1, IsString t2, IsString o, Eq a1) => (t1 -> IOAct i o) -> (t2 -> IOAct i o) -> Integer -> Integer -> Integer -> a1 -> Map.Map (GateValue (IOAct i o)) a2
t1 startType _ p1 _ _ 0 = Map.fromList $ [((GateValue (startType "start") [Cint p1]), 1)]
t1 _ endType _ p2 q2 1 = Map.fromList $ [((GateValue (endType "end") [Cint p2, Cint q2]), 2)]
t1 _ _ _ _ _ 2 = Map.fromList $ [((GateValue (Out "done") []), 3)]
t1 _ _ _ _ _ 3 = Map.fromList $ []
impParameterized :: (String -> IOAct String String) -> (String -> IOAct String String) -> Integer -> Integer -> Integer -> IO (Adapter.Adapter (SuspendedIFGateValue String String) (Maybe (GateValue String)))
impParameterized startType endType p1 p2 q2 = do
    imp <- pureAdapter (mkStdGen 123) 0.5 (Map.mapKeys gateValueAsIOAct <$> t1 startType endType p1 p2 q2) (0 :: Integer) :: IO (Adapter.Adapter (SuspendedIF (GateValue String) (GateValue String)) (Maybe (GateValue String)))
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
    _ <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impParameterized startType endType p1 p2 q2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specParameterized startType endType comp splitFirst) stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester smtRef specIntrpr testSelector imp
    
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
inp g vals = GateValue (In (InputAttempt(g, True))) vals
inpf :: i -> [Constant] -> GateValue (IOAct (InputAttempt i) o)
inpf g vals = GateValue (In (InputAttempt(g, False))) vals
out :: o -> [Constant] -> GateValue (IOAct i (Suspended o))
out g vals = GateValue (Out (OutSusp g)) vals

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
    let start = SymInteract (In "start") [pvar]
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
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    _ <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete specQ stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester smtRef specIntrpr testSelector imp
    
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
    _ <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specParameterized In Out (\/) splitFirst) stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester smtRef specIntrpr testSelector imp
    
    assertEqual (testName ++ ": expected Pass after " ++ show observed) Fail verdict
    assertEqual (testName ++ ": expected nonconformal trace") [
                inp "start" [Cint 2],
                GateValue δ []
                ] observed

testLatticeSTSQuiescentFail2 :: String -> Bool -> Test
testLatticeSTSQuiescentFail2 testName _ = TestCase $ do
    let nrSteps = 2
        cfg = Config.changeLog Config.defaultConfig False
        smtLog = Config.smtLog cfg
        smtProc = fromJust (Config.getProc cfg)
    smtRef <- SMT.createSMTRef smtProc smtLog
    _ <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impParameterized In Out 2 42 42
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete specQ stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester smtRef specIntrpr testSelector imp
    
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
    let start = SymInteract (In "start") [pvar]
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
    _ <- SMT.runSMT smtRef SMT.openSolver

    let testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef 456 0.0 `untilCondition` stopAfterSteps nrSteps
                `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    imp <- impQParameterized In 2
    let specIntrpr = interpretSTSQuiescentInputAttemptConcrete (specUnimplementableParameterized splitFirst) stsExampleInitAssign
    (verdict, ((observed, _), _)) <- runSMTTester smtRef specIntrpr testSelector imp
    
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
