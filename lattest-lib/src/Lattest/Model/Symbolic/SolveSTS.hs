{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
interactsToGuard,
interactsToGuard',
symbolicExecutionTree,
toSolveTree,
SymExecTree(..),
SymExecNodeElem(..),
SolveTree(..),
DerivClassCond,
derivClasses,
destinationGuards,
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard, IOSymInteract, IOAct(..))
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asDualExpr)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.StandardAutomata(STS)
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential)
import Lattest.Model.Symbolic.Expr(substConst, Expr(..), VarModel, valuationToVarModel, sFalse, sTrue, (.&&), sAnd, sOr, sNot, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, varsToGuard, identityVarModel, getVariables)
import Lattest.SMT.SMT(SMT)
import Lattest.Util.Utils(takeJusts, distributeFirstMaybe)

import Control.Arrow((&&&), first, second)
import Control.Exception(throw)

import Data.Foldable(toList)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import GHC.Stack(callStack)
import List.Shuffle(shuffle)
import System.Random(RandomGen)

{-|
    For the given STS and a subset function, using SMT solving, find a interaction of the STS in that subset for which the guard is true from the
    current STS state. The interaction is picked uniformly randomly among interactions with satisfied gates, if any. This uses the supplied random 
    generator and returns the new random generator state. The returned gate values for that interaction are not randomized in any way, picking values
    is left to the SMT solver.
-}
solveRandomInteraction :: (BM.OrdMonad m, BooleanConfiguration m, Ord g, Ord (m (Expr Bool)), RandomGen r) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g'') -> (SymInteract g -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    fmap (,r') $ solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (BM.OrdMonad m, BooleanConfiguration m, Ord g, Ord (m (Expr Bool))) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g'') -> (SymInteract g -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr' subsetFunction' =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr'
        in takeJusts $ fmap (distributeFirstMaybe . (subsetFunction' &&& interactToGuard intrpr')) $ alph

interactToGuard :: (BM.OrdMonad m, BooleanConfiguration m, Ord g, Ord (m (Expr Bool))) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') -> SymInteract g -> SymGuard
interactToGuard intrpr interaction = let
        aut = syntacticAutomaton intrpr
    in asDualExpr $ BM.ordJoin $ stateAndInteractToGuards aut interaction BM.<#> stateConf intrpr

stateAndInteractToGuards :: (Ord g, BM.OrdFunctor m) => STS m loc g -> SymInteract g -> IntrpState loc -> m SymGuard
stateAndInteractToGuards aut interaction (IntrpState l valuation) =
    case Map.lookup interaction (transRel aut l) of
        Nothing -> throw $ ActionOutsideAlphabet callStack
        Just mtdestloc -> BM.ordMap guardAndLocToGuard mtdestloc
    where
    guardAndLocToGuard (STSLoc (tguard,_), _) = substConst valuation tguard




{-
    FIXME replace `interactToGuard` and `stateAndInteractToGuards` by the code below entirely, since
    a 1-step lookahead is just a specific version of the n-step lookahead.
-}
data SolveTree g = SolveTree {
    traceCondition :: SymGuard,
    traceChildren :: Map.Map (SymInteract g) (SolveTree g)
    }

data SymExecNodeElem loc = SymExecNodeElem {
    loc :: loc,
    symAssign :: VarModel,
    pathCondition :: SymGuard
} deriving (Eq, Ord, Show)

data SymExecTree m loc g = SymExecTree {
    node :: m (SymExecNodeElem loc),
    pathChildren :: Map.Map (SymInteract g) (Map.Map DerivClassCond (SymExecTree m loc g))
}

type DerivClassCond = (Set.Set SymGuard, Set.Set SymGuard) -- set of positive and negative guards, corresponding to a guard (∀ left) ∧ ¬(∃ right)

interactsToGuard :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToGuard intrpr interacts = interactsToGuard' (symbolicExecutionTree intrpr) interacts

interactsToGuard' :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => SymExecTree m loc (IOAct i o) -> [IOSymInteract i o] -> SymGuard
interactsToGuard' tree interacts = interactsToGuard'' 0 interacts tree
    where
    interactsToGuard'' :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => Int -> [IOSymInteract i o] -> SymExecTree m loc (IOAct i o) -> SymGuard
    interactsToGuard'' n [] tree = nodeCondition tree
    interactsToGuard'' n (x:xs) tree =
        let derivBranches = Map.assocs $ (pathChildren tree) Map.! x
            derivBranchConditions = uncurry (.&&) <$> first (classCondToGuard n) <$> second (interactsToGuard'' (n+1) xs) <$> derivBranches
        in nodeCondition tree .&& sOr (Set.fromList derivBranchConditions)
    nodeCondition :: (BM.BoundedMonad m, BooleanConfiguration m) => SymExecTree m loc g -> SymGuard
    nodeCondition = asDualExpr . BM.ordMap pathCondition . node
    classCondToGuard :: Int -> DerivClassCond -> SymGuard
    classCondToGuard pDepth (poss,negs) = sAnd (Set.map (indexExpr pDepth) poss) .&& sNot (sOr (Set.map (indexExpr pDepth) negs))

toSolveTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSolveTree intrpr = toSolveTree'  intrpr []
    where
    toSolveTree' :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SolveTree (IOAct i o)
    toSolveTree' intrpr pref = 
        let children = Map.fromSet (\x -> toSolveTree' intrpr (pref ++ [x])) (alphabet $ syntacticAutomaton intrpr)
        in SolveTree (interactsToGuard intrpr pref) children

symbolicExecutionTree :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc, Ord (m (Expr Bool))) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SymExecTree m loc (IOAct i o)
symbolicExecutionTree = symbolicExecutionTree' ioInteractToImpliticLocation
    where
    ioInteractToImpliticLocation (In _) = BM.underspecified
    ioInteractToImpliticLocation (Out _) = BM.forbidden

-- FIXME the location after an unsatisfied guard via interactToImplicitLocation is implemented in a hacky way. Using `implicitLocation` instead would
-- make sense but works on concrete values. Ideally, this location is stored in the transition (e.g. with the guard) itself
symbolicExecutionTree' :: (BM.BoundedMonad m, Foldable m, Ord g, Ord loc, Ord (m (Expr Bool))) => (forall x.(g -> m x)) -> AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') -> SymExecTree m loc g
symbolicExecutionTree' interactToImplicitLocation intrpr = symbExecTree 0 $ BM.ordMap initializeExecNodeElem $ stateConf intrpr
    where
    initializeExecNodeElem (IntrpState loc vals) =
        let initialVarModel = indexLeft 0 $ valuationToVarModel vals
        in SymExecNodeElem loc initialVarModel $ varsToGuard initialVarModel
    --symbExecTree :: Int -> m (SymGuard, loc, VarModel) -> SymbExecTree g
    symbExecTree pDepth execConf = SymExecTree execConf $ children pDepth execConf
    --children :: Int -> m (SymGuard, loc, VarModel) -> Map.Map (SymInteract g) (SymbExecTree g)
    children pDepth pExecConf = Map.fromSet (derivChildren pDepth pExecConf) (alphabet $ syntacticAutomaton intrpr)
    --pathClasses :: Int -> m (SymGuard, loc, VarModel) -> SymInteract g -> Map.Map DerivClassCond (SymExecTree m loc g)
    derivChildren pDepth pExecConf interaction =
        let mDestGuards = destinationGuards (tDest interaction) (loc BM.<#> pExecConf)
        in Map.fromSet (pathStep pDepth pExecConf interaction) (derivClasses mDestGuards)
    --pathStep :: (Ord g, Ord loc, BM.OrdFunctor m) => Int -> m (SymGuard, loc, VarModel) -> SymInteract -> DerivClassCond -> SymbExecTree g
    pathStep pDepth pExecConf interact derivClass = symbExecTree (pDepth + 1) (pExecConf BM.>># pathStep' pDepth derivClass interact)
        where
        --pathStep' :: (Ord g, Ord loc, BM.OrdFunctor m) => Int -> DerivClassCond -> SymInteract g -> (SymGuard, loc, VarModel) -> m (SymGuard, loc, VarModel)
        pathStep' pDepth derivClass interact@(SymInteract gate _) (SymExecNodeElem pLoc pVars _) =
            let mtdestloc = tDest interact pLoc
                classmtdestloc = mtdestloc BM.>># classDest derivClass gate
            in BM.ordMap (addToPath pDepth pVars derivClass) classmtdestloc
        --classDest :: DerivClassCond -> gate -> (STStdest, a) -> m (STStdest, a)
        classDest (poss, negs) gate globaldest@(STSLoc (guard, _), _)
            | guard `Set.member` poss = BM.ordReturn globaldest
            | guard `Set.member` negs = interactToImplicitLocation gate
             -- this would be a bug in derivClasses or pathStep
             | otherwise = error $ "destination guard is not in any derivative class condition\nguard:\n" ++ show guard ++ "\nclass condition:\n" ++ show (Set.toList poss) ++ "\n" ++ show (Set.toList negs)
        addToPath pDepth pVars (poss, negs) (STSLoc (tguard, tassign), tloc) =
            let completedAssign = tassign `varUnion` identityVarModel locVarSet
                indexedAssign = indexLeft (pDepth + 1) $ indexRight pDepth completedAssign
                pathLoc = tloc
                -- add the indexedAssign to the path condition. Don't substitute by the previous assignment, although this reduces the number
                -- of variables (eliminating all state variables of previous steps) this could also cause an exponential blowup
                pathCondition = varsToGuard indexedAssign .&& indexExpr pDepth tguard
            in SymExecNodeElem pathLoc indexedAssign pathCondition
    -- administration boilerplate: add indices to variables
    indexLeft :: Int -> VarModel -> VarModel
    indexLeft 0 = id -- don't add a suffix for 0 primes, this avoids dealign with primes in a 1-step lookahead
    indexLeft n = mapVars $ indexVar n
    indexRight :: Int -> VarModel -> VarModel
    indexRight 0 = id -- don't add a suffix for 0 primes, this avoids dealign with primes in a 1-step lookahead
    indexRight n = mapVarExprs $ indexVar n
    --tDest :: SymInteract g -> loc -> m (STStdest (SymGuard, SymAssign), loc)
    tDest interact loc = Maybe.fromMaybe (throw $ ActionOutsideAlphabet callStack) $ Map.lookup interact (transRel (syntacticAutomaton intrpr) loc)
    locVarSet =
        let mArbitraryState = (toList $ stateConf intrpr) List.!? 0
        in case mArbitraryState of
            Just (IntrpState _ arbitraryValuation) -> getVariables arbitraryValuation
            Nothing -> []

{-|
    Collect the destination guards reachable via a single interaction from the locations of a configuration.

    The locations are enumerated structurally (via 'Foldable'), rather than by binding the destination lookup through the
    configuration monad, since we don't want top and bottom to annihalate guards of other configurations. 
-}
destinationGuards :: Foldable m => (loc -> m (STStdest, loc)) -> m loc -> [SymGuard]
destinationGuards destForInteraction mLocs =
    [ tDestGuard dest | pLoc <- toList mLocs, dest <- toList (destForInteraction pLoc) ]

tDestGuard :: (STStdest, loc) -> SymGuard
tDestGuard (STSLoc (g, _), _) = g

derivClasses :: Foldable f => f SymGuard -> Set.Set DerivClassCond
derivClasses fGuards =
    let elems = Set.fromList $ toList fGuards
    in Set.filter (not . classIsEmpty) $ derivClass elems `Set.map` Set.powerSet elems -- filter is an optimization: remove empty classes (unsat guards)
    where
    derivClass :: Set.Set SymGuard -> Set.Set SymGuard -> DerivClassCond
    derivClass elems elemSubSet = Set.partition (`Set.member` elemSubSet) elems
    classIsEmpty :: DerivClassCond -> Bool -- should be sound, not necessarily complete (True must mean unsat, but False may also be unsat)
    classIsEmpty (poss, negs) = any (\c -> sNot c `Set.member` poss) poss -- unsat case: g and ¬g are both positive
                                || any (\c -> sNot c `Set.member` negs) negs
                                || any (\c -> c == sTrue) negs
                                || any (\c -> c == sFalse) poss

indexExpr :: Int -> Expr t -> Expr t
indexExpr n e = mapExpressionVars (indexVar n) e
indexVar :: Int -> Variable -> Variable
indexVar 0 v = v
indexVar n v = v {varName = varName v ++ "_" ++ show n} -- Hack. Ideally we have a nice representation which avoids collisions, and maybe a statically typed distinction between primed and unprimed variables
