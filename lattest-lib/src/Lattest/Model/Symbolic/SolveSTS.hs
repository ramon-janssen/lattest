{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
interactsToSpecifiedCondition,
interactsToAllowedCondition,
toSpecifiedTree,
toAllowedTree,
SolveTree(..),
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard, IOSymInteract, IOAct(..))
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asExpr, asDualExpr)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.StandardAutomata(STS)
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential)
import Lattest.Model.Symbolic.Expr(substConst, subst, substVarModel, Expr(..), VarModel, valuationToVarModel, sFalse, sTrue, sConst, (.&&), (.||), sAnd, sOr, sNot, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, identityVarModel, getVariables, noAssignment)
import Lattest.SMT(SMT)
import Lattest.Util.Utils(distributeFirstMaybe)

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
import Data.Maybe (mapMaybe)

{-|
    For the given STS and a subset function, using SMT solving, find a interaction of the STS in that subset for which the guard is true from the
    current STS state. The interaction is picked uniformly randomly among interactions with satisfied gates, if any. This uses the supplied random 
    generator and returns the new random generator state. The returned gate values for that interaction are not randomized in any way, picking values
    is left to the SMT solver.
-}
solveRandomInteraction :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, RandomGen r) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g'') -> (IOSymInteract i o -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    (,r') <$> solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g'') -> (IOSymInteract i o -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr' subsetFunction' =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr'
        in mapMaybe (distributeFirstMaybe . (fmap indexParams . subsetFunction' &&& (\interaction -> interactsToSpecifiedCondition intrpr' [interaction]))) alph
        where
        -- `interactsToSpecifiedCondition` puts the (single) step's variables in SSA form, indexing them with `_0`, so
        -- index the gate parameters we solve for and read the solution back from with the same suffix. Otherwise the
        -- SMT declarations (taken from these parameters) wouldn't match the variables mentioned in the guard.
        indexParams (SymInteract g' params) = SymInteract g' (indexVar 0 <$> params)


interactsToSpecifiedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToSpecifiedCondition intrpr interacts = interactsToGuard asDualExpr intrpr interacts

interactsToAllowedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToAllowedCondition intrpr interacts = interactsToGuard asExpr intrpr interacts



-- | The symbolic state a step is expanded from. It carries, besides the location:
--
--   * the /raw/ assignment of the transition that led into this state (its right-hand sides still mention state
--     variables), used to compute how the current state variables were assigned, and
--   * the /accumulated substitution/, mapping every (indexed) state variable seen so far to an expression over
--     interaction variables only.
--
-- The accumulated substitution is what lets us substitute state variables out of the interaction guards, rather than
-- constraining them with a separate assignment guard.
data SymIntrpState loc = SymIntrpState loc VarModel VarModel deriving (Eq, Ord)

intrpStateToSym :: IntrpState a -> SymIntrpState a
intrpStateToSym (IntrpState loc vals) = SymIntrpState loc (valuationToVarModel vals) noAssignment -- no state variables resolved yet at the start of the trace

interactsToGuard :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc)
    => (m SymGuard -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToGuard f intrpr interacts =
    let smloc = intrpStateToSym BM.<#> stateConf intrpr
    in f $ interactsToGuard' 0 interacts BM.<#> smloc
    where
    t i loc = completeSTSLoc BM.<#> Map.findWithDefault err i (transRel (syntacticAutomaton intrpr) loc)
    err = throw $ ActionOutsideAlphabet callStack
    --interactsToGuard' :: Int -> [IOSymInteract i o] -> SymIntrpState loc -> SymGuard
    interactsToGuard' _ [] _ = sTrue
--    interactsToGuard' n [i] sloc = f (seStep n f (const sTrue) (t i) sloc)
    interactsToGuard' n (i:is) sloc = seStep n (ioInteractToImpliticLocation i) f (interactsToGuard' (n+1) is) (t i) sloc
    completeSTSLoc :: (STStdest, loc) -> (SymGuard, VarModel, loc)
    completeSTSLoc (STSLoc (tguard, tassign), tloc) =
        let completedAssign = tassign `varUnion` identityVarModel locVarSet
        in (tguard, completedAssign, tloc)
    locVarSet :: [Variable]
    locVarSet =
        let mArbitraryState = (toList $ stateConf intrpr) List.!? 0
        in case mArbitraryState of
            Just (IntrpState _ arbitraryValuation) -> getVariables arbitraryValuation
            Nothing -> []
    ioInteractToImpliticLocation (SymInteract (In _) _) = BM.underspecified -- this shouldn't be hard-coded
    ioInteractToImpliticLocation (SymInteract (Out _) _) = BM.forbidden

seStep :: BM.OrdFunctor m
    => Int -- ^ Step number
    -> m SymGuard -- ^ implicit transition destination if a guard is false
    -> (m SymGuard -> SymGuard) -- ^ Subalgebra mapping?
    -> (SymIntrpState loc -> SymGuard) -- ^ function to expand symbolic destination states, potentially to further steps
    -> (loc -> m (SymGuard, VarModel, loc)) -- ^ transition function
    -> SymIntrpState loc -- ^ The current state to step from
    -> SymGuard -- ^ resulting guard expressions
seStep n implicit f expand t (SymIntrpState ploc pvars) = varsToGuard indexedAssign .&& f (seStep' BM.<#> t ploc)
    where
    indexedAssign = indexLeft n $ indexRight (n-1) pvars -- n-1 should be safe: at n=0, all assigned expressions should be constants
    seStep' (tguard, completedAssign, tloc) = 
        let indexedGuard = indexExpr n tguard
        in (indexedGuard .&& expand (SymIntrpState tloc completedAssign)) .|| (sNot indexedGuard .&& f implicit) -- The implicit transition destination is a bit hacky
    indexLeft :: Int -> VarModel -> VarModel
    indexLeft n = mapVars $ indexVar n
    indexRight :: Int -> VarModel -> VarModel
    indexRight n = mapVarExprs $ indexVar n

indexExpr :: Int -> Expr t -> Expr t
indexExpr n e = mapExpressionVars (indexVar n) e
indexVar :: Int -> Variable -> Variable
--indexVar 0 v = v
indexVar n v  -- don't add a suffix for 0 primes, this avoids dealign with primes in a 1-step lookahead
    | n < 0 = error $ "left symbolic variable with index " ++ show n
    | otherwise = v {varName = varName v ++ "_" ++ show n} -- Hack. Ideally we have a nice representation which avoids collisions, and maybe a statically typed distinction between primed and unprimed variables


data SolveTree g = SolveTree {
    traceCondition :: SymGuard,
    traceChildren :: Map.Map (SymInteract g) (SolveTree g)
    }

toSpecifiedTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSpecifiedTree = toSolveTree asDualExpr

toAllowedTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toAllowedTree = toSolveTree asExpr

toSolveTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => (m (Expr Bool) -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSolveTree f intrpr = toSolveTree' f intrpr []
    where
    toSolveTree' :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, Ord (m SymGuard)) => (m (Expr Bool) -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SolveTree (IOAct i o)
    toSolveTree' f intrpr pref =
        let children = Map.fromSet (\x -> toSolveTree' f intrpr (pref ++ [x])) (alphabet $ syntacticAutomaton intrpr)
        in SolveTree (interactsToGuard f intrpr pref) children
