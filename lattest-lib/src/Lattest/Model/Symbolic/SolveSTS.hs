{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
interactsToSpecifiedCondition,
interactsToAllowedCondition,
seTree,
treeToGuard,
SETree(..),
SEIte(..),
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard, IOSymInteract, IOAct(..))
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asExpr, asDualExpr)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential)
import Lattest.Model.Symbolic.Expr(subst, substVarModel, Expr(..), VarModel, valuationToVarModel, sTrue, (.&&), (.||), sNot, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, identityVarModel, getVariables)
import Lattest.SMT(SMT)
import Lattest.Util.Utils(distributeFirstMaybe)

import Control.Arrow((&&&))
import Control.Exception(throw)

import Data.Foldable(toList)
import qualified Data.List as List
import qualified Data.Map as Map
import GHC.Stack(callStack)
import List.Shuffle(shuffle)
import System.Random(RandomGen)
import Data.Maybe (mapMaybe)
import Data.Some (Some, mapSome)

{-|
    For the given STS and a subset function, using SMT solving, find a interaction of the STS in that subset for which the guard is true from the
    current STS state. The interaction is picked uniformly randomly among interactions with satisfied gates, if any. This uses the supplied random 
    generator and returns the new random generator state. The returned gate values for that interaction are not randomized in any way, picking values
    is left to the SMT solver.
-}
solveRandomInteraction :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, RandomGen r, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g'') -> (IOSymInteract i o -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    (,r') <$> solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g'') -> (IOSymInteract i o -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr' subsetFunction' =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr'
        in mapMaybe (distributeFirstMaybe . (fmap indexParams . subsetFunction' &&& (\interaction -> interactsToSpecifiedCondition intrpr' [interaction]))) alph
        where
        -- `interactsToSpecifiedCondition` puts the (single) step's variables in SSA form, indexing them with `_0`, so
        -- index the gate parameters we solve for and read the solution back from with the same suffix. Otherwise the
        -- SMT declarations (taken from these parameters) wouldn't match the variables mentioned in the guard.
        indexParams (SymInteract g' params) = SymInteract g' (mapSome (indexVar 0) <$> params)


interactsToSpecifiedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToSpecifiedCondition = interactsToGuard asDualExpr

interactsToAllowedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToAllowedCondition = interactsToGuard asExpr

interactsToGuard :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a))
    => (m SymGuard -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToGuard f intrpr interacts = f (treeToGuard f interacts BM.<#> seTree intrpr)

{- |
    map a symbolic execution tree to the path condition for a given sequence of interactions, where 
    the monadic branching at each step is collapsed with @f@.
-}
treeToGuard :: (BM.BoundedMonad m, Ord i)
    => (m SymGuard -> SymGuard) -> [i] -> SETree m i -> SymGuard
treeToGuard _ [] _ = sTrue
treeToGuard f (i:is) (SETree setree) = f (stepGuard BM.<#> Map.findWithDefault err i setree)
    where
    stepGuard (SEIte g tTree fTree) = (g .&& f (treeToGuard f is BM.<#> tTree)) .|| (sNot g .&& f (treeToGuard f is BM.<#> fTree))
    err = throw $ ActionOutsideAlphabet callStack

-- | The symbolic state: the location and the mapping of state variables to /indexed/ interaction variables. 
data SymIntrpState loc = SymIntrpState loc VarModel deriving (Eq, Ord)

intrpStateToSym :: IntrpState a -> SymIntrpState a
intrpStateToSym (IntrpState loc vals) = SymIntrpState loc (mapVars (indexVar 0) (valuationToVarModel vals))

-- | Symbolic if-then-else branching
data SEIte t = SEIte SymGuard t t deriving (Eq, Ord)

{- |
    Symbolic execution tree: every interaction monadically leads to guards (over parameters in that interaction, and in previous interactions) and new trees (for the true/false branches).

    Note: the if-then-else @SEIte@ type allows quite general forms of monadic branching, but currently, the use in @seTree@ is quite limited: the
    then-branch is always singular (ordReturn) and the else-branch is always underspecified or forbidden.
-}
newtype SETree m i = SETree (Map.Map i (m (SEIte (m (SETree m i)))))
deriving instance (Ord i, forall a. Ord a => Ord (m a)) => Eq (SETree m i)
deriving instance (Ord i, forall a. Ord a => Ord (m a)) => Ord (SETree m i)

seTree :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a))
    => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> m (SETree m (IOSymInteract i o))
seTree intrpr =
    let smlocs = intrpStateToSym BM.<#> stateConf intrpr
    in seTree' 0 BM.<#> smlocs
    where
    --t :: loc -> Map.Map (IOSymInteract i o) (m (SymGuard, VarModel, loc))
    t loc = Map.map (BM.ordMap completeSTSLoc) (transRel (syntacticAutomaton intrpr) loc)
    --seTree' :: Int -> SymIntrpState loc -> SETree m i
    -- the LHS pvar contains the indexed vars of the previous step, RHS contains only interaction variables
    seTree' n (SymIntrpState ploc pvar) = SETree $ Map.mapWithKey (BM.ordMap . seStep') (t ploc)
        where
        --seStep' :: (SymGuard, VarModel, loc) -> SEBranch (SETree m i)
        seStep' i (tguard, completedAssign, tloc) =
            let indexedGuard = subst pvar (indexExpr n tguard)
                pvar' = substVarModel pvar (indexLeft (n+1) $ indexRight n completedAssign)
                nextSeTree = BM.ordReturn $ seTree' (n+1) (SymIntrpState tloc pvar')
                negNextSeTree = ioInteractToImpliticLocation i
            in SEIte indexedGuard nextSeTree negNextSeTree
        indexLeft :: Int -> VarModel -> VarModel
        indexLeft k = mapVars $ indexVar k
        indexRight :: Int -> VarModel -> VarModel
        indexRight k = mapVarExprs $ indexVar k
    completeSTSLoc :: (STStdest, loc) -> (SymGuard, VarModel, loc)
    completeSTSLoc (STSLoc (tguard, tassign), tloc) =
        let completedAssign = tassign `varUnion` identityVarModel locVarSet
        in (tguard, completedAssign, tloc)
    locVarSet :: [Some Variable]
    locVarSet = -- a bit hacky: we assume that there is a global set of state variables, but we extract it from the assignment of an arbitrary transition
        let mArbitraryState = toList (stateConf intrpr) List.!? 0
        in case mArbitraryState of
            Just (IntrpState _ arbitraryValuation) -> getVariables arbitraryValuation
            Nothing -> []
    ioInteractToImpliticLocation (SymInteract (In _) _) = BM.underspecified -- this shouldn't be hard-coded
    ioInteractToImpliticLocation (SymInteract (Out _) _) = BM.forbidden

indexExpr :: Int -> Expr t -> Expr t
indexExpr n = mapExpressionVars (indexVar n)

indexVar :: Int -> Variable a -> Variable a
indexVar 0 v = v
indexVar n v  -- don't add a suffix for 0 primes, this avoids dealign with primes in a 1-step lookahead
    | n < 0 = error $ "left symbolic variable with index " ++ show n
    | otherwise = v {varName = varName v ++ "_" ++ show n} -- Hack. Ideally we have a nice representation which avoids collisions, and maybe a statically typed distinction between primed and unprimed variables


