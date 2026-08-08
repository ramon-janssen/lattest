{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
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
SeTree(..),
SeBranch(..),
interactsToSeTree,
foldSeTree,
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard, IOSymInteract, IOAct(..))
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asExpr, asDualExpr)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.StandardAutomata(STS)
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential)
import Lattest.Model.Symbolic.Expr(substConst, Expr(..), VarModel, valuationToVarModel, sFalse, sTrue, sConst, (.&&), (.||), sAnd, sOr, sNot, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, varsToGuard, identityVarModel, getVariables)
import Lattest.SMT.SMT(SMT)
import Lattest.Util.Utils(takeJusts, distributeFirstMaybe)

import Control.Arrow((&&&), first, second)
import Control.Exception(throw)

import Data.Foldable(toList)
import Data.Kind(Constraint)
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

-- FIXME replace 1-step `interactToGuard` and `stateAndInteractToGuards` by the n-step variants below, which should should subsume this
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





interactsToSpecifiedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToSpecifiedCondition intrpr interacts = interactsToGuard asDualExpr intrpr interacts

interactsToAllowedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToAllowedCondition intrpr interacts = interactsToGuard asDualExpr intrpr interacts



data SymIntrpState loc = SymIntrpState loc VarModel deriving (Eq, Ord)

intrpStateToSym :: IntrpState a -> SymIntrpState a
intrpStateToSym (IntrpState loc vals) =
    let abstractVarModel = valuationToVarModel vals
    in SymIntrpState loc abstractVarModel

-- | A quantified 'Ord' constraint on the state-configuration monad, needed to map the intermediate 'SeTree'
-- (and its 'SeBranch'es) into the (ordered) monad while building it.
type OrdConfig m = (forall a. Ord a => Ord (m a)) :: Constraint

{-|
    Intermediate representation of the symbolic execution of a trace. It retains the /sequence/, /if-then-else/ and
    /monad/ structure of the execution, before it is folded into a single boolean guard by 'foldSeTree'. Keeping this
    structure available (rather than folding it away in one pass) makes the resulting guards much easier to inspect and
    debug: the shape of the tree mirrors the shape of the trace and the branching of the automaton.
-}
data SeTree m
    = SeLeaf SymGuard                 -- ^ a terminal guard: the end of the trace has been reached
    | SeSeq SymGuard (m (SeBranch m)) -- ^ a sequential step: an assignment guard, conjoined with a monadic choice of branches
    | SeConf (m (SeTree m))           -- ^ the (monadic) state configuration the trace starts from

-- | A single branch of a step: the if-then-else on a transition guard.
data SeBranch m
    = SeIte SymGuard (SeTree m) (m SymGuard) -- ^ if the (indexed) guard holds, continue with the subtree, else fall through to the implicit destination

-- Equality and ordering are only needed so the tree can be mapped into the (ordered) state-configuration monad. They
-- are defined via 'compare' so that a single quantified 'Ord' constraint on the monad ('OrdConfig') suffices.
instance OrdConfig m => Eq (SeTree m) where
    a == b = compare a b == EQ
instance OrdConfig m => Ord (SeTree m) where
    compare (SeLeaf g1) (SeLeaf g2) = compare g1 g2
    compare (SeLeaf _) _ = LT
    compare _ (SeLeaf _) = GT
    compare (SeSeq g1 b1) (SeSeq g2 b2) = compare g1 g2 <> compare b1 b2
    compare (SeSeq _ _) _ = LT
    compare _ (SeSeq _ _) = GT
    compare (SeConf c1) (SeConf c2) = compare c1 c2
instance OrdConfig m => Eq (SeBranch m) where
    a == b = compare a b == EQ
instance OrdConfig m => Ord (SeBranch m) where
    compare (SeIte g1 t1 e1) (SeIte g2 t2 e2) = compare g1 g2 <> compare t1 t2 <> compare e1 e2

interactsToGuard :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m)
    => (m SymGuard -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToGuard f intrpr interacts = foldSeTree f (interactsToSeTree intrpr interacts)

{-|
    Fold the intermediate 'SeTree' into a single boolean guard. The subalgebra @f@ reduces each monadic state
    configuration to a guard (e.g. via 'asExpr' for the allowed condition, or 'asDualExpr' for the specified one);
    it is the only place where the specified/allowed distinction enters, so both conditions share the same tree.

    Structurally: a sequential step becomes a conjunction of the assignment guard with the folded branches, and each
    if-then-else branch becomes @(guard ∧ then) ∨ (¬guard ∧ else)@ where the else falls through to the implicit
    destination.
-}
foldSeTree :: BM.OrdFunctor m => (m SymGuard -> SymGuard) -> SeTree m -> SymGuard
foldSeTree _ (SeLeaf g) = g
foldSeTree f (SeConf c) = f (foldSeTree f BM.<#> c)
foldSeTree f (SeSeq assignGuard branches) = assignGuard .&& f (foldSeBranch f BM.<#> branches)

foldSeBranch :: BM.OrdFunctor m => (m SymGuard -> SymGuard) -> SeBranch m -> SymGuard
foldSeBranch f (SeIte guard thenTree implicit) =
    (guard .&& foldSeTree f thenTree) .|| (sNot guard .&& f implicit) -- The implicit transition destination is a bit hacky

{-|
    Build the intermediate 'SeTree' for a trace of interactions, capturing the symbolic execution as a tree of
    sequential steps and if-then-else branches over the state-configuration monad, without yet folding it to a guard.
-}
interactsToSeTree :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc, OrdConfig m)
    => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SeTree m
interactsToSeTree intrpr interacts =
    let smloc = intrpStateToSym BM.<#> stateConf intrpr
    in SeConf (interactsToSeTree' 0 interacts BM.<#> smloc)
    where
    t i loc = completeSTSLoc BM.<#> Map.findWithDefault err i (transRel (syntacticAutomaton intrpr) loc)
    err = throw $ ActionOutsideAlphabet callStack
    --interactsToSeTree' :: Int -> [IOSymInteract i o] -> SymIntrpState loc -> SeTree m
    interactsToSeTree' _ [] _ = SeLeaf sTrue
    interactsToSeTree' n (i:is) sloc = seStep n (ioInteractToImpliticLocation i) (interactsToSeTree' (n+1) is) (t i) sloc
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

-- | Build one step of the intermediate tree: an assignment guard, together with a monadic choice of if-then-else
-- branches (one per transition), each continuing with the expansion of its destination state.
seStep :: (BM.OrdFunctor m, OrdConfig m)
    => Int -- ^ Step number
    -> m SymGuard -- ^ implicit transition destination if a guard is false
    -> (SymIntrpState loc -> SeTree m) -- ^ function to expand symbolic destination states, potentially to further steps
    -> (loc -> m (SymGuard, VarModel, loc)) -- ^ transition function
    -> SymIntrpState loc -- ^ The current state to step from
    -> SeTree m -- ^ resulting subtree
seStep n implicit expand t (SymIntrpState ploc pvars) = SeSeq (varsToGuard indexedAssign) (seStep' BM.<#> t ploc)
    where
    indexedAssign = indexLeft n $ indexRight (n-1) pvars -- n-1 should be safe: at n=0, all assigned expressions should be constants
    seStep' (tguard, completedAssign, tloc) =
        let indexedGuard = indexExpr n tguard
        in SeIte indexedGuard (expand (SymIntrpState tloc completedAssign)) implicit
    indexLeft :: Int -> VarModel -> VarModel
    indexLeft n' = mapVars $ indexVar n'
    indexRight :: Int -> VarModel -> VarModel
    indexRight n' = mapVarExprs $ indexVar n'

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

toSpecifiedTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSpecifiedTree = toSolveTree asDualExpr

toAllowedTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toAllowedTree = toSolveTree asExpr

toSolveTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m) => (m (Expr Bool) -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSolveTree f intrpr = toSolveTree' f intrpr []
    where
    toSolveTree' :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, OrdConfig m) => (m (Expr Bool) -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SolveTree (IOAct i o)
    toSolveTree' f intrpr pref =
        let children = Map.fromSet (\x -> toSolveTree' f intrpr (pref ++ [x])) (alphabet $ syntacticAutomaton intrpr)
        in SolveTree (interactsToGuard f intrpr pref) children
