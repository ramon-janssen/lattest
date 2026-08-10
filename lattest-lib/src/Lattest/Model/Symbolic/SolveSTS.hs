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
import Lattest.Model.Symbolic.Expr(substConst, subst, substVarModel, Expr(..), VarModel, valuationToVarModel, sFalse, sTrue, sConst, (.&&), (.||), sAnd, sOr, sNot, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, identityVarModel, getVariables, noAssignment)
import Lattest.SMT(SMT)
import Lattest.Util.Utils(distributeFirstMaybe)

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
intrpStateToSym (IntrpState loc vals) =
    SymIntrpState loc (valuationToVarModel vals) noAssignment -- no state variables resolved yet at the start of the trace

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
    | SeSeq VarModel (m (SeBranch m)) -- ^ a sequential step: the (resolved) assignment applied at this step, kept for
                                      --   inspection only — it is /not/ folded into the guard — together with a monadic
                                      --   choice of branches. State variables are substituted out of the branch guards
                                      --   using this assignment, so the folded guard mentions interaction variables only.
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

-- | Compute the guard of a trace by folding the symbolic execution into a boolean as it is walked
interactsToGuard :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc)
    => (m SymGuard -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToGuard f intrpr interacts =
    let smloc = intrpStateToSym BM.<#> stateConf intrpr
    in f (goTrace 0 interacts BM.<#> smloc)
    where
    goTrace _ [] _ = sTrue
    goTrace n (i:is) sloc = goStep n (implicitLocation i) (goTrace (n+1) is) (transitionAt intrpr i) sloc
    -- fused counterpart of 'seStep': same SSA bookkeeping, but each branch folds straight to a guard
    goStep n implicit expand t (SymIntrpState ploc prevAssign sigma) = f (branchGuard BM.<#> t ploc)
        where
        indexedAssign = indexLeft n $ indexRight (n-1) prevAssign
        resolvedAssign = substVarModel sigma indexedAssign
        sigma' = resolvedAssign `varUnion` sigma
        branchGuard (tguard, completedAssign, tloc) =
            let indexedGuard = subst sigma' (indexExpr n tguard)
            in (indexedGuard .&& expand (SymIntrpState tloc completedAssign sigma')) .|| (sNot indexedGuard .&& f implicit)

{-|
    Fold the intermediate 'SeTree' into a single boolean guard. The subalgebra @f@ reduces each monadic state
    configuration to a guard (e.g. via 'asExpr' for the allowed condition, or 'asDualExpr' for the specified one);
    it is the only place where the specified/allowed distinction enters, so both conditions share the same tree.

    Structurally: a sequential step folds to just its branches (the assignment carried by the step is not conjoined —
    it has already been substituted into the branch guards, see 'seStep'), and each if-then-else branch becomes
    @(guard ∧ then) ∨ (¬guard ∧ else)@ where the else falls through to the implicit destination. Because the
    assignments are substituted rather than conjoined, the resulting guard mentions interaction variables only.
-}
foldSeTree :: BM.OrdFunctor m => (m SymGuard -> SymGuard) -> SeTree m -> SymGuard
foldSeTree _ (SeLeaf g) = g
foldSeTree f (SeConf c) = f (foldSeTree f BM.<#> c)
foldSeTree f (SeSeq _assign branches) = f (foldSeBranch f BM.<#> branches)

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
    --interactsToSeTree' :: Int -> [IOSymInteract i o] -> SymIntrpState loc -> SeTree m
    interactsToSeTree' _ [] _ = SeLeaf sTrue
    interactsToSeTree' n (i:is) sloc = seStep n (implicitLocation i) (interactsToSeTree' (n+1) is) (transitionAt intrpr i) sloc

-- | Build one step of the intermediate tree: the assignment that produced the current state (resolved to interaction
-- variables), together with a monadic choice of if-then-else branches (one per transition), each continuing with the
-- expansion of its destination state. The guard of each branch has its state variables substituted away using the
-- accumulated assignment, so that only interaction variables remain — instead of adding an assignment guard as a
-- conjunct that constrains the (internal, invisible) state variables.
seStep :: (BM.OrdFunctor m, OrdConfig m)
    => Int -- ^ Step number
    -> m SymGuard -- ^ implicit transition destination if a guard is false
    -> (SymIntrpState loc -> SeTree m) -- ^ function to expand symbolic destination states, potentially to further steps
    -> (loc -> m (SymGuard, VarModel, loc)) -- ^ transition function
    -> SymIntrpState loc -- ^ The current state to step from
    -> SeTree m -- ^ resulting subtree
seStep n implicit expand t (SymIntrpState ploc prevAssign sigma) = SeSeq resolvedAssign (seStep' BM.<#> t ploc)
    where
    -- the assignment that produced the current state's variable values, in SSA form: {x_n := E(vars_{n-1})}
    indexedAssign = indexLeft n $ indexRight (n-1) prevAssign -- n-1 should be safe: at n=0, all assigned expressions should be constants
    -- resolve its right-hand sides against the substitution accumulated so far, so they mention interaction variables
    -- only, then extend the accumulated substitution with it (its keys x_n are fresh, so the union does not clash)
    resolvedAssign = substVarModel sigma indexedAssign
    sigma' = resolvedAssign `varUnion` sigma
    seStep' (tguard, completedAssign, tloc) =
        -- index the transition guard, then substitute every state variable away, leaving interaction variables only
        let indexedGuard = subst sigma' (indexExpr n tguard)
        in SeIte indexedGuard (expand (SymIntrpState tloc completedAssign sigma')) implicit

-- Helpers shared by the tree builder ('interactsToSeTree'/'seStep') and the fused folder ('interactsToGuard'), so the
-- two agree on how the automaton is walked and only differ in what they accumulate.

-- | For interaction @i@ at location @loc@, the monadic choice of (transition guard, completed assignment, destination
-- location) triples over the outgoing transitions. The assignment is completed with an identity assignment for the
-- state variables the transition does not touch.
transitionAt :: (Ord i, Ord o, Ord loc, Foldable m, BM.OrdFunctor m)
    => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> IOSymInteract i o -> loc -> m (SymGuard, VarModel, loc)
transitionAt intrpr i loc = completeSTSLoc BM.<#> Map.findWithDefault err i (transRel (syntacticAutomaton intrpr) loc)
    where
    err = throw $ ActionOutsideAlphabet callStack
    completeSTSLoc (STSLoc (tguard, tassign), tloc) = (tguard, tassign `varUnion` identityVarModel (locVars intrpr), tloc)

-- | The state variables a transition assignment is completed over, taken from an arbitrary state valuation of the
-- interpreter's configuration.
locVars :: Foldable m => AutIntrpr m loc (IntrpState loc) t tdest act -> [Variable]
locVars intrpr = case (toList $ stateConf intrpr) List.!? 0 of
    Just (IntrpState _ arbitraryValuation) -> getVariables arbitraryValuation
    Nothing -> []

-- | The implicit transition destination taken when a transition guard is false: underspecified for inputs (they may be
-- left unspecified), forbidden for outputs. FIXME this shouldn't be hard-coded.
implicitLocation :: BM.BoundedConfiguration m => IOSymInteract i o -> m SymGuard
implicitLocation (SymInteract (In _) _) = BM.underspecified
implicitLocation (SymInteract (Out _) _) = BM.forbidden

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

toSpecifiedTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSpecifiedTree = toSolveTree asDualExpr

toAllowedTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toAllowedTree = toSolveTree asExpr

toSolveTree :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => (m (Expr Bool) -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> SolveTree (IOAct i o)
toSolveTree f intrpr = toSolveTree' f intrpr []
    where
    toSolveTree' :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc) => (m (Expr Bool) -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SolveTree (IOAct i o)
    toSolveTree' f intrpr pref =
        let children = Map.fromSet (\x -> toSolveTree' f intrpr (pref ++ [x])) (alphabet $ syntacticAutomaton intrpr)
        in SolveTree (interactsToGuard f intrpr pref) children
