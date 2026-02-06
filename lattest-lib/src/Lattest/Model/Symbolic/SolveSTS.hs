{-# LANGUAGE TupleSections #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard)
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asDualValExpr)
import Lattest.Model.StandardAutomata(STS)
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential)
import Lattest.Model.Symbolic.ValExpr.ValExpr(Valuation,Variable(..))
import Lattest.Model.Symbolic.ValExpr.ValExprDefs(ValExprBoolView(BoolConst), ValExpr(..), eval)
import Lattest.Model.Symbolic.ValExpr.ValExprImpls(evalConst')
import Lattest.Model.Symbolic.ValExpr.Constant(Constant(Cbool))
import Lattest.SMT.SMT(SMTRef,pop,getSolution,addAssertions,getSolvable,push,Solution,SolvableProblem(..),SMT)
import Lattest.Util.Utils(takeJusts, distributeFirstMaybe)

import Control.Arrow((&&&))
import Control.Exception(throw)
import Control.Monad(join)
import Data.Foldable(toList)
import qualified Data.Map as Map
import GHC.Stack(callStack)
import List.Shuffle(shuffle)
import System.Random(RandomGen)

{-|
    For the given STS and a subset function, using SMT solving, find a interaction of the STS in that subset for which the guard is true from the
    current STS state. The interaction is picked uniformly randomly among interactions with satisfied gates, if any. This uses the supplied random 
    generator and returns the new random generator state. The returned gate values for that interaction are not randomized in any way, picking values
    is left to the SMT solver.
-}
solveRandomInteraction :: (Monad m, BooleanConfiguration m, Ord g, RandomGen r) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g'') -> (SymInteract g -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    fmap (,r') $ solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (Monad m, BooleanConfiguration m, Ord g) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g'') -> (SymInteract g -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr subsetFunction =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr
        in takeJusts $ fmap (distributeFirstMaybe . (subsetFunction &&& interactToGuard intrpr)) $ alph

interactToGuard :: (Monad m, BooleanConfiguration m, Ord g) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') -> SymInteract g -> SymGuard
interactToGuard intrpr interaction = let
        aut = syntacticAutomaton intrpr
    in asDualValExpr $ join $ stateAndInteractToGuards aut interaction <$> stateConf intrpr

stateAndInteractToGuards :: (Ord g, Functor m) => STS m loc g -> SymInteract g -> IntrpState loc -> m SymGuard
stateAndInteractToGuards aut interaction intrpr@(IntrpState l valuation) =
    case Map.lookup interaction (transRel aut l) of
        Nothing -> throw $ ActionOutsideAlphabet callStack
        Just mtdestloc -> fmap guardAndLocToGuard mtdestloc
    where
    guardAndLocToGuard (STSLoc (tguard,_), _) = evalConst' valuation tguard



