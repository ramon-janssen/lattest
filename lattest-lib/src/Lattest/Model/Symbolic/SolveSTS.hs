{-# LANGUAGE TupleSections #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
solveAnySequential,
combineGuards,
substituteInGuard
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard)
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asDualValExpr)
import Lattest.Model.StandardAutomata(STS, STSIntrp)
import Lattest.Model.Symbolic.ValExpr.ValExpr(Valuation,Variable(..))
import Lattest.Model.Symbolic.ValExpr.ValExprDefs(ValExprBoolView(VBoolConst), ValExpr(..))
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
solveRandomInteraction :: (Monad m, BooleanConfiguration m, Ord g, RandomGen r) => STSIntrp m loc g -> (SymInteract g -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    fmap (,r') $ solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (Monad m, BooleanConfiguration m, Ord g) => STSIntrp m loc g -> (SymInteract g -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr subsetFunction =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr
        in takeJusts $ fmap (distributeFirstMaybe . (subsetFunction &&& interactToGuard intrpr)) $ alph

{-|
    For the given list of interactions and guards, using SMT solving, pick the first interaction in that list for which the guard is satisfiable, if
    any. The returned gate values for that interaction are not randomized in any way, picking values is left to the SMT solver.
-}
solveAnySequential :: [(SymInteract g,SymGuard)] -> SMT (Maybe (GateValue g))
solveAnySequential [] = return Nothing
solveAnySequential ((interact@(SymInteract _ vars),guard):alph) = do
    maybeSolved <- solveGuard vars guard
    case maybeSolved of
        Nothing -> solveAnySequential alph
        Just solved -> return $ Just $ valuationToGateValue interact solved

solveGuard :: [Variable] -> SymGuard -> SMT (Maybe Valuation)
solveGuard vars guard = do
    solveOutcome <- getSolvable
    case solveOutcome of
        Sat -> do
            push
            addAssertions [guard]
            solution <- getSolution vars
            pop
            return $ Just solution
        Unsat -> return Nothing
        Unknown -> return Nothing

valuationToGateValue :: SymInteract g -> Valuation -> GateValue g
valuationToGateValue (SymInteract gate params) valuation =
    GateValue gate $ fmap (getValueForVar valuation) params
    where
        getValueForVar valuation var =
            case Map.lookup var valuation of
                Just value -> value
                Nothing -> undefined  "valuationToGateValue: wrong type" -- TODO throw exception. Static type checking is infeasible due to external SMT solving. Should not happen if SMT solver behaves properly.

interactToGuard :: (Monad m, BooleanConfiguration m, Ord g) => STSIntrp m loc g -> SymInteract g -> SymGuard
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


{-|
    Combine the given guards into one.
-}
combineGuards :: (BooleanConfiguration m, Functor m) => m SymGuard -> SymGuard
combineGuards = asDualValExpr

{-|
    In the given guard, substitute the given valuation.
-}
substituteInGuard :: Valuation -> SymGuard -> SymGuard
substituteInGuard valuation guard = evalConst' valuation guard

{-|
    Evaluate the given guard
-}
evaluateGuard :: SymGuard -> Boolean
evaluateGuard guard = case evalConst guard of
    Left e = error e -- TODO proper exception
    Right (Cbool b) = b
