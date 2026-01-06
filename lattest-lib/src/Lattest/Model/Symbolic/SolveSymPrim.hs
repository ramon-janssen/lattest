module Lattest.Model.Symbolic.SolveSymPrim (
combineGuards,
substituteInGuard,
evaluateGuard,
solveAnySequential
) where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asDualValExpr)
import Lattest.Model.Symbolic.ValExpr.ValExpr(Valuation,Variable(..))
import Lattest.Model.Symbolic.ValExpr.ValExprDefs(eval)
import Lattest.Model.Symbolic.ValExpr.ValExprImpls(evalConst')
import Lattest.Model.Symbolic.ValExpr.Constant(Constant(Cbool))
import Lattest.SMT.SMT(pop,getSolution,addAssertions,getSolvable,push,SolvableProblem(..),SMT)

import qualified Data.Map as Map

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
evaluateGuard :: SymGuard -> Bool
evaluateGuard guard = case eval guard of
    Left e -> error e -- TODO proper exception
    Right (Cbool b) -> b

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

valuationToGateValue :: SymInteract g -> Valuation -> GateValue g
valuationToGateValue (SymInteract gate params) valuation =
    GateValue gate $ fmap (getValueForVar valuation) params
    where
        getValueForVar valuation var =
            case Map.lookup var valuation of
                Just value -> value
                Nothing -> undefined  "valuationToGateValue: wrong type" -- TODO throw exception. Static type checking is infeasible due to external SMT solving. Should not happen if SMT solver behaves properly.

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