{-# OPTIONS_HADDOCK hide, prune #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
module Lattest.Model.Symbolic.SolveSymPrim (
combineGuards,
substituteInGuard,
evaluateGuard,
solveAnySequential,
solveGuard
) where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard)
import Lattest.Model.BoundedMonad(BooleanConfiguration, OrdFunctor, asDualExpr)
import qualified Lattest.Model.Symbolic.Expr as E
import Lattest.Model.Symbolic.Expr (Valuation,Variable(..), runValuation, eval, substConst)
import Lattest.Model.Symbolic.Internal.ExprDefs (ExprType)
import Lattest.SMT(pop,getSolution,addAssertions,addDeclarations,getSolvable,push,SolvableProblem(..),SMT)

import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Data.Constraint.Extras (Has(..))

{-|
    Combine the given guards into one.
-}
combineGuards :: (BooleanConfiguration m, OrdFunctor m) => m SymGuard -> SymGuard
combineGuards = asDualExpr

{-|
    In the given guard, substitute the given valuation.
-}
substituteInGuard :: Valuation -> SymGuard -> SymGuard
--substituteInGuard valuation guard = evalConst' valuation guard
substituteInGuard = substConst

{-|
    Evaluate the given guard
-}
evaluateGuard :: SymGuard -> Bool
evaluateGuard guard = case eval guard of
    Left e -> error e -- TODO proper exception
    Right b -> b

{-|
    For the given list of interactions and guards, using SMT solving, pick the first interaction in that list for which the guard is satisfiable, if
    any. The returned gate values for that interaction are not randomized in any way, picking values is left to the SMT solver.
-}
solveAnySequential :: [(SymInteract g,SymGuard)] -> SMT (Maybe (GateValue g))
solveAnySequential [] = return Nothing
solveAnySequential ((interact'@(SymInteract _ vars),guard):alph) = do
    maybeSolved <- solveGuard vars guard
    case maybeSolved of
        Nothing -> solveAnySequential alph
        Just solved -> return $ Just $ valuationToGateValue interact' solved
--data SymInteract g = SymInteract g [Variable]
--data GateValue g = GateValue g [Constant]
valuationToGateValue :: SymInteract g -> Valuation -> GateValue g
valuationToGateValue (SymInteract g' params) valuation =
    GateValue g' $ fmap (getValueForVar $ runValuation valuation) params
    where
        getValueForVar :: DMap.DMap Variable E.Val -> Some Variable -> Some E.Constant
        getValueForVar val' (Some var) =
            case DMap.lookup var val' of
                Just (E.Val value) -> case varType var of
                  E.IntType -> E.int value
                  E.FloatType -> E.float value
                  E.BoolType -> E.bool value
                  E.CharType -> E.char value
                  E.ListType t -> has @ExprType t E.list value
                  E.SetType t -> has @ExprType t E.set value
                  E.TupleType a b -> has @ExprType a $ has @ExprType b $ let (x,y) = value in E.tuple x y
                  E.SumType a b -> has @ExprType a $ has @ExprType b $ E.option value
                Nothing -> undefined  "valuationToGateValue: wrong type" -- TODO throw exception. Static type checking is infeasible due to external SMT solving. Should not happen if SMT solver behaves properly.

solveGuard :: [Some Variable] -> SymGuard -> SMT (Maybe Valuation)
solveGuard vars guard = do
    push
    addDeclarations vars
    addAssertions [guard]
    solveOutcome <- getSolvable
    mSolution <- case solveOutcome of
        Sat -> do
            solution <- getSolution vars
            return $ Just solution
        Unsat -> return Nothing
        Unknown -> return Nothing
        --_ -> return $ error $ "error solving guard " ++ show guard ++ " [" ++ show vars ++ "]"
    pop
    return mSolution
