{-# OPTIONS_HADDOCK hide, prune #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
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
import Lattest.Model.Symbolic.Expr (Valuation,Variable(..), runValuation, eval, substConst, Val (..), Expr)
import Lattest.Model.Symbolic.Internal.ExprDefs (ExprType)
import Lattest.SMT(getSolution,addAssertions,addDeclarations,getSolvable,SolvableProblem(..), runSMT, query, SMTQ, addAssertionsQ)

import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Data.Constraint.Extras (Has(..))
import System.Random ( randomIO, randomR )
import System.Random.Stateful ( mkStdGen, StdGen )
import Data.Dependent.Sum (DSum (..))

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
solveAnySequential :: [(SymInteract g,SymGuard)] -> IO (Maybe (GateValue g))
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
                  E.UnitType -> E.unit
                  E.FloatType -> E.float value
                  E.BoolType -> E.bool value
                  E.CharType -> E.char value
                  E.ListType t -> has @ExprType t E.list value
                  E.SetType t -> has @ExprType t E.set value
                  E.TupleType a b -> has @ExprType a $ has @ExprType b $ let (x,y) = value in E.tuple x y
                  E.SumType a b -> has @ExprType a $ has @ExprType b $ E.option value
                Nothing -> undefined  "valuationToGateValue: wrong type" -- TODO throw exception. Static type checking is infeasible due to external SMT solving. Should not happen if SMT solver behaves properly.

solveGuard :: [Some Variable] -> SymGuard -> IO (Maybe Valuation)
solveGuard vars guard = do
  randomgen <- mkStdGen <$> randomIO
  runSMT do
    addDeclarations vars
    addAssertions [guard]
    -- Only one `query` block is allowed in a Symbolic. solveGuard returns an IO to avoid running into this problem.
    -- Since sbv-14.8 (unreleased), addAssertions on higher order functions no longer need registerFunction to work in query.
    -- This means that we will be able to change back to having our SMT type being what our SMTQ type is now; and having solveGuard return that.
    query $ do
      solveOutcome <- getSolvable
      case solveOutcome of
        Unsat -> return Nothing
        Unknown -> return Nothing
        Sat -> go randomgen 20 []
  where
    go :: StdGen -> Int -> [Valuation] -> SMTQ (Maybe Valuation)
    go g 0 xs = do
      let (ix,_) = randomR (0, length xs - 1) g
      pure $ Just $ xs !! ix
    go g n xs = do
      addAssertionsQ $ map atleastoneisdifferent xs
      getSolvable >>= \case
        Unsat -> go g 0 xs
        Unknown -> go g 0 xs
        Sat -> do
          x <- getSolution vars
          go g (n-1) (x : xs)

    atleastoneisdifferent :: Valuation -> SymGuard
    atleastoneisdifferent = foldr ((E..||) . isNot) E.sFalse . DMap.assocs . runValuation

    -- for doubles, enforce a distance of at least 0.1
    isNot :: DSum Variable Val -> Expr Bool
    isNot (var@(Variable _ E.FloatType) :=> (Val val)) = E.sVar var E..< E.sConst (val - 0.1) E..|| E.sVar var E..> E.sConst (val + 0.1)
    isNot (var :=> (Val val)) = E.sNot $ E.sVar var E..== E.sConst val
