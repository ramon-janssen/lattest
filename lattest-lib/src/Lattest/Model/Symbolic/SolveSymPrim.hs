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
valuationToGateValue,
solveGuard, solveGuardAny, solveGuardIO,
isGuardSatisfiable
) where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard)
import Lattest.Model.BoundedMonad(BooleanConfiguration, OrdFunctor, asDualExpr)
import qualified Lattest.Model.Symbolic.Expr as E
import Lattest.Model.Symbolic.Expr (Valuation,Variable(..), runValuation, eval, substConst, Val (..), Expr)
import Lattest.Model.Symbolic.Internal.ExprDefs (ExprType, Expr (..))
import Lattest.SMT(getSolution,addAssertions,addDeclarations,getSolvable,SolvableProblem(..), runSMT, query, SMTQ, addAssertionsQ, sortOfEqualWith, push, pop)

import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Data.Constraint.Extras (Has(..))
import System.Random ( randomR, RandomGen, mkStdGen, randomIO )
import Data.Dependent.Sum (DSum (..))
import Control.Monad.State (StateT (..), evalStateT)
import Control.Monad.IO.Class (liftIO)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad (forM_)

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
solveAnySequential :: RandomGen randomgen => [(SymInteract g,SymGuard)] -> StateT randomgen IO (Maybe (GateValue g))
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
                  E.RationalType -> E.rational value
                  E.RealType -> E.real value
                  E.BoolType -> E.bool value
                  E.CharType -> E.char value
                  E.ListType t -> has @ExprType t E.list value
                  E.SetType t -> has @ExprType t E.set value
                  E.TupleType a b -> has @ExprType a $ has @ExprType b $ let (x,y) = value in E.tuple x y
                  E.SumType a b -> has @ExprType a $ has @ExprType b $ E.option value
                Nothing -> undefined  "valuationToGateValue: wrong type" -- TODO throw exception. Static type checking is infeasible due to external SMT solving. Should not happen if SMT solver behaves properly.

{-|
    Check whether the given guard is satisfiable, without obtaining a valuation. If the SMT solver can not tell, the guard is reported
    as not satisfiable, with a warning on stderr.

    The outcome is cached per guard, so that a guard is only solved once. Outcomes where the SMT solver could not tell are not cached.
-}
isGuardSatisfiable :: [Some Variable] -> SymGuard -> IO Bool
isGuardSatisfiable vars guard = do
  cache <- readIORef satisfiableCache
  case Map.lookup guard cache of
    Just isSat -> return isSat
    Nothing -> do
      g <- mkStdGen <$> randomIO -- We don't care about the solution, only whether there is one, so randomness is acceptable here
      outcome <- fst $ runSMT g do
        addDeclarations vars
        addAssertions [guard]
        query $ getSolvable >>= \case
          Sat -> return $ Just True
          Unsat -> return $ Just False
          Unknown -> Nothing <$ warnUnknown guard
      forM_ outcome \isSat -> atomicModifyIORef' satisfiableCache $ \c -> (Map.insert guard isSat c, ())
      return outcome

-- the guards solved so far by `isGuardSatisfiable`, with their outcome
satisfiableCache :: IORef (Map.Map SymGuard Bool)
satisfiableCache = unsafePerformIO $ newIORef Map.empty
{-# NOINLINE satisfiableCache #-}

warnUnknown :: SymGuard -> SMTQ ()
warnUnknown guard = liftIO $ hPutStrLn stderr $ "warning: SMT solver returned unknown, treating as unsatisfiable: " <> show guard

solveGuardIO :: [Some Variable] -> SymGuard -> IO (Maybe Valuation)
solveGuardIO vars guard = do
  g <- mkStdGen <$> randomIO
  evalStateT (solveGuard vars guard) g

solveGuard :: RandomGen g => [Some Variable] -> SymGuard -> StateT g IO (Maybe Valuation)
solveGuard = solveGuardAmong 10

-- | As 'solveGuard', but takes the first solution that the SMT solver comes up with, instead of picking randomly among several solutions.
solveGuardAny :: RandomGen g => [Some Variable] -> SymGuard -> StateT g IO (Maybe Valuation)
solveGuardAny = solveGuardAmong 0

-- solve the guard, picking randomly among the first solution and up to the given number of additional, different solutions.
-- If the SMT solver can not tell whether there is a (further) solution, then that is
-- treated as there being none, with a warning.
solveGuardAmong :: RandomGen g => Int -> [Some Variable] -> SymGuard -> StateT g IO (Maybe Valuation)
solveGuardAmong extraSolutions vars guard = StateT $ \randomgen ->
  fst $ runSMT randomgen do
    addDeclarations vars
    -- addDeclarations (Set.toList $ freeVars guard)
    addAssertions [guard]
    -- Only one `query` block is allowed in a Symbolic. solveGuard returns an IO to avoid running into this problem.
    -- Since sbv-14.8 (unreleased), addAssertions on higher order functions no longer need registerFunction to work in query.
    -- This means that we will be able to change back to having our SMT type being what our SMTQ type is now; and having solveGuard return that.
    query $ do
      solveOutcome <- getSolvable
      case solveOutcome of
        Unsat -> return (Nothing, randomgen)
        Unknown -> (Nothing, randomgen) <$ warnUnknown guard
        Sat -> getSolution vars >>= \x -> go randomgen extraSolutions True x []
  where
    -- the solutions found so far are the newest one and the older ones. The flag tells whether to still try to find
    -- a solution in which every variable differs from all solutions found so far.
    go :: RandomGen g => g -> Int -> Bool -> Valuation -> [Valuation] -> SMTQ (Maybe Valuation, g)
    go g 0 _ x xs = do
      let (ix, g') = randomR (0, length xs) g
      pure (Just $ (x : xs) !! ix, g')
    go g n tryAllDifferent x xs = do
      -- assertions accumulate, so only the newest solution has to be excluded
      addAssertionsQ [atleastoneisdifferent x]
      allDifferent <- if tryAllDifferent then solveAllDifferent (x : xs) else pure Nothing
      case allDifferent of
        Just x' -> go g (n-1) True x' (x : xs)
        -- once no solution differs in every variable, adding more solutions will not change that
        Nothing -> getSolvable >>= \case
          Unsat -> go g 0 False x xs
          Unknown -> warnUnknown guard >> go g 0 False x xs
          Sat -> do
            x' <- getSolution vars
            go g (n-1) False x' (x : xs)

    -- look for a solution in which every variable differs from the given solutions, without keeping that requirement
    -- afterwards. Variables that can only have one value are ignored.
    solveAllDifferent :: [Valuation] -> SMTQ (Maybe Valuation)
    solveAllDifferent xs = do
      push
      addAssertionsQ [ isNot v | x <- xs, v <- DMap.assocs $ runValuation x, hasMultipleValues v ]
      outcome <- getSolvable
      x' <- case outcome of
        Sat -> Just <$> getSolution vars
        _ -> pure Nothing
      pop
      pure x'

    hasMultipleValues :: DSum Variable Val -> Bool
    hasMultipleValues (var :=> _) = case varType var of
      E.UnitType -> False
      _ -> True

    atleastoneisdifferent :: Valuation -> SymGuard
    atleastoneisdifferent = foldr ((E..||) . isNot) E.sFalse . DMap.assocs . runValuation

    -- for doubles, rationals and reals, enforce a distance of at least 0.1
    isNot :: DSum Variable Val -> Expr Bool
    isNot (var :=> (Val val)) = E.sNot $ Expr $ sortOfEqualWith True 0.1 (E.Var var) (E.Const val)
