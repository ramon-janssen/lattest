{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Lattest.SMT (
  SMT,
  SolvableProblem(..),

  addAssertions,
  addDeclarations,
  getSolution,
  getSolvable,
  pop,
  push,
  runSMT
) where

import Data.SBV( constrain, HasKind(isBoolean), SBV, SymVal (..), freshVar)
import Data.SBV.Control( CheckSatResult, checkSat, getModel, query, Query)
import Data.SBV.Internals( CV(cvVal), CVal(CString, CInteger), SMTModel(modelAssocs),cvToBool )
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import qualified Data.SBV.List as SBV
import qualified Data.SBV.Internals as SBVI -- 'unsafe' internals

import Lattest.Model.Symbolic.Expr(ExprView(..), Variable (..), Valuation, Expr, Type (..), Constant (..), view)
import Lattest.Model.Symbolic.Internal.FreeMonoidX
import Lattest.Model.Symbolic.Internal.Sum(SumTerm(..))

import Control.Monad((<=<))
import Control.Monad.State (StateT, evalStateT, lift, modify, gets)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Model.Symbolic.Internal.Product (ProductTerm(..))
import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Lattest.Model.Symbolic.Internal.ExprImpls (Val(..))

--------------------
-- exported types and functions
-- these define the interface to
-- the SMT backend
--------------------
type  Solution v       =  Map.Map v (Some Constant)
data  SolvableProblem  = Sat
                       | Unsat
                       | Unknown
     deriving (Eq,Ord,Read,Show)
data  SolveProblem v  = Solved (Solution v)
                      | Unsolvable
                      | UnableToSolve
     deriving (Eq,Ord,Read,Show)

type SMT = StateT (Map String SBVI.SVal) Query

runSMT :: SMT a -> IO a
runSMT = SBV.runSMT . query . flip evalStateT Map.empty

getSolution :: [Some Variable] -> SMT Valuation
getSolution vs =
  (\val -> DMap.intersection val $ foldr (\(Some v) -> DMap.insert v (error "dummy variable that should never be evaluated")) mempty vs)
  . sbvModelToValuation <$> lift getModel

addAssertions :: [Expr Bool] -> SMT ()
addAssertions = mapM_ (lift . constrain <=< exprToSymbolic . view)

-- This is the reason we have the StateT wrapper in SMT:
-- SBV wants us to keep track of the symbolic variables
-- we get on each declaration, and use them to reference
-- the variable.
addDeclarations :: [Some Variable] -> SMT ()
addDeclarations = mapM_ (\(Some v) -> addDeclaration v)

addDeclaration :: forall t. Variable t -> SMT ()
addDeclaration (Variable nm ty) = case ty of
  -- case split to get the SymVal instances, the alternative is to attach the constraint to the constructor Variable
  IntType -> do
    SBVI.SBV v <- freshVar @t nm
    modify $ Map.insert nm v
  BoolType -> do
    SBVI.SBV v <- freshVar @t nm
    modify $ Map.insert nm v
  StringType -> do
    SBVI.SBV v <- freshVar @t nm
    modify $ Map.insert nm v

getSolvable :: SMT SolvableProblem
getSolvable = checkSatToSolveProblem <$> lift checkSat

pop, push :: SMT ()
pop  = lift $ SBV.pop  1
push = lift $ SBV.push 1

---------------
-- Non-exported functions
---------------

-- The main translation between our Exprs and SBV's Symbolic
exprToSymbolic :: (Show a, SBV.SymVal a) => ExprView a -> SMT (SBV a)
exprToSymbolic v = case v of
  Var (Variable nm _tp) -> gets (SBVI.SBV . (Map.! nm))
  Const t -> pure $ literal t
  Ite i t e -> SBV.ite <$> go i <*> go t <*> go e
  Equal _ l r -> (SBV..==) <$> go l <*> go r
  Divide x y -> SBV.sDiv  <$> go x <*> go y
  Modulo x y -> SBV.sMod  <$> go x <*> go y
  Sum s -> foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal i + sY) <$> go x <*> symY) (pure $ literal 0) s
  Product p -> foldOccur (\(ProductTerm x) i symY -> (\x' y -> x' ^ i * y) <$> go x <*> symY) (pure $ literal 1) p
  Length s -> SBV.length <$> go s
  GezInt i -> (SBV..>= literal 0) <$> go i
  Not b -> SBV.sNot <$> go b
  And xs -> foldr (\b bs -> (SBV..&&) <$> go b <*> bs) (pure $ literal True) (Set.toList xs)
   -- The below version errors because SBV doesn't properly declare some variable
   -- My best guess is that it's a bug if you use 'and' inside a Query, but I haven't
   -- looked deep enough nor done enough testing to report as a bug.
   -- SBV.and <$> foldr (\b bs -> (SBV..:) <$> go b <*> bs) (pure SBV.nil) (Set.toList xs)
  Concat strs -> SBV.concat <$> foldr (\s ss -> (SBV..:) <$> go s <*> ss) (pure SBV.nil) strs
  where
    go :: (SBV.SymVal a, Show a) => ExprView a -> SMT (SBV a)
    go = exprToSymbolic

checkSatToSolveProblem :: CheckSatResult -> SolvableProblem
checkSatToSolveProblem = \case
  SBV.Sat -> Sat
  SBV.Unsat -> Unsat
  SBV.Unk -> Unknown
  SBV.DSat _ -> Unknown

sbvModelToValuation :: SMTModel -> Valuation
sbvModelToValuation = foldr f DMap.empty . modelAssocs
  where
    f (varname, cv) = case cvVal cv of
      -- booleans for some reason are represented as CInteger with a different 'Kind'
      _ | isBoolean cv -> DMap.insert (Variable varname BoolType) $ Val $ cvToBool cv
      CInteger i -> DMap.insert (Variable varname IntType) $ Val i
      CString s -> DMap.insert (Variable varname StringType) $ Val s
      _ -> error "todo: the other SBV types, including lists, sets, arbitrary ADTs, floating point values, etc"

