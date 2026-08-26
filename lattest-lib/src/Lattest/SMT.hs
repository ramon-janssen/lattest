{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
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

import Data.SBV( constrain, SBV, SymVal (..), freshVar)
import Data.SBV.Control( CheckSatResult, checkSat, query, Query)
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import qualified Data.SBV.List as SBV
import qualified Data.SBV.Internals as SBVI -- 'unsafe' internals

import Lattest.Model.Symbolic.Expr(ExprView(..), Variable (..), Valuation, Expr, fromConstantsMap, Type (..), Constant (..), view)
import Lattest.Model.Symbolic.Internal.FreeMonoidX
import Lattest.Model.Symbolic.Internal.Sum(SumTerm(..))

import Control.Monad((<=<))
import Control.Monad.State (StateT, evalStateT, lift, modify, gets)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Model.Symbolic.Internal.Product (ProductTerm(..))

--------------------
-- exported types and functions
-- these define the interface to
-- the SMT backend
--------------------
type  Solution v       =  Map.Map v Constant
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

getSolution :: [Variable] -> SMT Valuation
getSolution vs =
  fromConstantsMap
  . Map.fromList
  <$> mapM getVarValue vs
  where
    getVarValue :: Variable -> SMT (Variable, Constant)
    getVarValue v@(Variable nm tp) = do
        sval <- gets (\m -> case m Map.!? nm of
            Nothing -> error $ show nm <> "is not in" <> show m
            Just x -> x)
        c <- lift $ svalToConstant tp sval
        return (v, c)

svalToConstant :: Type -> SBVI.SVal -> Query Constant
svalToConstant IntType    s = Cint    <$> SBV.getValue (SBVI.SBV s :: SBV Integer)
svalToConstant BoolType   s = Cbool   <$> SBV.getValue (SBVI.SBV s :: SBV Bool)
svalToConstant StringType s = Cstring <$> SBV.getValue (SBVI.SBV s :: SBV String)
svalToConstant FloatType  s = Cfloat  <$> SBV.getValue (SBVI.SBV s :: SBV Double)

addAssertions :: [Expr Bool] -> SMT ()
addAssertions = mapM_ (lift . constrain <=< exprToSymbolic . view)

-- This is the reason we have the StateT wrapper in SMT:
-- SBV wants us to keep track of the symbolic variables
-- we get on each declaration, and use them to reference
-- the variable.
addDeclarations :: [Variable] -> SMT ()
addDeclarations = mapM_ $ \(Variable nm tp) -> case tp of
  IntType -> do
    SBVI.SBV v <- freshVar @Integer nm
    modify $ Map.insert nm v
  BoolType -> do
    SBVI.SBV v <- freshVar @Bool nm
    modify $ Map.insert nm v
  StringType -> do
    SBVI.SBV v <- freshVar @String nm
    modify $ Map.insert nm v
  FloatType -> do
    SBVI.SBV v <- freshVar @Double nm
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
  Var (Variable nm _tp) -> gets (SBVI.SBV . (\m -> case m Map.!? nm of
            Nothing -> error $ show nm <> "is not in" <> show m
            Just x -> x))
  Const t -> pure $ literal t
  Ite i t e -> SBV.ite <$> go i <*> go t <*> go e
  EqualInt    l r -> (SBV..==) <$> go l <*> go r
  EqualFloat  l r -> (SBV..==) <$> go l <*> go r
  EqualString l r -> (SBV..==) <$> go l <*> go r
  EqualBool   l r -> (SBV..==) <$> go l <*> go r
  Divide      x y -> SBV.sDiv  <$> go x <*> go y
  DivideFloat x y -> (/)       <$> go x <*> go y
  Modulo x y      -> SBV.sMod  <$> go x <*> go y
  Sum      s -> foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal i               + sY) <$> go x <*> symY) (pure $ literal 0) s
  SumFloat s -> foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal (fromInteger i) + sY) <$> go x <*> symY) (pure $ literal 0) s
  Product      p -> foldOccur (\(ProductTerm x) i symY -> (\x' y -> x' ^ i * y) <$> go x <*> symY) (pure $ literal 1) p
  ProductFloat p -> foldOccur (\(ProductTerm x) i symY -> (\x' y -> x' ^ i * y) <$> go x <*> symY) (pure $ literal 1) p
  Length s -> SBV.length <$> go s
  GezInt   i -> (SBV..>= literal 0) <$> go i
  GezFloat f -> (SBV..>= literal 0) <$> go f
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

