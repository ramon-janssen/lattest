{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
module Lattest.SMT (
  runSMT,
  SMTRef,
  SMT,
  pop,
  getSolution,
  addAssertions,
  addDeclarations,
  getSolvable,
  push,
  SolvableProblem(..),
  SmtEnv
) where

-- Comment this line out to use SBV, un-comment it to use TorXaKis
-- #define USE_TOR

#ifdef USE_TOR

import Lattest.SMTTor.SMT
import Lattest.SMTTor.SMTData

#else
-- The rest of this file is in the 'else' branch

import Data.SBV( constrain, HasKind(isBoolean), symbolic, Symbolic, SBV, SymVal (..), freshVar)
import Data.SBV.Control( CheckSatResult, checkSat, getModel, query, Query)
import Data.SBV.Internals( CV(cvVal), CVal(CString, CInteger), SMTModel(modelAssocs),cvToBool )
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import qualified Data.SBV.Internals as SBVI
import qualified Data.SBV.List as SBV

import Lattest.Model.Symbolic.Expr(ExprView(..), Variable (..), Valuation, Expr, fromConstantsMap, Type (..), Constant (..), toConstantsMap, view)
import Lattest.Model.Symbolic.Internal.FreeMonoidX
import Lattest.Model.Symbolic.Internal.Sum(SumTerm(..))

import Control.Monad((<=<))
import Control.Monad.State (StateT, evalStateT, lift, modify, gets)
import Data.IORef (IORef)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

--------------------
-- exported types and functions
-- these define the interface between
-- either of the SMT backends and the
-- rest of the library
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

type SMTRef = IORef ()
type SMT = StateT (Map String SBVI.SVal) Query
type SmtEnv = ()

runSMT :: SMTRef -> SMT a -> IO a
runSMT _ = SBV.runSMT . query . flip evalStateT Map.empty

getSolution :: [Variable] -> SMT Valuation
getSolution vs =
  fromConstantsMap
  . (`Map.intersection` Map.fromList (map (,()) vs))
  . toConstantsMap
  . sbvModelToValuation <$> lift getModel

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
  EqualInt    l r -> (SBV..==) <$> go l <*> go r
  EqualString l r -> (SBV..==) <$> go l <*> go r
  EqualBool   l r -> (SBV..==) <$> go l <*> go r
  Divide x y      -> SBV.sDiv  <$> go x <*> go y
  Modulo x y      -> SBV.sMod  <$> go x <*> go y
  Sum s -> foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal i + sY) <$> go x <*> symY) (pure $ literal 0) s
  -- I don't see any 'power' option in SBV (one of the examples defines power as a recursive haskell function),
  -- so we just multiply the dumb way
  Product p -> foldrTerms (\x symY -> (*) <$> go x <*> symY) (pure $ literal 1) p
  Length s -> SBV.length <$> go s
  GezInt i -> (SBV..>= literal 0) <$> go i
  Not b -> SBV.sNot <$> go b
  And xs -> foldr (\b bs -> (SBV..&&) <$> go b <*> bs) (pure $ literal True) (Set.toList xs)
   -- The below version errors because SBV doesn't properly declare some variable
   -- My best guess is that it's a bug if you use 'and' inside a Query, but I haven't
   -- looked deep enough nor done enough testing to report as a bug.
   -- SBV.and <$> foldr (\b bs -> (SBV..:) <$> go b <*> bs) (pure SBV.nil) (Set.toList xs)
  Concat strs -> SBV.concat <$> foldr (\s ss -> (SBV..:) <$> go s <*> ss) (pure SBV.nil) strs
  -- At :: {string2 :: ExprView String, position2 :: ExprView Integer} -> ExprView String
  At _ _ -> error "I don't know what this is supposed to do. Is it string indexing, returning String instead of Char?"
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
sbvModelToValuation = fromConstantsMap . foldr f Map.empty . modelAssocs
  where
    f (varname, cv) = (\(typ, c) -> Map.insert (Variable varname typ) c) $ case cvVal cv of
      -- booleans for some reason are represented as CInteger with a different 'Kind'
      _ | isBoolean cv -> (BoolType, Cbool (cvToBool cv))
      CInteger i -> (IntType, Cint i)
      CString s -> (StringType, Cstring s)
      _ -> error "todo: the other SBV types, including lists, sets, arbitrary ADTs, floating point values, etc"

#endif

