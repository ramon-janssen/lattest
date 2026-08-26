{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Lattest.SMT (
  SMT,
  SolvableProblem(..),

  addAssertions,
  addDeclarations,
  getSolution,
  getSolvable,
  pop,
  push,
  runSMT,
  Some(..),
  RCSet(..)
) where

import Data.SBV( constrain, SBV, SymVal (..), freshVar, RCSet(..), Kind (..))
import Data.SBV.Control( CheckSatResult, checkSat, query, Query)
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import qualified Data.SBV.List as SBV
import qualified Data.SBV.Internals as SBVI -- 'unsafe' internals

import Lattest.Model.Symbolic.Expr(ExprView(..), Variable (..), Valuation(..), Expr, Type (..), Constant (..), view)
import Lattest.Model.Symbolic.Internal.FreeMonoidX
import Lattest.Model.Symbolic.Internal.Sum(SumTerm(..))

import Control.Monad((<=<))
import Control.Monad.State (StateT (StateT), evalStateT, lift, modify, gets, MonadState (..), runState, State, evalState)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Model.Symbolic.Internal.Product (ProductTerm(..))
import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Lattest.Model.Symbolic.Internal.ExprImpls (Val(..))
import Data.Constraint.Extras (Has(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (ExprType (..), ExprConstraints, withExprConstraints, Constant (..))
import qualified Data.SBV.Tuple as SBV
import qualified Data.SBV.Either as SBV
import qualified Data.SBV.Set as SBV
import Unsafe.Coerce (unsafeCoerce)

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

type SMT = StateT (Map String (Some SBV)) Query
type SMT' = State (Map String (Some SBV))

smt'tosmt :: SMT' a -> SMT a
smt'tosmt smt = StateT $ (\f x -> pure $ f x) $ runState smt

runSMT :: SMT a -> IO a
runSMT = SBV.runSMT . query . flip evalStateT Map.empty

getSolution :: [Some Variable] -> SMT Valuation
getSolution vs =
  Valuation . foldr DMap.union mempty
  <$> mapM getVarValue vs
  where
    getVarValue :: Some Variable -> SMT (DMap.DMap Variable Val)
    getVarValue (Some v@(Variable nm tp)) = do
        sval <- gets (\m -> case m Map.!? nm of
            Nothing -> error $ show nm <> "is not in the map"
            Just (Some (SBVI.SBV x)) -> x)
        (Constant _ c) <- lift $ svalToConstant tp sval
        return $ DMap.singleton v (withExprConstraints tp $ Val c)

svalToConstant :: Type a -> SBVI.SVal -> Query (Constant a)
svalToConstant t s = withExprConstraints t $ Constant t <$> SBV.getValue (SBVI.SBV s)

addAssertions :: [Expr Bool] -> SMT ()
addAssertions = mapM_ (lift . constrain <=< smt'tosmt . exprToSymbolic . view)

-- This is the reason we have the StateT wrapper in SMT:
-- SBV wants us to keep track of the symbolic variables
-- we get on each declaration, and use them to reference
-- the variable.
addDeclarations :: [Some Variable] -> SMT ()
addDeclarations = mapM_ (\(Some v) -> addDeclaration v)

addDeclaration :: forall t. Variable t -> SMT ()
addDeclaration (Variable nm ty) = do
    v <- has @SymVal ty $ freshVar @t nm
    modify $ Map.insert nm $ Some v

getSolvable :: SMT SolvableProblem
getSolvable = checkSatToSolveProblem <$> lift checkSat

pop, push :: SMT ()
pop  = lift $ SBV.pop  1
push = lift $ SBV.push 1

---------------
-- Non-exported functions
---------------

-- The main translation between our Exprs and SBV's Symbolic
exprToSymbolic :: ExprConstraints a => ExprView a -> SMT' (SBV a)
exprToSymbolic v = case v of
  Var (Variable nm _tp) -> gets ((\(Some (SBVI.SBV x)) -> SBVI.SBV x) . (Map.! nm))
  Const c -> pure $ literal c
  Ite i t e -> SBV.ite <$> go i <*> go t <*> go e
  Equal _ l r -> (SBV..==) <$> go l <*> go r
  Divide      x y -> SBV.sDiv  <$> go x <*> go y
  DivideFloat x y -> (/)       <$> go x <*> go y
  Modulo x y -> SBV.sMod  <$> go x <*> go y
  Sum      s -> foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal i               + sY) <$> go x <*> symY) (pure $ literal 0) s
  SumFloat s -> foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal (fromInteger i) + sY) <$> go x <*> symY) (pure $ literal 0) s
  Product      p -> foldOccur (\(ProductTerm x) i symY -> (\x' y -> x' ^ i * y) <$> go x <*> symY) (pure $ literal 1) p
  ProductFloat p -> foldOccur (\(ProductTerm x) i symY -> (\x' y -> x' ^ i * y) <$> go x <*> symY) (pure $ literal 1) p
  Length t x -> withExprConstraints t $ SBV.length <$> go x
  GezInt   i -> (SBV..>= literal 0) <$> go i
  GezFloat f -> (SBV..>= literal 0) <$> go f
  Not b -> SBV.sNot <$> go b
  And xs -> foldr (\b bs -> (SBV..&&) <$> go b <*> bs) (pure $ literal True) (Set.toList xs)
   -- The below version errors because SBV doesn't properly declare some variable
   -- My best guess is that it's a bug if you use 'and' inside a Query, but I haven't
   -- looked deep enough nor done enough testing to report as a bug.
   -- SBV.and <$> foldr (\b bs -> (SBV..:) <$> go b <*> bs) (pure SBV.nil) (Set.toList xs)
  Concat xs -> SBV.concat <$> go xs
  Cons x xs -> case typeOf' xs of
    ListType t -> withExprConstraints t $ (SBV..:) <$> go x <*> go xs
  Append xs ys -> case typeOf' xs of
    ListType t -> withExprConstraints t $ (SBV.++) <$> go xs <*> go ys
  LElem t x xs -> withExprConstraints t $ SBV.elem <$> go x <*> go xs
  Take i xs -> case typeOf' xs of
    ListType t -> withExprConstraints t $ SBV.take <$> go i <*> go xs
  Drop i xs -> case typeOf' xs of
    ListType t -> withExprConstraints t $ SBV.drop <$> go i <*> go xs
  First t x -> withExprConstraints t $ SBV.fst <$> go x
  Second t x -> withExprConstraints t $ SBV.snd <$> go x
  Pair x y -> case typeOf' (Pair x y) of
    TupleType t1 t2 -> withExprConstraints t1 $ withExprConstraints t2 $
      curry SBV.tuple <$> go x <*> go y
  Head xs -> withExprConstraints (typeOf' xs) $ SBV.head <$> go xs
  Tail xs -> withExprConstraints (typeOf' xs) $ SBV.tail <$> go xs
  ELeft xs -> withExprConstraints (typeOf' xs) $ SBV.sLeft <$> go xs
  ERight xs -> withExprConstraints (typeOf' xs) $ SBV.sRight <$> go xs
  SElem t x xs -> withExprConstraints t $ withExprConstraints (SetType t) $ SBV.member <$> go x <*> go xs
  SInsert x xs -> SBV.insert <$> go x <*> go xs
  Map (Variable nm ta) f x -> withExprConstraints ta $ has @ExprType f $ withExprConstraints (typeOf' f) $ do
    -- do-notation makes it easier to massage the functions into the type that 'SBV.map' wants
    xs <- go x
    m <- get
    -- locally modify the environment to map 'v' to the smtvar we get
    let f' smtvar = flip evalState m $ do
          modify $ Map.insert nm $ Some smtvar
          go f
    pure $ SBV.map f' xs
  Either (Variable nml tl) (Variable nmr tr) l r e -> withExprConstraints tl $ withExprConstraints tr $ has @ExprType e $ withExprConstraints (typeOf' e) $ do
    -- see the case for 'Map' above; this one is very similar
    ei <- go e
    m <- get
    let fl smtvar = flip evalState m $ do
          modify $ Map.insert nml $ Some smtvar
          go l
    let fr smtvar = flip evalState m $ do
          modify $ Map.insert nmr $ Some smtvar
          go r
    pure $ SBV.either fl fr ei
  where
    go :: ExprConstraints a => ExprView a -> SMT' (SBV a)
    go = exprToSymbolic


checkSatToSolveProblem :: CheckSatResult -> SolvableProblem
checkSatToSolveProblem = \case
  SBV.Sat -> Sat
  SBV.Unsat -> Unsat
  SBV.Unk -> Unknown
  SBV.DSat _ -> Unknown

sbvModelToValuation :: SBVI.SMTModel -> Valuation
sbvModelToValuation = Valuation . foldr f DMap.empty . SBVI.modelAssocs
  where
    f (varname, cv) = go cv $
        \tp x -> DMap.insert (Variable varname tp) $ withExprConstraints tp $ Val x

    go :: SBVI.CV -> (forall t. Type t -> t -> r) -> r
    go cv k = case cv of
      SBVI.CV KBool _ -> k BoolType (SBVI.cvToBool cv)
      SBVI.CV KUnbounded (SBVI.CInteger i) -> k IntType i
      SBVI.CV KDouble (SBVI.CDouble d) -> k FloatType d
      SBVI.CV KChar (SBVI.CChar c) -> k CharType c
      SBVI.CV KString (SBVI.CString s) -> k (ListType CharType) s
      SBVI.CV (KList t) (SBVI.CList xs) -> kindToType t $ \tp -> k (ListType tp) $
        foldr (\x ys -> go (SBVI.CV t x) $ \_ y -> unsafeCoerce y:ys) [] xs
      SBVI.CV (KSet t) (SBVI.CSet s) -> case s of
        RegularSet    xs -> go (SBVI.CV (KList t) (SBVI.CList $ Set.toList xs)) $ \cases
          (ListType tp) ys -> withExprConstraints tp $ k (SetType tp) (RegularSet    $ Set.fromList ys)
          _ _ -> error "impossible"
        ComplementSet xs -> go (SBVI.CV (KList t) (SBVI.CList $ Set.toList xs)) $ \cases
          (ListType tp) ys -> withExprConstraints tp $ k (SetType tp) (ComplementSet $ Set.fromList ys)
          _ _ -> error "impossible"
      SBVI.CV (KTuple [k1, k2]) (SBVI.CTuple [x,y]) -> go (SBVI.CV k1 x) $ \t1 x' -> go (SBVI.CV k2 y) $ \t2 y' -> k (TupleType t1 t2) (x', y')
      SBVI.CV (KADT "Either" _ [("Left", _), ("Right", [rk])]) (SBVI.CADT ("Left", [(k', x)])) -> kindToType rk $ \rty ->
        go (SBVI.CV k' x) $ \tp y -> k (SumType tp rty) (Left y)
      SBVI.CV (KADT "Either" _ [("Left", [lk]), ("Right", _)]) (SBVI.CADT ("Right", [(k', x)])) -> kindToType lk $ \lty ->
        go (SBVI.CV k' x) $ \tp y -> k (SumType lty tp) (Right y)
      SBVI.CV k' _ -> error $ "Couldn't convert " <> show cv <> ", with kind " <> show k'

    -- needed to correctly type empty lists and sets
    kindToType :: Kind -> (forall t. Type t -> r) -> r
    kindToType kind k = case kind of
      KBool -> k BoolType
      KUnbounded -> k IntType
      KDouble -> k FloatType
      KChar -> k CharType
      KString -> k $ ListType CharType
      KList t -> kindToType t $ k . ListType
      KSet t -> kindToType t $ k . SetType
      KTuple [k1, k2] -> kindToType k1 $ \t1 -> kindToType k2 $ \t2 -> k $ TupleType t1 t2
      _ -> error $ "couldn't convert kind " <> show kind
