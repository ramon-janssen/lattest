--{-# LANGUAGE MultiParamTypeClasses #-}
--{-# LANGUAGE FlexibleInstances #-}

{-|
    This module contains the definitions for working with symbolic values: variables, expressions, concrete values, guards and assignments.
-}

module Lattest.Model.Symbolic (
SymGuard,
SymAssign,
Value(..),
Variable(..),
addTypedVar,
Type(..),
SymExpr(..),
equalTyped,
Valuation
)
where

import Grisette.Core as Grisette
import Grisette.SymPrim as GSymPrim
import qualified Data.Map as Map (Map)

{- |
    Types of symbolic expressions.
    
    Note: the supported types will be extended in the future.
-}
data Type = IntType | BoolType deriving (Eq, Ord,Show)

{- |
    Check whether the types of a variable and an expression match.
-}
equalTyped :: Variable -> Value -> Bool
equalTyped (Variable _ BoolType) (BoolVal _) = True
equalTyped (Variable _ IntType) (IntVal _) = True
equalTyped _ _ = False

{- |
    In a symbolic model, substitute a variable by an expression.
-}
addTypedVar :: Variable -> Value -> Model -> Model
addTypedVar (Variable v BoolType) (BoolVal w) m = Grisette.insertValue (GSymPrim.typedAnySymbol v :: TypedAnySymbol Bool) w m
addTypedVar (Variable v IntType) (IntVal w) m = Grisette.insertValue (GSymPrim.typedAnySymbol v :: TypedAnySymbol Integer) w m

{- |
    A typed variable.
-}
data Variable = Variable Grisette.Symbol Type deriving (Eq, Ord, Show)

{- |
    A symbolic guard, i.e., an predicate.
-}
type SymGuard = GSymPrim.SymBool

{- |
    A typed expression.
-}
data SymExpr = BoolExpr SymBool | IntExpr SymInteger deriving (Show)

{- |
    Assignments of symbolic expressions to variables.
-}
type SymAssign  = Map.Map Variable SymExpr

{- |
    Typed, concrete values.
-}
data Value = IntVal Integer | BoolVal Bool deriving (Eq, Ord,Show)

{- |
    Assignments of concrete expressions to variables.
-}
type Valuation = (Map.Map Variable Value)
