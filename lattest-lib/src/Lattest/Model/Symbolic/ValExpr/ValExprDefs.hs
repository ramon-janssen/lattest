{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ValExprDefs
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Data definitions file for Value Expressions.
-----------------------------------------------------------------------------
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Lattest.Model.Symbolic.ValExpr.ValExprDefs
( ExprView(..)
, Expr(..)       -- for local usage only!
, eval
, reduce
, Variable(..)
, Type(..)
, varName
, varType
, isConst
)
where

import           Control.DeepSeq
import           Data.Data
import qualified Data.List as List
import           Data.Set         (Set)
import qualified Data.Set as Set
import           Data.Text        (Text)
import qualified Data.Text as Text(length, pack, index, concat)
import           GHC.Generics     (Generic)
import           GHC.Integer (divInteger)

import           Lattest.Model.Symbolic.ValExpr.Constant (Constant(..), toBool, toText)
import qualified Lattest.Model.Symbolic.ValExpr.Constant as Const (toInteger)
import           Lattest.Model.Symbolic.ValExpr.FreeMonoidX
import           Lattest.Model.Symbolic.ValExpr.Product
import           Lattest.Model.Symbolic.ValExpr.Sum


data Type = IntType | BoolType | StringType deriving (Eq, Ord, Show, Read)

-- TODO ideally the Variable has a parameter t that denotes the type, so that the typechecker can match it to ValExprs with the same type t
data Variable = Variable {varName :: String, varType :: Type} deriving (Eq, Ord)

instance Show Variable where
    show (Variable name stype) = name ++ ":" ++ show stype

-- ----------------------------------------------------------------------------------------- --
-- value expression

data ExprView v where
    IntConst :: Integer -> ExprView Integer
    IntVar :: Variable -> ExprView Integer
    IntIte :: {conditionInt2 :: ExprView Bool, trueBranchInt2 :: ExprView Integer, falseBranchInt2 :: ExprView Integer} -> ExprView Integer
    IntDivide :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    IntModulo :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    IntSum :: FreeSum (ExprView Integer) -> ExprView Integer
    IntProduct :: FreeProduct (ExprView Integer) -> ExprView Integer
    Length :: ExprView String -> ExprView Integer
    BoolConst :: Bool -> ExprView Bool
    BoolVar :: Variable -> ExprView Bool
    EqualInt :: ExprView Integer -> ExprView Integer -> ExprView Bool
    EqualBool :: ExprView Bool -> ExprView Bool -> ExprView Bool
    EqualString :: ExprView String -> ExprView String -> ExprView Bool
    BoolIte :: {conditionBool2 :: ExprView Bool, trueBranchBool2 :: ExprView Bool, falseBranchBool2 :: ExprView Bool} -> ExprView Bool
    GezInt :: ExprView Integer -> ExprView Bool
    Not :: ExprView Bool -> ExprView Bool
    And :: Set (ExprView Bool) -> ExprView Bool
    StringConst :: String -> ExprView String
    StringVar :: Variable -> ExprView String
    StringIte :: {conditionString2 :: ExprView Bool, trueBranchString2 :: ExprView String, falseBranchString2 :: ExprView String} -> ExprView String
    At :: {string2 :: ExprView String, position2 :: ExprView Integer} -> ExprView String
    Concat :: [ExprView String] -> ExprView String

deriving instance Eq v => Eq (ExprView v)
deriving instance Ord v => Ord (ExprView v)

instance Show (ExprView v) where
    show (IntConst c) = show c
    show (IntVar v) = show v
    show (IntIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (IntDivide e1 e2) = "(" ++ show e2 ++ ") / (" ++ show e2 ++ ")"
    show (IntModulo e1 e2) = "(" ++ show e2 ++ ") % (" ++ show e2 ++ ")"
    show (IntSum es) = show es -- List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> Set.toList es -- FreeSum ValExpr
    show (IntProduct es) = show es -- "(" ++ show e2 ++ ")" --FreeProduct ValExpr
    show (Length e) = "length(" ++ show e ++ ")"
    show (BoolConst c) = show c
    show (BoolVar v) = show v
    show (EqualInt e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (EqualBool e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (EqualString e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (BoolIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (GezInt e) = "(" ++ show e ++ ") > 0"
    show (Not e) = "¬(" ++ show e ++ ")"
    show (And es) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> Set.toList es
    show (StringConst c) = show c
    show (StringVar v) = show v
    show (StringIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (At e1 e2) = "" ++ show e2 ++ "[" ++ show e2 ++ "]"
    show (Concat es) = List.intercalate "++" $ (\e -> "(" ++ show e ++ ")") <$> es

-- | Expr: value expression
-- 1. User can't directly construct Expr (such that invariants will always hold)
-- 2. User can still pattern match on Expr using 'ExprView'
-- 3. Overhead at run-time is zero. See https://wiki.haskell.org/Performance/Data_types#Newtypes
newtype Expr v = Expr {view :: ExprView v} deriving (Eq, Ord)

instance Show (Expr v) where
    show = show . view

-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: Expr v -> Either String v
eval = evalView . view

evalView :: ExprView v -> Either String v
evalView (reduce -> IntConst v) = Right v
evalView (reduce -> BoolConst v) = Right v
evalView (reduce -> StringConst v) = Right v
evalView x = Left $ "Value Expression is not a constant value " ++ show x

isConst :: ExprView v -> Bool
isConst (IntConst _) = True
isConst (BoolConst _) = True
isConst (StringConst _) = True
isConst _ = False

reduce :: ExprView v -> ExprView v
--reduce (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduce (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduce (view -> Viscstr { })                                   =
--reduce (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduce (IntConst v) = IntConst v
reduce (IntVar v) = IntVar v
reduce (IntIte (reduce -> BoolConst b) (reduce -> e1) (reduce -> e2)) = if b then e1 else e2
reduce (IntIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = IntIte c e1 e2
reduce (IntSum (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = IntConst $ foldrTerms (+) 0 (mapFreeMonoidX getIntConst es)
reduce (IntSum (mapFreeMonoidX reduce -> es)) = IntSum es
reduce (IntProduct (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = IntConst $ foldrTerms (*) 1 (mapFreeMonoidX getIntConst es)
reduce (IntProduct (mapFreeMonoidX reduce -> es)) = IntProduct es
reduce (IntModulo (reduce -> (IntConst x)) (reduce -> (IntConst y))) = IntConst $ x `mod` y
reduce (IntModulo (reduce -> e1) (reduce -> e2)) = IntModulo e1 e2
reduce (IntDivide (reduce -> (IntConst x)) (reduce -> (IntConst y))) = IntConst $ x `divInteger` y
reduce (IntDivide (reduce -> e1) (reduce -> e2)) = IntDivide e1 e2
reduce (Length (reduce -> (StringConst s))) = IntConst $ fromIntegral $ length s
reduce (Length (reduce -> e)) = Length e
--reduce (view -> Vstrinre { })                                  =
--reduce (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

--reduce (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduce (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduce (view -> Viscstr { })                                   =
--reduce (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduce (BoolConst con) = BoolConst con
reduce (BoolVar v) = BoolVar v
reduce (BoolIte (reduce -> BoolConst c) (reduce -> e1) (reduce -> e2)) = if c then e1 else e2
reduce (BoolIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = BoolIte c e1 e2
reduce (EqualInt (reduce -> IntConst e1) (reduce -> IntConst e2)) = BoolConst (e1 == e2)
reduce (EqualInt (reduce -> e1) (reduce -> e2)) = EqualInt e1 e2
reduce (EqualBool (reduce -> BoolConst e1) (reduce -> BoolConst e2)) = BoolConst (e1 == e2)
reduce (EqualBool (reduce -> e1) (reduce -> e2)) = EqualBool e1 e2
reduce (EqualString (reduce -> StringConst e1) (reduce -> StringConst e2)) = BoolConst (e1 == e2)
reduce (EqualString (reduce -> e1) (reduce -> e2)) = EqualString e1 e2
reduce (GezInt (reduce -> (IntConst x))) = BoolConst $ x >= 0
reduce (GezInt (reduce -> e)) = GezInt e
reduce (Not (reduce -> (BoolConst b))) = BoolConst $ not b
reduce (Not (reduce -> e)) = Not e
reduce (And (Set.map reduce -> es)) | all isConst es = BoolConst $ foldr (&&) True (Set.map getBoolConst es) -- TODO could be optimized further: if not all elements are constant, but if there are multiple constant elements, then the latter could still be combined
reduce (And (Set.map reduce -> es)) = And es
--reduce (view -> Vstrinre { })                                  =
--reduce (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

--reduce (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduce (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduce (view -> Viscstr { })                                   =
--reduce (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduce (StringConst con) = StringConst con
reduce (StringVar v) = StringVar v
reduce (StringIte (reduce -> BoolConst c) (reduce -> e1) (reduce -> e2)) = if c then e1 else e2
reduce (StringIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = StringIte c e1 e2
reduce (At (reduce -> (StringConst s)) (reduce -> (IntConst i))) = StringConst $ drop (fromIntegral i) s -- TODO are these semantics the same as in SMT2?
reduce (At (reduce -> e1) (reduce -> e2)) = At e1 e2
reduce (Concat (fmap reduce -> es)) | all isConst es = StringConst $ concat $ fmap getStringConst es -- TODO could be optimized further: if not all elements are constant, but if there are multiple successive constant elements, then the latter could still be combined
reduce (Concat (fmap reduce -> e)) = Concat e
--reduce (view -> Vstrinre { })                                  =
--reduce (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

--getConst :: ValExprView -> Constant
getIntConst :: ExprView Integer -> Integer
getIntConst (IntConst c) = c
getBoolConst :: ExprView Bool -> Bool
getBoolConst (BoolConst c) = c
getStringConst :: ExprView String -> String
getStringConst (StringConst c) = c

typeOfExpr :: ExprView t -> Type
typeOfExpr (IntConst _) = IntType
typeOfExpr (IntVar _) = IntType
typeOfExpr (IntIte _ _ _) = IntType
typeOfExpr (IntDivide _ _) = IntType
typeOfExpr (IntModulo _ _) = IntType
typeOfExpr (IntSum _) = IntType
typeOfExpr (IntProduct _) = IntType
typeOfExpr (Length _) = IntType
typeOfExpr (BoolConst _) = BoolType
typeOfExpr (BoolVar _) = BoolType
typeOfExpr (EqualInt _ _) = BoolType
typeOfExpr (EqualBool _ _) = BoolType
typeOfExpr (EqualString _ _) = BoolType
typeOfExpr (BoolIte _ _ _) = BoolType
typeOfExpr (GezInt _) = BoolType
typeOfExpr (Not _) = BoolType
typeOfExpr (And _) = BoolType
typeOfExpr (StringConst _) = StringType
typeOfExpr (StringVar _) = StringType
typeOfExpr (StringIte _ _ _) = StringType
typeOfExpr (At _ _) = StringType
typeOfExpr (Concat _) = StringType

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
