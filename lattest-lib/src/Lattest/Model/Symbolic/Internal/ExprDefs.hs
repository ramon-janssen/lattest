{-
This is a modified version of:
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

module Lattest.Model.Symbolic.Internal.ExprDefs
( ExprView(..)
, Expr(..)       -- for local usage only!
, eval
, reduce
, Variable(..)
, Type(..)
, allTypes
, Constant(..)
, constType
, ConstType
, fromConst
, toConst
, ExprType
, typeOf
, typeOf'
, varName
, varType
, isConst
, freeVars
)
where

import qualified Data.List as List
import           Data.Set         (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Text        (Text)
import qualified Data.Text as Text(length, pack, index, concat)
import           GHC.Generics     (Generic)
import           GHC.Integer (divInteger)

import           Lattest.Model.Symbolic.Internal.FreeMonoidX
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX as FMX
import           Lattest.Model.Symbolic.Internal.Product
import           Lattest.Model.Symbolic.Internal.Sum


data Type = IntType | BoolType | StringType deriving (Eq, Ord)

allTypes :: [Type]
allTypes = [IntType, BoolType, StringType]

class ExprType t where
    typeOf :: t -> Type
    typeOf' :: f t -> Type

instance ExprType Integer where
    typeOf _ = IntType
    typeOf' _ = IntType
instance ExprType Bool where
    typeOf _ = BoolType
    typeOf' _ = BoolType
instance ExprType String where
    typeOf _ = StringType
    typeOf' _ = StringType

instance Show Type where
    show IntType = "Int"
    show BoolType = "Bool"
    show StringType = "String"

data Variable = Variable {varName :: String, varType :: Type} deriving (Eq, Ord)

instance Show Variable where
    show (Variable name stype) = name ++ ":" ++ show stype

data Constant = -- | Constructor of Boolean constant.
                Cbool    { toBool :: Bool }
                -- | Constructor of Integer constant.
              | Cint     { toInteger :: Integer }
                -- | Constructor of String constant.
              | Cstring  { toString :: String }
                -- | Constructor of constructor constant (value of ADT).
              | Ccstr    { cstrName :: String, args :: [Constant] }
{-
                -- | Constructor of Regular Expression constant.
              | Cregex   { -- | Regular Expression in XSD format
                           toXSDRegex :: Text } 
                                            -- PvdL: performance gain: translate only once,
                                            --       storing SMT string as well
                -- | Constructor of ANY constant.
              | Cany     { sort :: SortId }
-}
  deriving (Eq, Ord, Read)

constType :: Constant -> Type
constType (Cbool _) = BoolType
constType (Cint _) = IntType
constType (Cstring _) = StringType

instance Show Constant where
  show (Cbool b) = show b
  show (Cint i) = show i
  show (Cstring t) = show t

-- | convert a Constant to an typed value
class ConstType t where
    fromConst :: Constant -> Either String t
    toConst :: t -> Constant

instance ConstType Bool where
    fromConst (Cbool b) = Right b
    fromConst v = Left $ typeError "Bool" v
    toConst = Cbool

instance ConstType Integer where
    fromConst (Cint i) = Right i
    fromConst v = Left $ typeError "Int" v
    toConst = Cint

instance ConstType String where
    fromConst (Cstring s) = Right s
    fromConst v = Left $ typeError "String" v
    toConst = Cstring

typeError :: String -> Constant -> String
typeError received expected = "Type mismatch - " ++ show expected ++ " expected, got " ++ received ++ "\n"


-- ----------------------------------------------------------------------------------------- --
-- value expression

data ExprView t where
    Var :: {variable :: Variable} -> ExprView t
    Const :: ExprType t => {constant :: t} -> ExprView t
    Ite :: {conditional :: ExprView Bool, trueBranch :: ExprView t, falseBranch :: ExprView t} -> ExprView t
    {-
    No polymorphic Equal possible, because that would make sensible Eq and Ord instances impossible: Equal 1 2 and Equal
    "a" "b" are both ExprView Bool's, but an == on those expressions would have to compare 1 == "a" and 2 == "b".
    Var, Const and Ite don't have this problem because the argument types are forced to be equal through the return type.
    -}
    EqualInt :: {leftInt :: ExprView Integer, rightInt :: ExprView Integer} -> ExprView Bool
    EqualString :: {leftString :: ExprView String, rightString :: ExprView String} -> ExprView Bool
    EqualBool :: {leftBool :: ExprView Bool, rightBool :: ExprView Bool} -> ExprView Bool
    Divide :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    Modulo :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    Sum :: FreeSum (ExprView Integer) -> ExprView Integer
    Product :: FreeProduct (ExprView Integer) -> ExprView Integer
    Length :: ExprView String -> ExprView Integer
    GezInt :: ExprView Integer -> ExprView Bool
    Not :: ExprView Bool -> ExprView Bool
    And :: Set (ExprView Bool) -> ExprView Bool
    At :: {string2 :: ExprView String, position2 :: ExprView Integer} -> ExprView String
    Concat :: [ExprView String] -> ExprView String

deriving instance Eq t => Eq (ExprView t)
deriving instance Ord t => Ord (ExprView t)

instance Show t => Show (ExprView t) where
    show (Var v) = varName v
    show (Const c) = show c
    show (Ite cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (Divide e1 e2) = "(" ++ show e2 ++ ") / (" ++ show e2 ++ ")"
    show (Modulo e1 e2) = "(" ++ show e2 ++ ") % (" ++ show e2 ++ ")"
    show (Sum es) | es == mempty = "∑∅"
    show (Sum es) = "(" ++ showFreeMonoid "+" showSumTerm es ++ ")"
        where
        showSumTerm (-1)     t = "-" ++ t
        showSumTerm 1 t = t
        showSumTerm n t = show n ++ "⋅" ++ t
    show (Product es) | es == mempty = "∏∅"
    show (Product es) = showFreeMonoid "⋅" (\n t -> show n ++ "^" ++ t) es -- "(" ++ show e2 ++ ")" --FreeProduct Expr
    show (Length e) = "length(" ++ show e ++ ")"
    show (EqualInt e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (EqualBool e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (EqualString e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (GezInt e) = "(" ++ show e ++ ") ≥ 0"
    show (Not e) = "¬(" ++ show e ++ ")"
    show (And (Set.toList -> [])) = "⋀∅"
    show (And (Set.toList -> es)) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$>  es
    show (At e1 e2) = "" ++ show e1 ++ "[" ++ show e2 ++ "]"
    show (Concat []) = "∑'∅"
    show (Concat es) = List.intercalate "++" $ (\e -> "(" ++ show e ++ ")") <$> es

showFreeMonoid :: Show a => String -> (Integer -> String -> String) -> FreeMonoidX a -> String
showFreeMonoid plusRepr multRepr m@(FMX p) = List.intercalate plusRepr $ showTerm <$> Map.assocs p
    where
    showTerm (x, i) = multRepr i (show x)


-- | Expr: value expression
-- 1. User can't directly construct Expr (such that invariants will always hold)
-- 2. User can still pattern match on Expr using 'ExprView'
-- 3. Overhead at run-time is zero. See https://wiki.haskell.org/Performance/Data_types#Newtypes
newtype Expr t = Expr {view :: ExprView t} deriving (Eq, Ord)

instance Show t => Show (Expr t) where
    show = show . view

-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: Expr v -> Either String v
eval = evalView . view

evalView :: ExprView v -> Either String v
evalView (reduce -> Const v) = Right v
evalView x = Left $ "Value Expression is not a constant value"

isConst :: ExprView v -> Bool
isConst (Const _) = True
isConst _ = False

reduce :: ExprView v -> ExprView v
--reduce (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduce (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduce (view -> Viscstr { })                                   =
--reduce (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduce (Var v) = Var v
reduce (Const v) = Const v
reduce (Product v) = Product v
reduce (Ite (reduce -> Const b) (reduce -> e1) (reduce -> e2)) = if b then e1 else e2
reduce (Ite (reduce -> c) (reduce -> e1) (reduce -> e2)) = Ite c e1 e2
reduce (Sum (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Sum (mapFreeMonoidX reduce -> es)) = Sum es
reduce (Product (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Product (mapFreeMonoidX reduce -> es)) = Product es
reduce (Modulo (reduce -> e1) (reduce -> e2@(Const 0))) = Modulo e1 e2 -- leave divisions by zero as expressions
reduce (Modulo (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `mod` y
reduce (Modulo (reduce -> e1) (reduce -> e2)) = Modulo e1 e2
reduce (Divide (reduce -> e1) (reduce -> e2@(Const 0))) = Divide e1 e2 -- leave divisions by zero as expressions
reduce (Divide (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `divInteger` y
reduce (Divide (reduce -> e1) (reduce -> e2)) = Divide e1 e2
reduce (Length (reduce -> (Const s))) = Const $ fromIntegral $ length s
reduce (Length (reduce -> e)) = Length e
--reduce (view -> Vstrinre { })                                  =
--reduce (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

--reduce (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduce (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduce (view -> Viscstr { })                                   =
--reduce (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduce (EqualInt (reduce -> Const e1) (reduce -> Const e2)) = Const (e1 == e2)
reduce (EqualInt (reduce -> e1) (reduce -> e2)) = EqualInt e1 e2
reduce (EqualBool (reduce -> Const e1) (reduce -> Const e2)) = Const (e1 == e2)
reduce (EqualBool (reduce -> e1) (reduce -> e2)) = EqualBool e1 e2
reduce (EqualString (reduce -> Const e1) (reduce -> Const e2)) = Const (e1 == e2)
reduce (EqualString (reduce -> e1) (reduce -> e2)) = EqualString e1 e2
reduce (GezInt (reduce -> (Const x))) = Const $ x >= 0
reduce (GezInt (reduce -> e)) = GezInt e
reduce (Not (reduce -> (Const b))) = Const $ not b
reduce (Not (reduce -> e)) = Not e
reduce (And (Set.map reduce -> es)) | all isConst es = Const $ foldr (&&) True (Set.map constant es) -- TODO could be optimized further: if not all elements are constant, but if there are multiple constant elements, then the latter could still be combined
reduce (And (Set.map reduce -> es)) = And es
--reduce (view -> Vstrinre { })                                  =
--reduce (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

--reduce (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduce (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduce (view -> Viscstr { })                                   =
--reduce (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduce (At (reduce -> (Const s)) (reduce -> (Const i))) = Const $ drop (fromIntegral i) s -- TODO are these semantics the same as in SMT2?
reduce (At (reduce -> e1) (reduce -> e2)) = At e1 e2
reduce (Concat (fmap reduce -> es)) | all isConst es = Const $ concat $ fmap constant es -- TODO could be optimized further: if not all elements are constant, but if there are multiple successive constant elements, then the latter could still be combined
reduce (Concat (fmap reduce -> e)) = Concat e
--reduce (view -> Vstrinre { })                                  =
--reduce (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --

freeVars :: Expr t -> Set.Set Variable
freeVars = Set.fromList . freeVars' . view

freeVars' :: ExprView t -> [Variable]
freeVars' (Var v) = [v]
freeVars' (Const _) = []
freeVars' (Ite cond e1 e2) = freeVars' cond ++ freeVars' e1 ++ freeVars' e2
freeVars' (Divide e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Modulo e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Sum (distinctTermsT -> es)) = concat $ freeVars' <$> es
freeVars' (Product (distinctTermsT -> es)) = concat $ freeVars' <$> es
freeVars' (Length e) = freeVars' e
freeVars' (EqualInt e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (EqualBool e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (EqualString e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (GezInt e) = freeVars' e
freeVars' (Not e) = freeVars' e
freeVars' (And (Set.toList -> es)) = concat $ freeVars' <$> es
freeVars' (At e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Concat es) = concat $ freeVars' <$> es






