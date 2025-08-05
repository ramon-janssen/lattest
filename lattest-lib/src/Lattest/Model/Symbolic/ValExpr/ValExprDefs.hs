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
module Lattest.Model.Symbolic.ValExpr.ValExprDefs
( ValExprView(..)
, ValExpr(..)       -- for local usage only!
, eval
, PredefKind(..)
, Variable(..)
, Type(..)
, varName
, varType
, constType
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
import           Lattest.Model.Symbolic.ValExpr.CstrId
import           Lattest.Model.Symbolic.ValExpr.FreeMonoidX
import           Lattest.Model.Symbolic.ValExpr.FuncId
import           Lattest.Model.Symbolic.ValExpr.Id
import           Lattest.Model.Symbolic.ValExpr.Product
import           Lattest.Model.Symbolic.ValExpr.Sum
import           Lattest.Model.Symbolic.ValExpr.SortId
import           Lattest.Model.Symbolic.ValExpr.SortOf


data Type = IntType | BoolType | StringType deriving (Eq, Ord)

constType :: Constant -> Type
constType (Cbool _) = BoolType
constType (Cint _) = IntType
constType (Cstring _) = StringType

instance Show Type where
    show IntType = "Int"
    show BoolType = "Bool"
    show BoolType = "String"

data Variable = Variable {varName :: String, varType :: Type} deriving (Eq, Ord)

instance Show Variable where
    show (Variable name stype) = name ++ ":" ++ show stype


-- ----------------------------------------------------------------------------------------- --
-- value expression

-- | ValExprView: the public view of value expression 'ValExpr'
data ValExprIntView = VIntConst  Constant
                    | VIntVar    Variable
                    | VIntIte   {   condition   :: ValExprBool
                                ,   trueBranch  :: ValExprInt
                                ,   falseBranch :: ValExprInt
                                }
                    | VIntDivide   {   dividend :: ValExprInt
                                ,   divisor  :: ValExprInt
                                }
                    | VIntModulo   {   dividend :: ValExprInt
                                ,   divisor  :: ValExprInt
                                }
                    | VIntSum      (FreeSum ValExprInt)
                    | VIntProduct  (FreeProduct ValExprInt)
                    | VIntGez      ValExprInt
                    | VLength   ValExprInt

data ValExprBoolView = VBoolConst  Constant
                    | VBoolVar    Variable
                    | VEqualInt  ValExprInt ValExprInt
                    | VEqualBool  ValExprBool ValExprBool
                    | VBoolEqualString  ValExprString ValExprString
                    | VBoolIte   {   condition   :: ValExprBool
                                ,   trueBranch  :: ValExprBool
                                ,   falseBranch :: ValExprBool
                                }
                    | VNot      ValExprBool
                    | VAnd      (Set ValExprBool)

data ValExprStringView = VStringConst  Constant
                    | VStringVar    Variable
                    | VStringIte   {   condition   :: ValExprString
                                ,   trueBranch  :: ValExprString
                                ,   falseBranch :: ValExprString
                                }
                    | VAt       {   string   :: ValExprString
                                ,   position :: ValExprString
                                }
                    | VConcat   [ValExprString]
{-
                    -- Regex
                    | Vstrinre {    string :: ValExpr
                               ,    regex  :: ValExpr
                               }
                    -- ADT
                    | Vcstr   CstrId [ValExpr]
                    | Viscstr CstrId ValExpr
                    | Vaccess CstrId Text Int ValExpr

                    | Vfunc   FuncId [ValExpr]
                    | Vpredef PredefKind FuncId [ValExpr]
-}
     deriving (Eq, Ord)

instance Show ValExprIntView where
    show (VIntConst c) = show c
    show (VIntVar v) = show v
    show (VIntIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (VIntDivide e1 e2) = "(" ++ show e2 ++ ") / (" ++ show e2 ++ ")"
    show (VIntModulo e1 e2) = "(" ++ show e2 ++ ") % (" ++ show e2 ++ ")"
    show (VIntSum es) = show es -- List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> Set.toList es -- FreeSum ValExpr
    show (VIntProduct es) = show es -- "(" ++ show e2 ++ ")" --FreeProduct ValExpr
    show (VIntGez e) = "(" ++ show e ++ ") > 0"
    show (VIntLength e) = "length(" ++ show e ++ ")"

instance Show ValExprBoolView where
    show (VBoolConst c) = show c
    show (VBoolVar v) = show v
    show (VEqualInt e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (VEqualBool e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (VEqualString e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (VBoolIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (VNot e) = "¬(" ++ show e ++ ")"
    show (VAnd es) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> Set.toList es

instance Show ValExprStringView where
    show (VStringConst c) = show c
    show (VStringVar v) = show v
    show (VStringIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (VAt e1 e2) = "" ++ show e2 ++ "[" ++ show e2 ++ "]"
    show (VConcat es) = List.intercalate "++" $ (\e -> "(" ++ show e ++ ")") <$> es

-- These instances are needed to use the symbolic representation of sums and
-- products of val expressions. These instances have no implementation, which
-- means that if an attempt is made to compute the value of a sum or product of
-- `ValExpr` then a runtime error will occur. When GADT's are used it will be
-- possible to define instances for `ValExpr` of numeric types.

{-instance Num ValExpr
    where
        (+)         = error "Symbolic ValExpr Num: +"
        (*)         = error "Symbolic ValExpr Num: *"
        abs         = error "Symbolic ValExpr Num: abs"
        signum      = error "Symbolic ValExpr Num: signum"
        fromInteger = error "Symbolic ValExpr Num: fromInteger"
        (-)         = error "Symbolic ValExpr Num: -"
instance Enum ValExpr
    where
        toEnum   = error "Symbolic ValExpr Enum: toEnum"
        fromEnum = error "Symbolic ValExpr Enum: fromEnum"
instance Ord v => Real ValExpr
    where
        toRational = error "Symbolic ValExpr Real: toRational"
instance Ord v => Integral ValExpr
    where
        quotRem   = error "Symbolic ValExpr Integral: quotRem"
        toInteger = error "Symbolic ValExpr Integral: toInteger"
-}

-- | ValExpr: value expression
--
-- 1. User can't directly construct ValExpr (such that invariants will always hold)
--
-- 2. User can still pattern match on ValExpr using 'ValExprView'
--
-- 3. Overhead at run-time is zero. See https://wiki.haskell.org/Performance/Data_types#Newtypes
newtype ValExpr v = ValExpr {
                        -- | View on value expression.
                        view :: v }
  deriving (Eq, Ord)

instance Show v => Show (ValExpr v) where
    show = show . view

type ValExprInt = ValExpr ValExprViewInt
type ValExprBool = ValExpr ValExprViewBool
type ValExprString = ValExpr ValExprViewString

class Eval v where
    eval :: v -> Either String Constant
    evalView :: v -> Either String Constant

-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: Reduce v => ValExpr v -> Either String Constant
eval = evalView . view

evalView :: Reduce v => v -> Either String Constant
evalView (reduceExpr -> Vconst v) = Right v
evalView x          = Left $ "Value Expression is not a constant value " ++ show x

class Reduce v where
    reduceExpr :: v -> v

instance Reduce ValExprIntView where
    --reduceExpr (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
    --reduceExpr (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
    --reduceExpr (view -> Viscstr { })                                   =
    --reduceExpr (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
    reduceExpr (VIntConst con) = Vconst con
    reduceExpr (VIntVar v) = Vvar v
    reduceExpr (VIntIte (reduceView -> Vconst c) (reduceView -> e1) (reduceView -> e2)) = if toBool c then e1 else e2
    reduceExpr (VIntIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = Vite c e1 e2
    reduceExpr (VEqualInt (reduceView -> Vconst e1) (reduceView -> Vconst e2)) = Vconst $ Cbool (e1 == e2)
    reduceExpr (VEqualInt (reduce -> e1) (reduce -> e2)) = Vequal e1 e2
    reduceExpr (VNot (reduceView -> (Vconst (Cbool b)))) = vbool b
    reduceExpr (VNot (reduce -> e)) = Vnot e
    reduceExpr (VAnd (Set.map reduceView -> es)) | all isConst es = vbool $ foldr (&&) True (Set.map getBool es)
    reduceExpr (VAnd (Set.map reduce -> es)) = Vand es
    reduceExpr (VIntSum (mapFreeMonoidX reduceView -> es)) | allFreeMonoidX isConst es = vint $ foldrTerms (+) 0 (mapFreeMonoidX getInt es)
    reduceExpr (VIntSum (mapFreeMonoidX reduce -> es)) = Vsum es
    reduceExpr (VIntProduct (mapFreeMonoidX reduceView -> es)) | allFreeMonoidX isConst es = vint $ foldrTerms (*) 1 (mapFreeMonoidX getInt es)
    reduceExpr (VIntProduct (mapFreeMonoidX reduce -> es)) = Vproduct es
    reduceExpr (VIntModulo (reduceView -> (Vconst (Cint x))) (reduceView -> (Vconst (Cint y)))) = vint $ x `mod` y
    reduceExpr (VIntModulo (reduce -> e1) (reduce -> e2)) = Vmodulo e1 e2
    reduceExpr (VIntDivide (reduceView -> (Vconst (Cint x))) (reduceView -> (Vconst (Cint y)))) = vint $ x `divInteger` y
    reduceExpr (VIntDivide (reduce -> e1) (reduce -> e2)) = Vdivide e1 e2
    reduceExpr (VIntGez (reduceView -> (Vconst (Cint x)))) = vbool $ x >= 0
    reduceExpr (VIntGez (reduce -> e)) = Vgez e
    reduceExpr (VLength (reduceView -> (Vconst (Cstring s)))) = vint $ textLength s
    reduceExpr (VLength (reduce -> e)) = Vlength e
    reduceExpr (VAt (reduceView -> (Vconst (Cstring s))) (reduceView -> (Vconst (Cint i)))) = vtext $ charAt s i -- TODO are these semantics the same as in SMT2?
    reduceExpr (VAt (reduce -> e1) (reduce -> e2)) = Vat e1 e2
    reduceExpr (VConcat (fmap reduceView -> es)) | all isConst es = vtext $ Text.concat $ fmap getText es
    reduceExpr (VConcat (fmap reduce -> e)) = Vconcat e
    --reduceExpr (view -> Vstrinre { })                                  =
    --reduceExpr (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

isConst :: ValExprView -> Bool
isConst (Vconst _) = True
isConst _ = False
getConst :: ValExprView -> Constant
getConst (Vconst c) = c
getInt :: ValExprView -> Integer
getInt = Const.toInteger . getConst
getBool :: ValExprView -> Bool
getBool = toBool . getConst
getText :: ValExprView -> Text
getText = toText . getConst
-- variations of reduceExpr that work on ValExprs or produce ValExprs. Note that this is only to make the type checker happy.
reduceView :: ValExpr -> ValExprView
reduceView = reduceExpr . view
reduce :: ValExpr -> ValExpr
reduce = ValExpr . reduceView
vbool :: Bool -> ValExprView
vbool = Vconst . Cbool
vint :: Integer -> ValExprView
vint = Vconst . Cint
vtext :: Text -> ValExprView
vtext = Vconst . Cstring
textLength :: Text -> Integer
textLength = Prelude.toInteger . Text.length
charAt :: Text -> Integer -> Text
charAt t i = Text.pack $ if i > Prelude.toInteger (Text.length t) then [Text.index t (fromInteger i)] else "" 

typeOfExpr = sortOf'

sortOf' :: ValExpr -> Type
--sortOf' (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         = fs
--sortOf' (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         = cs
--sortOf' (view -> Viscstr { })                                   = BoolType
--sortOf' (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  = ca!!p
sortOf' (view -> Vconst con)                                    = constType con
sortOf' (view -> Vvar (Variable _  t))                          = t
sortOf' (view -> Vite _cond vexp1 _vexp2)                       = sortOf' vexp1
sortOf' (view -> Vequal { })                                    = BoolType
sortOf' (view -> Vnot { })                                      = BoolType
sortOf' (view -> Vand { })                                      = BoolType
sortOf' (view -> Vsum { })                                      = IntType
sortOf' (view -> Vproduct { })                                  = IntType
sortOf' (view -> Vmodulo { })                                   = IntType
sortOf' (view -> Vdivide { })                                   = IntType
sortOf' (view -> Vgez { })                                      = BoolType
sortOf' (view -> Vlength { })                                   = IntType
sortOf' (view -> Vat { })                                       = StringType
sortOf' (view -> Vconcat { })                                   = StringType
--sortOf' (view -> Vstrinre { })                                  = BoolType
--sortOf' (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   = fs

-- | only needed for CNECTDEF
data PredefKind     = AST     -- Algebraic To String
                    | ASF     -- Algebraic From String
                    | AXT     -- Algebraic To Xml
                    | AXF     -- Algebraic From Xml
                    | SSB     -- Standard Sort Bool
                    | SSI     -- Standard Sort Int
                    | SSS     -- Standard Sort String
     deriving (Eq, Ord, Read, Show, Generic, NFData, Data)

instance Resettable PredefKind

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
