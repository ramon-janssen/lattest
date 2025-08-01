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
data  ValExprView   = Vconst  Constant
                    | Vvar    Variable
                    -- Boolean
                    | Vequal    ValExpr ValExpr
                    | Vite      {   condition   :: ValExpr
                                ,   trueBranch  :: ValExpr
                                ,   falseBranch :: ValExpr
                                }
                    | Vnot      ValExpr
                    | Vand      (Set ValExpr)
                    -- Int
                    | Vdivide   {   dividend :: ValExpr
                                ,   divisor  :: ValExpr
                                }
                    | Vmodulo   {   dividend :: ValExpr
                                ,   divisor  :: ValExpr
                                }
                    | Vsum      (FreeSum ValExpr)
                    | Vproduct  (FreeProduct ValExpr)
                    | Vgez      ValExpr
                    -- String
                    | Vlength   ValExpr
                    | Vat       {   string   :: ValExpr
                                ,   position :: ValExpr
                                }
                    | Vconcat   [ValExpr]
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

instance Show ValExprView where
    show (Vconst c) = show c
    show (Vvar v) = show v
    show (Vequal e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (Vite cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (Vnot e) = "¬(" ++ show e ++ ")"
    show (Vand es) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> Set.toList es
    show (Vdivide e1 e2) = "(" ++ show e2 ++ ") / (" ++ show e2 ++ ")"
    show (Vmodulo e1 e2) = "(" ++ show e2 ++ ") % (" ++ show e2 ++ ")"
    show (Vsum es) = show es -- List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> Set.toList es -- FreeSum ValExpr
    show (Vproduct es) = show es -- "(" ++ show e2 ++ ")" --FreeProduct ValExpr
    show (Vgez e) = "(" ++ show e ++ ") > 0"
    show (Vlength e) = "length(" ++ show e ++ ")"
    show (Vat e1 e2) = "" ++ show e2 ++ "[" ++ show e2 ++ "]"
    show (Vconcat es) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$> es


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
newtype ValExpr = ValExpr {
                        -- | View on value expression.
                        view :: ValExprView }
  deriving (Eq, Ord)

instance Show ValExpr where
    show = show . view

-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: ValExpr -> Either String Constant
eval = evalView . view

evalView :: ValExprView -> Either String Constant
evalView (reduceExpr -> Vconst v) = Right v
evalView x          = Left $ "Value Expression is not a constant value " ++ show x

reduceExpr :: ValExprView -> ValExprView
--reduceExpr (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
--reduceExpr (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
--reduceExpr (view -> Viscstr { })                                   =
--reduceExpr (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
reduceExpr (Vconst con) = Vconst con
reduceExpr (Vvar v) = Vvar v
reduceExpr (Vite (reduceView -> Vconst c) (reduceView -> e1) (reduceView -> e2)) = if toBool c then e1 else e2
reduceExpr (Vite (reduce -> c) (reduce -> e1) (reduce -> e2)) = Vite c e1 e2
reduceExpr (Vequal (reduceView -> Vconst e1) (reduceView -> Vconst e2)) = Vconst $ Cbool (e1 == e2)
reduceExpr (Vequal (reduce -> e1) (reduce -> e2)) = Vequal e1 e2
reduceExpr (Vnot (reduceView -> (Vconst (Cbool b)))) = vbool b
reduceExpr (Vnot (reduce -> e)) = Vnot e
reduceExpr (Vand (Set.map reduceView -> es)) | all isConst es = vbool $ foldr (&&) True (Set.map getBool es)
reduceExpr (Vand (Set.map reduce -> es)) = Vand es
reduceExpr (Vsum (mapFreeMonoidX reduceView -> es)) | allFreeMonoidX isConst es = vint $ foldrTerms (+) 0 (mapFreeMonoidX getInt es)
reduceExpr (Vsum (mapFreeMonoidX reduce -> es)) = Vsum es
reduceExpr (Vproduct (mapFreeMonoidX reduceView -> es)) | allFreeMonoidX isConst es = vint $ foldrTerms (*) 1 (mapFreeMonoidX getInt es)
reduceExpr (Vproduct (mapFreeMonoidX reduce -> es)) = Vproduct es
reduceExpr (Vmodulo (reduceView -> (Vconst (Cint x))) (reduceView -> (Vconst (Cint y)))) = vint $ x `mod` y
reduceExpr (Vmodulo (reduce -> e1) (reduce -> e2)) = Vmodulo e1 e2
reduceExpr (Vdivide (reduceView -> (Vconst (Cint x))) (reduceView -> (Vconst (Cint y)))) = vint $ x `divInteger` y
reduceExpr (Vdivide (reduce -> e1) (reduce -> e2)) = Vdivide e1 e2
reduceExpr (Vgez (reduceView -> (Vconst (Cint x)))) = vbool $ x >= 0
reduceExpr (Vgez (reduce -> e)) = Vgez e
reduceExpr (Vlength (reduceView -> (Vconst (Cstring s)))) = vint $ textLength s
reduceExpr (Vlength (reduce -> e)) = Vlength e
reduceExpr (Vat (reduceView -> (Vconst (Cstring s))) (reduceView -> (Vconst (Cint i)))) = vtext $ charAt s i -- TODO are these semantics the same as in SMT2?
reduceExpr (Vat (reduce -> e1) (reduce -> e2)) = Vat e1 e2
reduceExpr (Vconcat (fmap reduceView -> es)) | all isConst es = vtext $ Text.concat $ fmap getText es
reduceExpr (Vconcat (fmap reduce -> e)) = Vconcat e
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
