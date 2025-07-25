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
import           Data.Set        (Set)
import           Data.Text       (Text)
import           GHC.Generics    (Generic)

import           Lattest.Model.Symbolic.ValExpr.Constant (Constant(..))
import           Lattest.Model.Symbolic.ValExpr.CstrId
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
    show (Variable name stype) = show name ++ ":" ++ show stype


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
     deriving (Eq, Ord, Show)

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
  deriving (Eq, Ord, Show)

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
reduceExpr (Vconst con)                                    = Vconst con
reduceExpr (Vvar v)                                        = Vvar v
reduceExpr (Vite (reduceExpr . view -> Vconst c) (view -> e1) (view -> e2))     = if toBool c then reduceExpr e1 else reduceExpr e2
reduceExpr (Vite (reduceExpr . view -> Vconst c) (view -> e1) (view -> e2))     = if toBool c then reduceExpr e1 else reduceExpr e2
reduceExpr (Vite (view -> c) (view -> e1) (view -> e2))            = Vite (ValExpr $ reduceExpr c) (ValExpr $ reduceExpr e1) (ValExpr $ reduceExpr e2)
reduceExpr (Vequal (reduceExpr . view -> e1) (reduceExpr . view -> e2))  =
    case (e1, e2) of
        (Vconst c1, Vconst c2) -> Vconst $ Cbool (c1 == c2)
        _ -> Vequal (ValExpr $ e1) (ValExpr $ e2)
{-reduceExpr e@(view -> Vequal { }) = e 
reduceExpr (view -> Vnot { })                                      = BoolType
reduceExpr (view -> Vnot { })                                      = BoolType
reduceExpr (view -> Vand { })                                      = BoolType
reduceExpr (view -> Vand { })                                      = BoolType
reduceExpr (view -> Vsum { })                                      = IntType
reduceExpr (view -> Vsum { })                                      = IntType
reduceExpr (view -> Vproduct { })                                  = IntType
reduceExpr (view -> Vproduct { })                                  = IntType
reduceExpr (view -> Vmodulo { })                                   = IntType
reduceExpr (view -> Vmodulo { })                                   = IntType
reduceExpr (view -> Vdivide { })                                   = IntType
reduceExpr (view -> Vdivide { })                                   = IntType
reduceExpr (view -> Vgez { })                                      = BoolType
reduceExpr (view -> Vgez { })                                      = BoolType
reduceExpr (view -> Vlength { })                                   = IntType
reduceExpr (view -> Vlength { })                                   = IntType
reduceExpr (view -> Vat { })                                       = StringType
reduceExpr (view -> Vat { })                                       = StringType
reduceExpr (view -> Vconcat { })                                   = StringType
reduceExpr (view -> Vconcat { })                                   = StringType-}
--reduceExpr (view -> Vstrinre { })                                  =
--reduceExpr (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

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
