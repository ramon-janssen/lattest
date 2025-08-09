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
( ValExprIntView(..)
, ValExprBoolView(..)
, ValExprStringView(..)
, ValExpr(..)       -- for local usage only!
, ValExprInt
, ValExprBool
, ValExprString
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
                    | VIntIte   {   conditionInt   :: ValExprBool
                                ,   trueBranchInt  :: ValExprInt
                                ,   falseBranchInt :: ValExprInt
                                }
                    | VIntDivide   {   dividend :: ValExprInt
                                ,   divisor  :: ValExprInt
                                }
                    | VIntModulo   {   dividend :: ValExprInt
                                ,   divisor  :: ValExprInt
                                }
                    | VIntSum      (FreeSum ValExprInt)
                    | VIntProduct  (FreeProduct ValExprInt)
                    | VLength   ValExprString
     deriving (Eq, Ord)

data ValExprBoolView = VBoolConst  Constant
                    | VBoolVar    Variable
                    | VEqualInt  ValExprInt ValExprInt
                    | VEqualBool  ValExprBool ValExprBool
                    | VEqualString  ValExprString ValExprString
                    | VBoolIte   {   conditionBool   :: ValExprBool
                                ,   trueBranchBool  :: ValExprBool
                                ,   falseBranchBool :: ValExprBool
                                }
                    | VGezInt      ValExprInt
                    | VNot      ValExprBool
                    | VAnd      (Set ValExprBool)
     deriving (Eq, Ord)

data ValExprStringView = VStringConst  Constant
                    | VStringVar    Variable
                    | VStringIte   {   conditionString   :: ValExprBool
                                ,   trueBranchString  :: ValExprString
                                ,   falseBranchString :: ValExprString
                                }
                    | VAt       {   string   :: ValExprString
                                ,   position :: ValExprInt
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
    show (VLength e) = "length(" ++ show e ++ ")"

instance Show ValExprBoolView where
    show (VBoolConst c) = show c
    show (VBoolVar v) = show v
    show (VEqualInt e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (VEqualBool e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (VEqualString e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (VBoolIte cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (VGezInt e) = "(" ++ show e ++ ") > 0"
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

type ValExprInt = ValExpr ValExprIntView
type ValExprBool = ValExpr ValExprBoolView
type ValExprString = ValExpr ValExprStringView

{-class Eval v where
    eval :: v -> Either String Constant
    evalView :: v -> Either String Constant
-}
-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: Eval v => ValExpr v -> Either String Constant
eval = evalView . view

class Reduce v => Eval v where
    evalView :: v -> Either String Constant
    isConst :: v -> Bool

instance Eval ValExprIntView where
    evalView (reduceExpr -> VIntConst v) = Right v
    evalView x          = Left $ "Value Expression is not a constant value " ++ show x
    isConst (VIntConst _) = True
    isConst _ = False

instance Eval ValExprBoolView where
    evalView (reduceExpr -> VBoolConst v) = Right v
    evalView x          = Left $ "Value Expression is not a constant value " ++ show x
    isConst (VBoolConst _) = True
    isConst _ = False

instance Eval ValExprStringView where
    evalView (reduceExpr -> VStringConst v) = Right v
    evalView x          = Left $ "Value Expression is not a constant value " ++ show x
    isConst (VStringConst _) = True
    isConst _ = False

class Reduce v where
    reduceExpr :: v -> v

instance Reduce ValExprIntView where
    --reduceExpr (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
    --reduceExpr (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
    --reduceExpr (view -> Viscstr { })                                   =
    --reduceExpr (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
    reduceExpr (VIntConst con) = VIntConst con
    reduceExpr (VIntVar v) = VIntVar v
    reduceExpr (VIntIte (reduceView -> VBoolConst c) (reduceView -> e1) (reduceView -> e2)) = if toBool c then e1 else e2
    reduceExpr (VIntIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = VIntIte c e1 e2
    reduceExpr (VIntSum (mapFreeMonoidX reduceView -> es)) | allFreeMonoidX isConst es = vint $ foldrTerms (+) 0 (mapFreeMonoidX getInt es)
    reduceExpr (VIntSum (mapFreeMonoidX reduce -> es)) = VIntSum es
    reduceExpr (VIntProduct (mapFreeMonoidX reduceView -> es)) | allFreeMonoidX isConst es = vint $ foldrTerms (*) 1 (mapFreeMonoidX getInt es)
    reduceExpr (VIntProduct (mapFreeMonoidX reduce -> es)) = VIntProduct es
    reduceExpr (VIntModulo (reduceView -> (VIntConst (Cint x))) (reduceView -> (VIntConst (Cint y)))) = vint $ x `mod` y
    reduceExpr (VIntModulo (reduce -> e1) (reduce -> e2)) = VIntModulo e1 e2
    reduceExpr (VIntDivide (reduceView -> (VIntConst (Cint x))) (reduceView -> (VIntConst (Cint y)))) = vint $ x `divInteger` y
    reduceExpr (VIntDivide (reduce -> e1) (reduce -> e2)) = VIntDivide e1 e2
    reduceExpr (VLength (reduceView -> (VStringConst (Cstring s)))) = vint $ textLength s
    reduceExpr (VLength (reduce -> e)) = VLength e
    --reduceExpr (view -> Vstrinre { })                                  =
    --reduceExpr (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

instance Reduce ValExprBoolView where
    --reduceExpr (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
    --reduceExpr (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
    --reduceExpr (view -> Viscstr { })                                   =
    --reduceExpr (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
    reduceExpr (VBoolConst con) = VBoolConst con
    reduceExpr (VBoolVar v) = VBoolVar v
    reduceExpr (VBoolIte (reduceView -> VBoolConst c) (reduceView -> e1) (reduceView -> e2)) = if toBool c then e1 else e2
    reduceExpr (VBoolIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = VBoolIte c e1 e2
    reduceExpr (VEqualInt (reduceView -> VIntConst e1) (reduceView -> VIntConst e2)) = VBoolConst $ Cbool (e1 == e2)
    reduceExpr (VEqualInt (reduce -> e1) (reduce -> e2)) = VEqualInt e1 e2
    reduceExpr (VEqualBool (reduceView -> VBoolConst e1) (reduceView -> VBoolConst e2)) = VBoolConst $ Cbool (e1 == e2)
    reduceExpr (VEqualBool (reduce -> e1) (reduce -> e2)) = VEqualBool e1 e2
    reduceExpr (VEqualString (reduceView -> VStringConst e1) (reduceView -> VStringConst e2)) = VBoolConst $ Cbool (e1 == e2)
    reduceExpr (VEqualString (reduce -> e1) (reduce -> e2)) = VEqualString e1 e2
    reduceExpr (VGezInt (reduceView -> (VIntConst (Cint x)))) = vbool $ x >= 0
    reduceExpr (VGezInt (reduce -> e)) = VGezInt e
    reduceExpr (VNot (reduceView -> (VBoolConst (Cbool b)))) = vbool b
    reduceExpr (VNot (reduce -> e)) = VNot e
    reduceExpr (VAnd (Set.map reduceView -> es)) | all isConst es = vbool $ foldr (&&) True (Set.map getBool es)
    reduceExpr (VAnd (Set.map reduce -> es)) = VAnd es
    --reduceExpr (view -> Vstrinre { })                                  =
    --reduceExpr (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

instance Reduce ValExprStringView where
    --reduceExpr (view -> Vfunc (FuncId _nm _uid _fa fs) _vexps)         =
    --reduceExpr (view -> Vcstr (CstrId _nm _uid _ca cs) _vexps)         =
    --reduceExpr (view -> Viscstr { })                                   =
    --reduceExpr (view -> Vaccess (CstrId _nm _uid ca _cs) _n p _vexps)  =
    reduceExpr (VStringConst con) = VStringConst con
    reduceExpr (VStringVar v) = VStringVar v
    reduceExpr (VStringIte (reduceView -> VBoolConst c) (reduceView -> e1) (reduceView -> e2)) = if toBool c then e1 else e2
    reduceExpr (VStringIte (reduce -> c) (reduce -> e1) (reduce -> e2)) = VStringIte c e1 e2
    reduceExpr (VAt (reduceView -> (VStringConst (Cstring s))) (reduceView -> (VIntConst (Cint i)))) = vtext $ charAt s i -- TODO are these semantics the same as in SMT2?
    reduceExpr (VAt (reduce -> e1) (reduce -> e2)) = VAt e1 e2
    reduceExpr (VConcat (fmap reduceView -> es)) | all isConst es = vtext $ Text.concat $ fmap getText es
    reduceExpr (VConcat (fmap reduce -> e)) = VConcat e
    --reduceExpr (view -> Vstrinre { })                                  =
    --reduceExpr (view -> Vpredef _kd (FuncId _nm _uid _fa fs) _vexps)   =

--getConst :: ValExprView -> Constant
getIntConst (VIntConst c) = c
getBoolConst (VBoolConst c) = c
getStringConst (VStringConst c) = c
--getInt :: ValExprView -> Integer
getInt = Const.toInteger . getIntConst
--getBool :: ValExprView -> Bool
getBool = toBool . getBoolConst
--getText :: ValExprView -> Text
getText = toText . getStringConst

-- variations of reduceExpr that work on ValExprs or produce ValExprs. Note that this is only to make the type checker happy.
reduceView :: Reduce t => ValExpr t -> t
reduceView = reduceExpr . view
reduce :: Reduce t => ValExpr t -> ValExpr t
reduce = ValExpr . reduceView
--vbool :: Bool -> ValExprView
vbool = VBoolConst . Cbool
--vint :: Integer -> ValExprView
vint = VIntConst . Cint
--vtext :: Text -> ValExprView
vtext = VStringConst . Cstring
textLength :: Text -> Integer
textLength = Prelude.toInteger . Text.length
charAt :: Text -> Integer -> Text
charAt t i = Text.pack $ if i > Prelude.toInteger (Text.length t) then [Text.index t (fromInteger i)] else "" 

class TypeableExpr t where
    typeOfExpr :: ValExpr t -> Type

instance TypeableExpr ValExprIntView where
    typeOfExpr _ = IntType

instance TypeableExpr ValExprBoolView where
    typeOfExpr _ = BoolType

instance TypeableExpr ValExprStringView where
    typeOfExpr _ = StringType

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
