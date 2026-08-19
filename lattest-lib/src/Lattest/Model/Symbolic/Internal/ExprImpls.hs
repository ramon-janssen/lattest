{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent Symbolic folder.
-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
module Lattest.Model.Symbolic.Internal.ExprImpls
( -- * Constructors to create Value Expressions
  -- ** Constant value
  sConst
, sTrue
, sFalse
  -- ** VarRef
, sVar
  -- ** General Operators to create Value Expressions
  -- *** Equal
, (.==)
  -- *** If Then Else
, sIfThenElse
  -- *** Function Call
--, cstrFunc
  -- ** Boolean Operators to create Value Expressions
  -- *** Not
, sNot
  -- *** And
, sAnd
  -- ** Numeric Operators to create Value Expressions
, ExprNum
  -- *** Sum
, sSum
  -- *** Product
, sProduct
  -- *** Divide
, (./)
  -- *** Modulo
, (.%)
  -- *** Comparisons GEZ
, sIsNonNegative
  -- ** List operations
, sLength
, sConcat
, sCons
, sNil
, sAppend
, sElem
, sTake
, sDrop
, sHead
, sTail
, sMap
  -- ** Set operations
, sInsert
, sEmptySet
, sSElem
  -- ** Pair operations
, sFirst
, sSecond
, sPair
  -- ** Either
, sEither
, sLeft
, sRight

-- * Substitution of var by value
, VarModel(..)
, assign
, Valuation(..)
, Val(..)
, emptyValuation
, assignValues
, assignValue
, insertIntoValuation
, substConst
, subst
, assignedExpr
, assignment
, noAssignment
, (=:)
, eval
, reduce
)
where

import           Control.Arrow   (first)
import qualified Data.Set        as Set

import qualified Lattest.Model.Symbolic.Internal.Boute as Boute
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX        as FMX
import           Lattest.Model.Symbolic.Internal.Product as Product
import           Lattest.Model.Symbolic.Internal.Sum as Sum
import           Lattest.Model.Symbolic.Internal.ExprDefs
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Constraint.Extras (Has (..))
import Data.Constraint.Compose (ComposeC)
import qualified Data.List as List
import Data.SBV (RCSet(..))
import Lattest.Model.Symbolic.Internal.FreeMonoidX (mapFreeMonoidX, allFreeMonoidX)
import GHC.Integer (divInteger)

sConst :: ExprConstraints t => t -> Expr t
sConst = Expr . Const

sTrue :: Expr Bool
sTrue = sConst True

sFalse :: Expr Bool
sFalse = sConst False

sVar :: Variable t -> Expr t
sVar = Expr . Var

-- | Apply operator ITE (IF THEN ELSE) on the provided value expressions.
-- Preconditions are /not/ checked.
sIfThenElse :: Expr Bool -> Expr t -> Expr t -> Expr t
sIfThenElse (view -> Const True) t _ = t
sIfThenElse (view -> Const False) _ f = f
sIfThenElse (view -> c) (view -> t) (view -> f) = Expr $ Ite c t f

(.==) :: ExprConstraints t => Expr t -> Expr t -> Expr Bool
x .== y = Expr $ Equal (typeOf' x) (view x) (view y)
infix 4 .==

{-
-- | Apply operator Equal on the provided value expressions.
-- Preconditions are /not/ checked.
(.==) :: Expr -> Expr -> Expr
-- Simplification a == a <==> True
(.==) ve1 ve2 | ve1 == ve2                      = sConst (Cbool True)
-- Simplification Different Values <==> False : use Same Values are already detected in previous step
(.==) (view -> Vconst _) (view -> Vconst _)     = sConst (Cbool False)
-- Simplification True == e <==> e (twice)
(.==) (view -> Vconst (Cbool True)) e           = e
(.==) e (view -> Vconst (Cbool True))           = e

-- Simplification False == e <==> not e (twice)
(.==) (view -> Vconst (Cbool False)) e              = sNot e
(.==) e (view -> Vconst (Cbool False))              = sNot e
-- Not x == x <==> false (twice)
(.==) e (view -> Vnot n) | e == n                   = sConst (Cbool False)
(.==) (view -> Vnot n) e | e == n                   = sConst (Cbool False)
-- Not x == Not y <==> x == y   -- same representation
(.==) (view -> Vnot n1) (view -> Vnot n2)     = (.==) n1 n2
-- Not a == b <==> a == Not b -- same representation (twice)
(.==) x@(view -> Vnot n) e                = if n <= e
                                                        then Expr (Vequal x e)
                                                        else Expr (Vequal (sNot e) n)
(.==) e x@(view -> Vnot n)                = if n <= e
                                                        then Expr (Vequal x e)
                                                        else Expr (Vequal (sNot e) n)
-- a == b <==> b == a -- same representation
(.==) ve1 ve2                                   = if ve1 <= ve2
                                                        then Expr (Vequal ve1 ve2)
                                                        else Expr (Vequal ve2 ve1)
-}

-- | Apply operator Not on the provided value expression.
-- Preconditions are /not/ checked.
sNot :: Expr Bool -> Expr Bool
{-sNot (view -> Vconst (Cbool True))       = sConst (Cbool False)
sNot (view -> Vconst (Cbool False))      = sConst (Cbool True)
sNot (view -> Vnot ve)                   = ve
-- not (if cs then tb else fb) == if cs then not (tb) else not (fb)
sNot (view -> Vite cs tb fb)             = Expr (Vite cs (sNot tb) (sNot fb))-}
sNot (view -> ve) = Expr $ Not ve

-- | Apply operator And on the provided set of value expressions.
-- Preconditions are /not/ checked.
sAnd :: Set.Set (Expr Bool) -> Expr Bool
--sAnd = sAnd' . flattenAnd
sAnd = Expr . And . flattenAnd
    where
        flattenAnd :: Set.Set (Expr Bool) -> Set.Set (ExprView Bool)
        flattenAnd = Set.unions . map fromExpr . Set.toList

        fromExpr :: Expr Bool -> Set.Set (ExprView Bool)
        fromExpr (view -> And a) = a
        fromExpr (view -> x) = Set.singleton x
{-
-- And doesn't contain elements of type Vand.
sAnd' :: Set.Set Expr Bool -> Expr Bool
sAnd' s =
    if Set.member (sConst (Cbool False)) s
        then sConst (Cbool False)
        else let s' = Set.delete (sConst (Cbool True)) s in
                case Set.size s' of
                    0   -> sConst (Cbool True)
                    1   -> head (Set.toList s')
                    _   ->  -- not(x) and x == False
                            let nots = filterNot (Set.toList s') in
                                if any (contains s') nots
                                    then sConst (Cbool False)
--                                    else let ts = isCstrTuples (Set.toList s') in
--                                            if sameExpr ts
--                                                then sConst (Cbool False)
                                                else Expr (Vand s')
    where
        filterNot :: [Expr] -> [Expr]
        filterNot [] = []
        filterNot (x:xs) = case view x of
                            Vnot n -> n : filterNot xs
                            _      ->     filterNot xs
        
        contains :: Set.Set Expr -> Expr -> Bool
        contains set (view -> Vand a) = all (`Set.member` set) (Set.toList a)
        contains set a                = Set.member a set
{-
        isCstrTuples :: [Expr] -> [(CstrId, Expr)]
        isCstrTuples [] = []
        isCstrTuples (x:xs) = case view x of
                                Viscstr c v -> (c,v) : isCstrTuples xs
                                _           ->         isCstrTuples xs
-}
        sameExpr :: [(CstrId, Expr)] ->  Bool
        sameExpr []     = False
        sameExpr (x:xs) = containExpr x xs
            where
                containExpr :: (CstrId, Expr) -> [(CstrId, Expr)] ->  Bool
                containExpr _      []             = False
                containExpr (c1,x1) ((c2,x2):cxs) = if x1 == x2 
                                                        then assert (c1 /= c2) True
                                                        else containExpr (c1,x1) cxs
-}

-- * Sum
isSum :: ExprView Integer -> Bool
isSum (Sum _) = True
isSum _ = False

getSum :: ExprView Integer -> FreeSum (ExprView Integer)
getSum (Sum s) = s
getSum _ = error "ExprImpls.hs - getSum - Unexpected Expr "

sSumInt :: FreeSum (Expr Integer) -> Expr Integer
sSumInt = Expr . cstrSum . FMX.mapTerms (SumTerm . view . summand)

-- | Apply operator sum on the provided sum of value expressions.
-- Preconditions are /not/ checked.
cstrSum :: FreeSum (ExprView Integer) -> ExprView Integer
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the sum of all values
--         special case if the sum is zero, no value is inserted since v == v+0
--    remove all nested sums, since (a+b) + (c+d) == (a+b+c+d)
cstrSum ms = cstrSum' $ nonadds <> FMX.flatten sumOfAdds
    where
      (adds, nonadds) = FMX.partitionT isSum ms
      sumOfAdds :: FMX.FreeMonoidX (FMX.FreeMonoidX (SumTerm (ExprView Integer)))
      sumOfAdds = FMX.mapTerms (getSum . summand) adds

-- Sum doesn't contain elements of type VExprSum
cstrSum' :: FreeSum (ExprView Integer) -> ExprView Integer
cstrSum' ms =
    let (vals, nonvals) = FMX.partitionT isConst ms
        valueSum = FMX.mapTerms (SumTerm . getConst . summand) vals
        sumVals = summand $ FMX.foldFMX valueSum
        retMS = case sumVals of
                    0 -> nonvals                                      -- 0 + x == x
                    _ -> Sum.add (Const sumVals) nonvals
    in
        case FMX.toOccurList retMS of
            []         -> Const 0 -- sum of nothing equal zero
            [(term,1)] -> summand term
            _          -> Sum retMS

getConst :: ExprView e -> e
getConst (Const c) = c
getConst _ = error "Not Const"

isSumF :: ExprView Double -> Bool
isSumF (SumFloat _) = True
isSumF _ = False

getSumF :: ExprView Double -> FreeSum (ExprView Double)
getSumF (SumFloat s) = s
getSumF _ = error "ExprImpls.hs - getSumF - Unexpected Expr "

sSumFloat :: FreeSum (Expr Double) -> Expr Double
sSumFloat = Expr . cstrSumF . FMX.mapTerms (SumTerm . view . summand)

-- | Apply operator sum on the provided sum of floating-point values.
cstrSumF :: FreeSum (ExprView Double) -> ExprView Double
cstrSumF ms = cstrSumF' $ nonadds <> FMX.flatten sumOfAdds
    where
      (adds, nonadds) = FMX.partitionT isSumF ms
      sumOfAdds :: FMX.FreeMonoidX (FMX.FreeMonoidX (SumTerm (ExprView Double)))
      sumOfAdds = FMX.mapTerms (getSumF . summand) adds

cstrSumF' :: FreeSum (ExprView Double) -> ExprView Double
cstrSumF' ms =
    let (vals, nonvals) = FMX.partitionT isConst ms
        valueSum = FMX.mapTerms (SumTerm . getConst . summand) vals
        sumVals = summand $ FMX.foldFMX valueSum
        retMS = case sumVals of
                    0.0 -> nonvals                                   -- 0.0 + x == x
                    _   -> Sum.add (Const sumVals) nonvals
    in
        case FMX.toOccurList retMS of
            []         -> Const 0.0 -- sum of nothing equals zero
            [(term,1)] -> summand term
            _          -> SumFloat retMS

-- Product

-- | Is Expr a Product Expression?
isProduct :: ExprView Integer -> Bool
isProduct (Product _) = True
isProduct _ = False

getProduct :: ExprView Integer -> FreeProduct (ExprView Integer)
getProduct (Product p) = p
getProduct _ = error "ExprImpls.hs - getProduct - Unexpected Expr "

sProductInt :: FreeProduct (Expr Integer) -> Expr Integer
sProductInt = Expr . cstrPrd . FMX.mapTerms (ProductTerm . view . factor)

-- | Apply operator product on the provided product of value expressions.
-- Be aware that division is not associative for Integer, so only use power >= 0.
-- Preconditions are /not/ checked.
cstrPrd :: FreeProduct (ExprView Integer) -> ExprView Integer
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the product of all values
--         special case if the product is one, no value is inserted since v == v*1
--    remove all nested products, since (a*b) * (c*d) == (a*b*c*d)
cstrPrd ms =
    cstrPrd' $ noprods <> FMX.flatten prodOfProds
    where
      (prods, noprods) = FMX.partitionT isProduct ms
      prodOfProds :: FMX.FreeMonoidX (FMX.FreeMonoidX (ProductTerm (ExprView Integer)))
      prodOfProds = FMX.mapTerms (getProduct . factor) prods

-- Product doesn't contain elements of type VExprProduct
cstrPrd' :: FreeProduct (ExprView Integer) -> ExprView Integer
cstrPrd' ms =
    let (vals, nonvals) = FMX.partitionT isConst ms
        (zeros, _) = FMX.partitionT isZero vals
    in
        case FMX.nrofDistinctTerms zeros of
            0   ->  -- let productVals = Product.foldPower timesVal 1 vals in
                    let intProducts = FMX.mapTerms (getConst <$>) vals
                        productVals = factor (FMX.foldFMX intProducts)
                    in
                        case FMX.toDistinctAscOccurListT nonvals of
                            []          ->  Const productVals
                            [(term, 1)] ->  cstrSum (FMX.fromOccurList [(SumTerm term, productVals)])                           -- term can be Sum -> rewrite needed
                            _           ->  cstrSum (FMX.fromOccurList [(SumTerm (Product nonvals), productVals)])  -- productVals can be 1 -> rewrite possible
            _   ->  let (_, n) = Product.fraction zeros in
                        case FMX.nrofDistinctTerms n of
                            0   ->  Const 0      -- 0 * x == 0
                            _   ->  error "Error in model: Division by Zero in Product (via negative power)"
    where
        isZero :: ExprView Integer -> Bool
        isZero (Const 0) = True
        isZero _         = False

-- Product of floating-point values
isProductF :: ExprView Double -> Bool
isProductF (ProductFloat _) = True
isProductF _ = False

getProductF :: ExprView Double -> FreeProduct (ExprView Double)
getProductF (ProductFloat p) = p
getProductF _ = error "ExprImpls.hs - getProductF - Unexpected Expr "

sProductFloat :: FreeProduct (Expr Double) -> Expr Double
sProductFloat = Expr . cstrPrdF . FMX.mapTerms (ProductTerm . view . factor)

-- | Apply operator product on the provided product of floating-point values.
cstrPrdF :: FreeProduct (ExprView Double) -> ExprView Double
cstrPrdF ms =
    cstrPrdF' $ noprods <> FMX.flatten prodOfProds
    where
      (prods, noprods) = FMX.partitionT isProductF ms
      prodOfProds :: FMX.FreeMonoidX (FMX.FreeMonoidX (ProductTerm (ExprView Double)))
      prodOfProds = FMX.mapTerms (getProductF . factor) prods

-- Product doesn't contain elements of type ProductFloat
cstrPrdF' :: FreeProduct (ExprView Double) -> ExprView Double
cstrPrdF' ms =
    let (vals, nonvals) = FMX.partitionT isConst ms
        (zeros, _) = FMX.partitionT isZeroF vals
    in
        case FMX.nrofDistinctTerms zeros of
            0   ->  let floatProducts = FMX.mapTerms (getConst <$>) vals
                        productVals = factor (FMX.foldFMX floatProducts)
                        withConst = if productVals == 1.0           -- 1.0 * x == x
                                        then nonvals
                                        else Product.multiply (Const productVals) nonvals
                    in
                        case FMX.toDistinctAscOccurListT withConst of
                            []          ->  Const productVals
                            [(term, 1)] ->  term
                            _           ->  ProductFloat withConst
            _   ->  let (_, n) = Product.fraction zeros in
                        case FMX.nrofDistinctTerms n of
                            0   ->  Const 0.0      -- 0.0 * x == 0.0
                            _   ->  error "Error in model: Division by Zero in Product (via negative power)"
    where
        isZeroF :: ExprView Double -> Bool
        isZeroF (Const 0.0) = True
        isZeroF _           = False

-- Divide

-- | Apply operator Divide on the provided integer value expressions.
-- Preconditions are /not/ checked.
divideInt :: Expr Integer -> Expr Integer -> Expr Integer
divideInt (view ->  Const t) (view -> Const n) | n /= 0 = sConst (t `Boute.div` n) -- leave error case (division by zero) unevaluated
divideInt (view -> vet)         (view -> ven) = Expr (Divide vet ven)

-- | Apply operator Divide on the provided floating-point value expressions.
-- Preconditions are /not/ checked.
divideFloat :: Expr Double -> Expr Double -> Expr Double
divideFloat (view ->  Const t) (view -> Const n) | n /= 0 = sConst (t / n) -- leave error case (division by zero) unevaluated
divideFloat (view -> vet)         (view -> ven) = Expr (DivideFloat vet ven)

-- Modulo

-- | Apply operator Modulo on the provided value expressions.
-- Preconditions are /not/ checked.
(.%) :: Expr Integer -> Expr Integer -> Expr Integer
(.%) (view -> Const t) (view -> Const n) | n /= 0 = sConst (t `Boute.mod` n) -- leave error case (division by zero) unevaluated
(.%) (view -> vet)        (view -> ven) = Expr (Modulo vet ven)

infixl 7 .%

-- | Apply operator GEZ (Greater Equal Zero) on the provided integer value expression.
-- Preconditions are /not/ checked.
sIsNonNegativeInt :: Expr Integer -> Expr Bool
-- Simplification Values
sIsNonNegativeInt (view -> Const v) = sConst (0 <= v)
sIsNonNegativeInt (view -> Length _ _)   = sConst True        -- length of list is always Greater or equal to zero
sIsNonNegativeInt (view -> ve)         = Expr (GezInt ve)

-- | Apply operator GEZ (Greater Equal Zero) on the provided floating-point value expression.
-- Preconditions are /not/ checked.
sIsNonNegativeFloat :: Expr Double -> Expr Bool
sIsNonNegativeFloat (view -> Const v) = sConst (0 <= v)
sIsNonNegativeFloat (view -> ve)      = Expr (GezFloat ve)

class Ord t => ExprNum t where
    sSum :: FreeSum (Expr t) -> Expr t
    sProduct :: FreeProduct (Expr t) -> Expr t
    sIsNonNegative :: Expr t -> Expr Bool
    (./) :: Expr t -> Expr t -> Expr t

infixl 7 ./

instance ExprNum Integer where
    sSum = sSumInt
    sProduct = sProductInt
    sIsNonNegative = sIsNonNegativeInt
    (./) = divideInt

instance ExprNum Double where
    sSum = sSumFloat
    sProduct = sProductFloat
    sIsNonNegative = sIsNonNegativeFloat
    (./) = divideFloat

sConcat :: ExprConstraints a => Expr [[a]] -> Expr [a]
sConcat = Expr . Concat . view

-- implementation details:
-- Properties incorporated
--    "" ++ x == x          - remove empty strings
--    "a" ++ "b" == "ab"    - concat consecutive string values
--   remove all nested sConcat, since (a ++ b) ++ (c ++ d) == (a ++ b ++ c ++ d)

sLength :: Expr [x] -> Expr Integer
sLength (view -> x) = Expr $ Length (case has @ExprType x $ typeOf' x of ListType t -> t) x

sCons :: Expr x -> Expr [x] -> Expr [x]
sCons (view -> x) (view -> xs) = Expr $ Cons x xs

sNil :: ExprConstraints x => Expr [x]
sNil = Expr $ Const []

sAppend :: Expr [x] -> Expr [x] -> Expr [x]
sAppend (view -> xs) (view -> ys) = Expr $ Append xs ys

sElem :: Expr x -> Expr [x] -> Expr Bool
sElem (view -> x) (view -> xs) = Expr $ LElem (has @ExprType x $ typeOf' x) x xs

sTake :: Expr Integer -> Expr [x] -> Expr [x]
sTake (view -> i) (view -> xs) = Expr $ Take i xs

sDrop :: Expr Integer -> Expr [x] -> Expr [x]
sDrop (view -> i) (view -> xs) = Expr $ Drop i xs

sFirst :: ExprType b => Expr (t, b) -> Expr t
sFirst (view -> i) = Expr $ First (typeOf undefined) i

sSecond :: ExprType a => Expr (a, t) -> Expr t
sSecond (view -> i) = Expr $ Second (typeOf undefined) i

sPair :: Expr a -> Expr b -> Expr (a, b)
sPair (view -> x) (view -> y) = Expr $ Pair x y

sHead :: ExprConstraints x => Expr [x] -> Expr x
sHead (view -> xs) = Expr $ Head xs

sTail :: ExprConstraints x => Expr [x] -> Expr [x]
sTail (view -> xs) = Expr $ Tail xs

-- | Map a function over a list. Think of the variable a and the expression b as morally forming a function a -> b:
-- the variable will, within the expression, represent the argument to the function.
sMap :: (ExprConstraints a, ExprConstraints b) => Variable a -> Expr b -> Expr [a] -> Expr [b]
sMap v (view -> b) (view -> xs) = Expr $ Map v b xs

-- | Case-of on Either: If sMap can be thought of as having type `(a -> b) -> List a -> List b`,
-- SEither should be considered as having type `(a -> c) -> (b -> c) -> Either a b -> c`.
sEither :: (ExprConstraints a, ExprConstraints b, ExprConstraints c) => Variable a -> Variable b -> Expr c -> Expr c -> Expr (Either a b) -> Expr c
sEither lv rv (view -> le) (view -> re) (view -> e) = Expr $ Either lv rv le re e

sLeft :: (ExprConstraints a, ExprConstraints b) => Expr a -> Expr (Either a b)
sLeft (view -> a) = Expr $ ELeft a

sRight :: (ExprConstraints a, ExprConstraints b) => Expr b -> Expr (Either a b)
sRight (view -> b) = Expr $ ERight b

sEmptySet :: (ExprConstraints a, ExprConstraints (RCSet a)) => Expr (RCSet a)
sEmptySet = Expr $ Const $ RegularSet $ Set.fromList []

sInsert :: ExprConstraints a => Expr a -> Expr (RCSet a) -> Expr (RCSet a)
sInsert (view -> x) (view -> xs) = Expr $ SInsert x xs

sSElem :: ExprConstraints a => Expr a -> Expr (RCSet a) -> Expr Bool
sSElem (view -> x) (view -> xs) = Expr $ SElem (typeOf' x) x xs

-- | Apply String In Regular Expression operator on the provided value expressions.
-- Preconditions are /not/ checked.
--cstrStrInRe :: Expr -> Expr -> Expr
--cstrStrInRe (view -> Vconst (Cstring s)) (view -> Vconst (Cregex r)) = sConst (Cbool (T.unpack s =~ T.unpack (xsd2posix r) ) )
--cstrStrInRe s r                                                      = Expr (Vstrinre s r)

{-
-- | Create a call to a predefined function as a value expression.
cstrPredef :: PredefKind -> FuncId -> [Expr] -> Expr
cstrPredef p f a = Expr (Vpredef p f a)
-}

data Val t where
  Val :: ExprConstraints t => { runVal :: t } -> Val t
deriving instance Eq (Val t)
deriving instance Ord (Val t)
instance Show (Val t) where
  show (Val t) = show t
newtype Valuation = Valuation { runValuation :: DMap Variable Val }
  deriving (Eq, Ord)
instance Has (ComposeC Eq Val) Variable where
  has _ k = k
instance Has (ComposeC Ord Val) Variable where
  has _ k = k
instance Has (ComposeC Show Val) Variable where
  has _ k = k

instance Show Valuation where
  show (Valuation val) = "{" ++ List.intercalate "," (printAsAssignments val) ++ "}"
    where
    printAsAssignments :: DMap Variable Val -> [String]
    printAsAssignments = DMap.foldrWithKey printAsAssignment []
    printAsAssignment v t strs = (varName v ++ ":=" ++ show t) : strs

assignValues :: [Valuation -> Valuation] -> Valuation
assignValues = foldr ($) emptyValuation

emptyValuation :: Valuation
emptyValuation = Valuation DMap.empty

newtype VarModel = VarModel {runVarModel :: DMap Variable Expr}
  deriving (Eq, Ord)
instance Show VarModel where
  show (VarModel vm) = "{" ++ List.intercalate ", " (printAsAssignments vm) ++ "}"
    where
    printAsAssignments :: DMap Variable Expr -> [String]
    printAsAssignments = DMap.foldrWithKey printAsAssignment []
    printAsAssignment v t strs = (varName v ++ ":=" ++ show t) : strs

assignment :: [VarModel -> VarModel] -> VarModel
assignment = foldr ($) noAssignment

valuationToVarModel :: Valuation -> VarModel
valuationToVarModel = VarModel . DMap.map (\(Val v) -> sConst v) . runValuation

insertIntoValuation :: Variable t -> Constant t -> Valuation -> Valuation
insertIntoValuation v@(Variable _ IntType) c = assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ FloatType) c = assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ BoolType) c = assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ CharType) c = assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ t@(ListType _)) c = withExprConstraints t $ assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ t@(SetType _)) c = withExprConstraints t $ assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ t@(TupleType _ _)) c = withExprConstraints t $ assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ t@(SumType _ _)) c = withExprConstraints t $ assignValue v (fromConst' c)

fromConst' :: ConstType a => Constant a -> a
fromConst' = fromConst


(=:) :: Variable t -> Expr t -> VarModel -> VarModel
(=:) = assign
infixr 0 =:

assign :: Variable t -> Expr t -> VarModel -> VarModel
assign v e = VarModel . DMap.insert v e . runVarModel

assignValue :: ExprConstraints t => Variable t -> t -> Valuation -> Valuation
assignValue v val = Valuation . DMap.insert v (Val val) . runValuation

assignedExpr :: Variable t -> VarModel -> Maybe (Expr t)
assignedExpr v = DMap.lookup v . runVarModel

assignedExprWithDefault :: Variable t -> VarModel -> Expr t
assignedExprWithDefault v = DMap.findWithDefault (sVar v) v . runVarModel

noAssignment :: VarModel
noAssignment = VarModel DMap.empty

substConst :: Valuation -> Expr t -> Expr t
substConst valuation = subst (valuationToVarModel valuation)

-- | Substitute variables by value expressions in a value expression.
--
-- Preconditions are /not/ checked.
--
subst :: VarModel      -- ^ Map from variables to value expressions.
{-      -> Map.Map FuncId (FuncDef w e) -- ^ Map from identifiers to their
                                    -- definitions, this is used to replace
                                    -- function calls by their bodies if all
                                    -- the arguments of the function are
                                    -- constant.-}
      -> Expr t                -- ^ Value expression where the
                                    -- substitution will take place.
      -> Expr t
--subst ve _ x   | ve == Map.empty = x
subst ve x = subst' ve (view x)

subst' :: VarModel -> ExprView t -> Expr t
subst' _  (Const const')          = sConst const'
subst' ve (Var vid)               = assignedExprWithDefault vid ve
subst' ve (Ite cond vexp1 vexp2)  = sIfThenElse (subst' ve cond) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (Divide t n)            = (./) (subst' ve t) (subst' ve n)
subst' ve (Modulo t n)            = (.%) (subst' ve t) (subst' ve n)
subst' ve (DivideFloat t n)       = (./) (subst' ve t) (subst' ve n)
subst' ve (Sum s)                 = sSum $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT s
subst' ve (SumFloat s)            = sSum $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT s
subst' ve (Product p)             = sProduct $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT p
subst' ve (ProductFloat p)        = sProduct $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT p
subst' ve (Length _ vexp) = sLength $ subst' ve vexp
subst' ve (GezInt v)                = sIsNonNegative (subst' ve v)
subst' ve (Equal _ vexp1 vexp2)    = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (GezFloat v)              = sIsNonNegative (subst' ve v)
subst' ve (And vexps)               = sAnd $ Set.map (subst' ve) vexps
subst' ve (Not vexp)                = sNot (subst' ve vexp)
subst' ve (Concat vexps)                = sConcat $ subst' ve vexps
subst' ve (Cons x xs) = has @ExprType x $ sCons (subst' ve x) (subst' ve xs)
subst' ve (Append xs ys) = sAppend (subst' ve xs) (subst' ve ys)
subst' ve (LElem t x xs) = has @ExprType t $ sElem (subst' ve x) (subst' ve xs)
subst' ve (Take x xs) = sTake (subst' ve x) (subst' ve xs)
subst' ve (Drop x xs) = sDrop (subst' ve x) (subst' ve xs)
subst' ve (First t x) = has @ExprType t $ sFirst $ subst' ve x
subst' ve (Second t x) = has @ExprType t $ sSecond $ subst' ve x
subst' ve (Pair x y) = sPair (subst' ve x) (subst' ve y)
subst' ve (Head x) = sHead $ subst' ve x
subst' ve (Tail x) = sTail $ subst' ve x
subst' ve (ELeft x) = sLeft $ subst' ve x
subst' ve (ERight x) = sRight $ subst' ve x
subst' ve (SElem t x xs) = withExprConstraints t $ sSElem (subst' ve x) (subst' ve xs)
subst' ve (SInsert x xs) = sInsert (subst' ve x) (subst' ve xs)
subst' ve (Map v f xs) = Expr $ Map (case assignedExprWithDefault v ve of {Expr (Var v') -> v'; _ -> error "impossible"}) (view $ subst' ve f) (view $ subst' ve xs)
subst' ve (Either vl vr l r x) = Expr $ Either
  (case assignedExprWithDefault vl ve of { Expr (Var v) -> v; _ -> error "impossible"})
  (case assignedExprWithDefault vr ve of { Expr (Var v) -> v; _ -> error "impossible"})
  (view $ subst' ve l)
  (view $ subst' ve r)
  (view $ subst' ve x)


-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: Expr v -> Either String v
eval = evalView . view

evalView :: ExprView v -> Either String v
evalView (reduce -> Const v) = Right v
evalView _ = Left "Value Expression is not a constant value"

reduce :: ExprView v -> ExprView v
reduce (Var v) = Var v
reduce (Const v) = Const v
reduce (Ite (reduce -> Const b) (reduce -> e1) (reduce -> e2)) = if b then e1 else e2
reduce (Ite (reduce -> c) (reduce -> e1) (reduce -> e2)) = Ite c e1 e2
reduce (Sum (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Sum (mapFreeMonoidX reduce -> es)) = Sum es
reduce (SumFloat (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (SumFloat (mapFreeMonoidX reduce -> es)) = SumFloat es
reduce (Product (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Product (mapFreeMonoidX reduce -> es)) = Product es
reduce (ProductFloat (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (ProductFloat (mapFreeMonoidX reduce -> es)) = ProductFloat es
reduce (Modulo (reduce -> e1) (reduce -> e2@(Const 0))) = Modulo e1 e2 -- leave divisions by zero as expressions
reduce (Modulo (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `mod` y
reduce (Modulo (reduce -> e1) (reduce -> e2)) = Modulo e1 e2
reduce (Divide (reduce -> e1) (reduce -> e2@(Const 0))) = Divide e1 e2 -- leave divisions by zero as expressions
reduce (Divide (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `divInteger` y
reduce (Divide (reduce -> e1) (reduce -> e2)) = Divide e1 e2
reduce (DivideFloat (reduce -> e1) (reduce -> e2@(Const 0))) = DivideFloat e1 e2 -- leave divisions by zero as expressions
reduce (DivideFloat (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x / y
reduce (DivideFloat (reduce -> e1) (reduce -> e2)) = DivideFloat e1 e2
reduce (Length _ (reduce -> Const xs)) = Const $ fromIntegral $ length xs
reduce (Length t (reduce -> e)) = Length t e
reduce (Equal _ (reduce -> Const e1) (reduce -> Const e2)) = Const (e1 == e2)
reduce (Equal t (reduce -> e1) (reduce -> e2)) = Equal t e1 e2
reduce (GezInt (reduce -> (Const x))) = Const $ x >= 0
reduce (GezInt (reduce -> e)) = GezInt e
reduce (GezFloat (reduce -> (Const x))) = Const $ x >= 0
reduce (GezFloat (reduce -> e)) = GezFloat e
reduce (Not (reduce -> (Const b))) = Const $ not b
reduce (Not (reduce -> e)) = Not e
reduce (And (Set.map reduce -> es)) | all isConst es = Const $ and (Set.map constant es) -- TODO could be optimized further: if not all elements are constant, but if there are multiple constant elements, then the latter could still be combined
reduce (And (Set.map reduce -> es)) = And es
reduce (Concat (reduce -> es))
  | Const as <- es = Const $ concat as
reduce (Concat (reduce -> e)) = Concat e
reduce (Cons (reduce -> x) (reduce -> xs))
  | Const a <- x
  , Const as <- xs = Const $ a : as
  | otherwise = Cons x xs
reduce (Append (reduce -> xs) (reduce -> ys))
  | Const as <- xs
  , Const bs <- ys = Const $ as ++ bs
  | otherwise = Append xs ys
reduce (LElem t (reduce -> x) (reduce -> xs))
  | Const a <- x
  , Const as <- xs = Const $ a `elem` as
  | otherwise = LElem t x xs
reduce (Take (reduce -> i) (reduce -> xs))
  | Const j <- i
  , Const as <- xs = Const $ take (fromInteger j) as
  | otherwise = Take i xs
reduce (Drop (reduce -> i) (reduce -> xs))
  | Const j <- i
  , Const as <- xs = Const $ drop (fromInteger j) as
  | otherwise = Drop i xs
reduce (First tp (reduce -> x))
  | Const (y,_) <- x = case typeOf' x of
      TupleType t _ -> withExprConstraints t $ Const y
  | otherwise = First tp x
reduce (Second tp (reduce -> x))
  | Const (_,y) <- x = case typeOf' x of
      TupleType _ t -> withExprConstraints t $ Const y
  | otherwise = Second tp x
reduce (Pair (reduce -> x) (reduce -> y))
  | Const a <- x
  , Const b <- y = Const (a,b)
  | otherwise = Pair x y
reduce (Head (reduce -> xs))
  | Const (y:_) <- xs = Const y
  | Const [] <- xs = error "Head of empty list"
  | otherwise = Head xs
reduce (Tail (reduce -> xs))
  | Const (_:y) <- xs = Const y
  | Const [] <- xs = error "Tail of empty list"
  | otherwise = Tail xs
reduce (ELeft (reduce -> x))
  | Const y <- x = Const (Left y)
  | otherwise = ELeft x
reduce (ERight (reduce -> x))
  | Const y <- x = Const (Right y)
  | otherwise = ERight x
reduce (SElem t (reduce -> x) (reduce -> xs))
  | Const y <- x
  , Const ys <- xs = case ys of
      RegularSet    s -> Const $       y `Set.member` s
      ComplementSet s -> Const $ not $ y `Set.member` s
  | otherwise = SElem t x xs
reduce (SInsert (reduce -> x) (reduce -> xs))
  | Const y <- x
  , Const ys <- xs = case ys of
      RegularSet    s -> Const $ RegularSet    $ y `Set.insert` s
      ComplementSet s -> Const $ ComplementSet $ y `Set.delete` s
  | otherwise = SInsert x xs
reduce (Map v (reduce -> f') (reduce -> xs))
  | Const ys <- xs =
    let f y = reduce $ view $ subst' (VarModel $ DMap.singleton v $ Expr $ Const y) f'
        zs = map f ys
    in case traverse (\case
                        Const a -> Just a
                        _ -> Nothing) zs of
      Just as -> Const as
      Nothing -> Map v f' xs
  | otherwise = Map v f' xs
reduce (Either vl vr (reduce -> l) (reduce -> r) (reduce -> x))
  | Const (Left x') <- x =
    reduce $ view $ subst' (VarModel $ DMap.singleton vl $ Expr $ Const x') l
  | Const (Right x') <- x =
    reduce $ view $ subst' (VarModel $ DMap.singleton vr $ Expr $ Const x') r
  | otherwise = Either vl vr l r x

