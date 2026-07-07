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
  -- ** Integer Operators to create Value Expressions
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
  -- ** String Operators to create Value Expressions
  -- *** Length operator
, sLength
  -- *** Concat operator
, sConcat

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

sSum :: FreeSum (Expr Integer) -> Expr Integer
sSum = Expr . cstrSum . FMX.mapTerms (SumTerm . view . summand)

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



-- Product

-- | Is Expr a Product Expression?
isProduct :: ExprView Integer -> Bool
isProduct (Product _) = True
isProduct _ = False

getProduct :: ExprView Integer -> FreeProduct (ExprView Integer)
getProduct (Product p) = p
getProduct _ = error "ExprImpls.hs - getProduct - Unexpected Expr "

sProduct :: FreeProduct (Expr Integer) -> Expr Integer
sProduct = Expr . cstrPrd . FMX.mapTerms (ProductTerm . view . factor)

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
-- Divide

-- | Apply operator Divide on the provided value expressions.
-- Preconditions are /not/ checked.
(./) :: Expr Integer -> Expr Integer -> Expr Integer
(./) (view ->  Const t) (view -> Const n) | n /= 0 = sConst (t `Boute.div` n) -- leave error case (division by zero) unevaluated
(./) (view -> vet)         (view -> ven) = Expr (Divide vet ven)

infixl 7 ./

-- Modulo

-- | Apply operator Modulo on the provided value expressions.
-- Preconditions are /not/ checked.
(.%) :: Expr Integer -> Expr Integer -> Expr Integer
(.%) (view -> Const t) (view -> Const n) | n /= 0 = sConst (t `Boute.mod` n) -- leave error case (division by zero) unevaluated
(.%) (view -> vet)        (view -> ven) = Expr (Modulo vet ven)

infixl 7 .%

-- | Apply operator GEZ (Greater Equal Zero) on the provided value expression.
-- Preconditions are /not/ checked.
sIsNonNegative :: Expr Integer -> Expr Bool
-- Simplification Values
sIsNonNegative (view -> Const v) = sConst (0 <= v)
sIsNonNegative (view -> Length _)   = sConst True        -- length of string is always Greater or equal to zero
sIsNonNegative (view -> ve)         = Expr (GezInt ve)


-- | Apply operator Length on the provided value expression.
-- Preconditions are /not/ checked.
sLength :: Expr String -> Expr Integer
sLength (view -> Const s) = sConst (Prelude.toInteger (length s))
sLength (view -> v)             = Expr (Length v)

-- | Apply operator Concat on the provided sequence of value expressions.
-- Preconditions are /not/ checked.
sConcat :: [Expr String] -> Expr String
sConcat l =
    let n = (mergeVals . flatten . filter (sConst "" /= ) ) l in
        case Prelude.length n of
           0 -> sConst ""
           1 -> head n
           _ -> Expr (Concat $ fmap view n)

-- implementation details:
-- Properties incorporated
--    "" ++ x == x          - remove empty strings
--    "a" ++ "b" == "ab"    - concat consecutive string values
--   remove all nested sConcat, since (a ++ b) ++ (c ++ d) == (a ++ b ++ c ++ d)

mergeVals :: [Expr String] -> [Expr String]
mergeVals []            = []
mergeVals [x]           = [x]
mergeVals ( (view -> Const s1) : (view -> Const s2) : xs) =
                          mergeVals (sConst (s1 <> s2): xs)
mergeVals (x1:x2:xs)    = x1 : mergeVals (x2:xs)

flatten :: [Expr String] -> [Expr String]
flatten []                       = []
flatten ((view -> Concat l):xs) = fmap Expr l ++ flatten xs
flatten (x:xs)                   = x : flatten xs

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
insertIntoValuation v@(Variable _ BoolType) c = assignValue v (fromConst' c)
insertIntoValuation v@(Variable _ StringType) c = assignValue v (fromConst' c)

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
subst' ve (Sum s)                 = sSum $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT s
subst' ve (Product p)             = sProduct $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT p
subst' ve (Length vexp)           = sLength (subst' ve vexp)

subst' ve (GezInt v)                = sIsNonNegative (subst' ve v)
subst' ve (Equal _ vexp1 vexp2)    = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (And vexps)               = sAnd $ Set.map (subst' ve) vexps
subst' ve (Not vexp)                = sNot (subst' ve vexp)

subst' ve (Concat vexps)                = sConcat $ map (subst' ve) vexps
