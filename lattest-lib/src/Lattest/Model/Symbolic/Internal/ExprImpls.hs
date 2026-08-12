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
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE FlexibleInstances #-}
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
  -- ** String Operators to create Value Expressions
  -- *** Length operator
, sLength
  -- *** Concat operator
, sConcat
  -- ** Regular Expression Operators to create Value Expressions
  -- *** String in Regular Expression operator
--, cstrStrInRe
  -- ** Algebraic Data Type Operators to create Value Expressions
  -- *** Algebraic Data Type constructor operator
--, cstrCstr
  -- *** Algebraic Data Type IsConstructor function
--, cstrIsCstr
  -- *** Algebraic Data Type Accessor
--, cstrAccess

-- to be documented
--, cstrPredef
-- * Substitution of var by value
, VarModel
, VarModel'(..)
, Assignable
, assign
, varUnion
, mapVars
, mapVarExprs
, Valuation
, Valuation'
, valuationToVarModel
, toConstantsMap
, fromConstantsMap
, emptyValuation
, assignValues
, assignValue
, getVariables
, identityVarModel
, varsToGuard
, insertIntoValuation
, substConst
, subst
, substVarModel
, assignedExpr
, assignment
, noAssignment
, (=:)
, mapExpressionVars
)
where

import           Control.Arrow   (first)
import qualified Data.List       as List
import qualified Data.Map        as Map
import qualified Data.Set        as Set
--import           Text.Regex.TDFA

import qualified Lattest.Model.Symbolic.Internal.Boute as Boute
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX        as FMX
import           Lattest.Model.Symbolic.Internal.Product as Product
--import           Lattest.Model.Symbolic.Expr.RegexXSD2Posix
import           Lattest.Model.Symbolic.Internal.Sum as Sum
import           Lattest.Model.Symbolic.Internal.ExprDefs

-- | Create a function call.
-- Preconditions are /not/ checked.
{-cstrFunc :: (Variable v, Variable w) => Map.Map FuncId (FuncDef v) -> FuncId -> [Expr w] -> Expr w
cstrFunc fis fi arguments =
    case Map.lookup fi fis of
        Nothing ->
            -- When implementing the body of a recursive function, a function
            -- call is made while the implementation is not (yet) finished and
            -- available.
            Expr (Vfunc fi arguments)
        Just (FuncDef params body)->
            case view body of
                Vconst x -> cons x
                _        -> if all isConst arguments
                            then compSubst (Map.fromList (zip params arguments)) fis body
                            else Expr (Vfunc fi arguments)

-- | Apply ADT Constructor of constructor with CstrId and the provided arguments (the list of value expressions).
-- Preconditions are /not/ checked.
cstrCstr :: CstrId -> [Expr] -> Expr
cstrCstr c a = if all isConst a
                then cons (Ccstr c (map toConst a) )
                else Expr (Vcstr c a)
    where   toConst :: Expr -> Constant
            toConst (view -> Vconst v) = v
            toConst _                  = error "Impossible when all satisfy isConst"

-- | Is the provided value expression made by the ADT constructor with CstrId?
-- Preconditions are /not/ checked.
cstrIsCstr :: CstrId -> Expr -> Expr
cstrIsCstr c1 (view -> Vcstr c2 _)          = cons (Cbool (c1 == c2) )
cstrIsCstr c1 (view -> Vconst (Ccstr c2 _)) = cons (Cbool (c1 == c2) )
cstrIsCstr c e                              = Expr (Viscstr c e)

-- | Apply ADT Accessor of constructor with CstrId on field with given position on the provided value expression.
-- Preconditions are /not/ checked.
cstrAccess :: CstrId -> T.Text -> Int -> Expr -> Expr
cstrAccess c1 n1 p1 (view -> Vcstr c2 fields) =
    if c1 == c2 -- prevent crashes due to model errors
        then fields!!p1
        else error ("Error in model: Accessing field " ++ show n1 ++ " of constructor " ++ show c1 ++ " on instance from constructor " ++ show c2)
cstrAccess c1 n1 p1 (view -> Vconst (Ccstr c2 fields)) =
    if c1 == c2 -- prevent crashes due to model errors
        then cons (fields!!p1)
        else error ("Error in model: Accessing field " ++ show n1 ++ " of constructor " ++ show c1 ++ " on value from constructor " ++ show c2)
cstrAccess c n p e = Expr (Vaccess c n p e)
-}
-- | Is Expr a Constant/Value Expression?
--isConst :: Expr -> Bool
--isConst (view -> Vconst{}) = True
--isConst _                  = False

sConst :: ExprType t => t -> Expr' tag t
sConst = Expr . Const

sTrue :: Expr' tag Bool
sTrue = sConst True

sFalse :: Expr' tag Bool
sFalse = sConst False

class VarExpr t where
    sVar :: Variable' tag -> Expr' tag t

instance VarExpr Integer where
    sVar v@(Var' _ IntType _) = sVar' v
    sVar (Var' n t _) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected Integer, received " ++ show t

instance VarExpr Bool where
    sVar v@(Var' _ BoolType _) = sVar' v
    sVar (Var' n t _) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected Bool, received " ++ show t

instance VarExpr String where
    sVar v@(Var' _ StringType _) = sVar' v
    sVar (Var' n t _) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected String, received " ++ show t

instance VarExpr Double where
    sVar v@(Var' _ FloatType _) = sVar' v
    sVar (Var' n t _) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected Real, received " ++ show t

sVar' :: Variable' tag -> Expr' tag t
sVar' = Expr . EVar

-- | Apply operator ITE (IF THEN ELSE) on the provided value expressions.
-- Preconditions are /not/ checked.
sIfThenElse :: Expr' tag Bool -> Expr' tag t -> Expr' tag t -> Expr' tag t
sIfThenElse (view -> Const True) t _ = t
sIfThenElse (view -> Const False) _ f = f
sIfThenElse (view -> c) (view -> t) (view -> f) = Expr $ Ite c t f

-- | Create a variable as a value expression.
-- typeclass because every type has its own ExprView-constructor
class EqExpr t where
    (.==) :: Expr' tag t -> Expr' tag t -> Expr' tag Bool

instance EqExpr Integer where
    (.==) (view -> x) (view -> y) = Expr $ EqualInt x y

instance EqExpr Bool where
    (.==) (view -> x) (view -> y) = Expr $ EqualBool x y

instance EqExpr String where
    (.==) (view -> x) (view -> y) = Expr $ EqualString x y

instance EqExpr Double where
    (.==) (view -> x) (view -> y) = Expr $ EqualFloat x y

infix 4 .==

{-
-- | Apply operator Equal on the provided value expressions.
-- Preconditions are /not/ checked.
(.==) :: Expr' tag -> Expr' tag -> Expr
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
sNot :: Expr' tag Bool -> Expr' tag Bool
sNot (view -> Const b)      = sConst (not b) -- constant fold: ¬True ≡ False, ¬False ≡ True
sNot (view -> Not ve)       = Expr ve -- eliminate double negation: ¬¬e ≡ e
-- push the negation into the branches: ¬(if cs then tb else fb) ≡ if cs then ¬tb else ¬fb
sNot (view -> Ite cs tb fb) = Expr (Ite cs (view $ sNot (Expr tb)) (view $ sNot (Expr fb)))
sNot (view -> ve)           = Expr $ Not ve

-- | Apply operator And on the provided set of value expressions.
-- Preconditions are /not/ checked.
sAnd :: forall tag. Ord tag => Set.Set (Expr' tag Bool) -> Expr' tag Bool
--sAnd = sAnd' . flattenAnd
sAnd = mkAnd . flattenAnd
    where
        flattenAnd :: Set.Set (Expr' tag Bool) -> Set.Set (ExprView' tag Bool)
        flattenAnd = Set.unions . map fromExpr . Set.toList

        fromExpr :: Expr' tag Bool -> Set.Set (ExprView' tag Bool)
        fromExpr (view -> And a) = a
        fromExpr (view -> x) = Set.singleton x

        -- annihilation (x ∧ False ≡ False) and identity (x ∧ True ≡ x); a single conjunct needs no wrapping
        mkAnd :: Set.Set (ExprView' tag Bool) -> Expr' tag Bool
        mkAnd (absorb -> vs)
            | Set.member (Const False) vs = sFalse
            | hasComplements vs           = sFalse -- contradiction: x ∧ ¬x ≡ False
            | otherwise = case Set.toList vs' of
                []  -> sTrue
                [v] -> Expr v
                _   -> Expr (And vs')
            where vs' = Set.delete (Const True) vs

        -- absorption under negation: e ∧ ¬(e ∧ rest) ≡ e ∧ ¬rest. A conjunct that is
        -- already asserted at the top level of the conjunction is redundant inside a
        -- negated conjunction, so it can be dropped from it. If every conjunct of the
        -- negated cube is dropped this yields ¬True ≡ False, which the checks above catch.
        absorb :: Set.Set (ExprView' tag Bool) -> Set.Set (ExprView' tag Bool)
        absorb vs = Set.map simplify vs
            where
                simplify (Not (And s))
                    | not (Set.null (Set.intersection s vs)) = view $ sNot $ sAnd $ Set.map Expr $ s Set.\\ vs
                simplify v = v

        -- does the conjunction contain both some e and its negation ¬e?
        hasComplements :: Set.Set (ExprView' tag Bool) -> Bool
        hasComplements vs = any ((`Set.member` vs) . negated) (Set.toList vs)
            where
                negated (Not e) = e
                negated e       = Not e
{-
-- And doesn't contain elements of type Vand.
sAnd' :: Set.Set Expr' tag Bool -> Expr' tag Bool
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
        
        contains :: Set.Set Expr' tag -> Expr' tag -> Bool
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
isSum :: ExprView' tag Integer -> Bool
isSum (Sum _) = True
isSum _ = False

getSum :: ExprView' tag Integer -> FreeSum (ExprView' tag Integer)
getSum (Sum s) = s
getSum _ = error "ExprImpls.hs - getSum - Unexpected Expr "

sSumInt :: Ord tag => FreeSum (Expr' tag Integer) -> Expr' tag Integer
sSumInt = Expr . cstrSum . FMX.mapTerms (SumTerm . view . summand)

-- | Apply operator sum on the provided sum of value expressions.
-- Preconditions are /not/ checked.
cstrSum :: forall tag. Ord tag => FreeSum (ExprView' tag Integer) -> ExprView' tag Integer
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the sum of all values
--         special case if the sum is zero, no value is inserted since v == v+0
--    remove all nested sums, since (a+b) + (c+d) == (a+b+c+d)
cstrSum ms = cstrSum' $ nonadds <> FMX.flatten sumOfAdds
    where
      (adds, nonadds) = FMX.partitionT isSum ms
      sumOfAdds :: FMX.FreeMonoidX (FMX.FreeMonoidX (SumTerm (ExprView' tag Integer)))
      sumOfAdds = FMX.mapTerms (getSum . summand) adds

-- Sum doesn't contain elements of type VExprSum
cstrSum' :: Ord tag => FreeSum (ExprView' tag Integer) -> ExprView' tag Integer
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

getConst :: ExprView' tag e -> e
getConst (Const c) = c
getConst _ = error "Not Const"

isSumF :: ExprView' tag Double -> Bool
isSumF (SumFloat _) = True
isSumF _ = False

getSumF :: ExprView' tag Double -> FreeSum (ExprView' tag Double)
getSumF (SumFloat s) = s
getSumF _ = error "ExprImpls.hs - getSumF - Unexpected Expr "

sSumFloat :: Ord tag => FreeSum (Expr' tag Double) -> Expr' tag Double
sSumFloat = Expr . cstrSumF . FMX.mapTerms (SumTerm . view . summand)

-- | Apply operator sum on the provided sum of floating-point values.
cstrSumF :: Ord tag => FreeSum (ExprView' tag Double) -> ExprView' tag Double
cstrSumF ms = cstrSumF' $ nonadds <> FMX.flatten sumOfAdds
    where
      (adds, nonadds) = FMX.partitionT isSumF ms
      sumOfAdds = FMX.mapTerms (getSumF . summand) adds

cstrSumF' :: Ord tag => FreeSum (ExprView' tag Double) -> ExprView' tag Double
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
isProduct :: ExprView' tag Integer -> Bool
isProduct (Product _) = True
isProduct _ = False

getProduct :: ExprView' tag Integer -> FreeProduct (ExprView' tag Integer)
getProduct (Product p) = p
getProduct _ = error "ExprImpls.hs - getProduct - Unexpected Expr "

sProductInt :: Ord tag => FreeProduct (Expr' tag Integer) -> Expr' tag Integer
sProductInt = Expr . cstrPrd . FMX.mapTerms (ProductTerm . view . factor)

-- | Apply operator product on the provided product of value expressions.
-- Be aware that division is not associative for Integer, so only use power >= 0.
-- Preconditions are /not/ checked.
cstrPrd :: Ord tag => FreeProduct (ExprView' tag Integer) -> ExprView' tag Integer
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the product of all values
--         special case if the product is one, no value is inserted since v == v*1
--    remove all nested products, since (a*b) * (c*d) == (a*b*c*d)
cstrPrd ms =
    cstrPrd' $ noprods <> FMX.flatten prodOfProds
    where
      (prods, noprods) = FMX.partitionT isProduct ms
      prodOfProds = FMX.mapTerms (getProduct . factor) prods

-- Product doesn't contain elements of type VExprProduct
cstrPrd' :: Ord tag => FreeProduct (ExprView' tag Integer) -> ExprView' tag Integer
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
        isZero :: ExprView' tag Integer -> Bool
        isZero (Const 0) = True
        isZero _         = False

-- Product of floating-point values
isProductF :: ExprView' tag Double -> Bool
isProductF (ProductFloat _) = True
isProductF _ = False

getProductF :: ExprView' tag Double -> FreeProduct (ExprView' tag Double)
getProductF (ProductFloat p) = p
getProductF _ = error "ExprImpls.hs - getProductF - Unexpected Expr "

sProductFloat :: Ord tag => FreeProduct (Expr' tag Double) -> Expr' tag Double
sProductFloat = Expr . cstrPrdF . FMX.mapTerms (ProductTerm . view . factor)

-- | Apply operator product on the provided product of floating-point values.
cstrPrdF :: Ord tag => FreeProduct (ExprView' tag Double) -> ExprView' tag Double
cstrPrdF ms =
    cstrPrdF' $ noprods <> FMX.flatten prodOfProds
    where
      (prods, noprods) = FMX.partitionT isProductF ms
      prodOfProds = FMX.mapTerms (getProductF . factor) prods

-- Product doesn't contain elements of type ProductFloat
cstrPrdF' :: Ord tag => FreeProduct (ExprView' tag Double) -> ExprView' tag Double
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
        isZeroF (Const 0.0) = True
        isZeroF _           = False

-- Divide

-- | Apply operator Divide on the provided integer value expressions.
-- Preconditions are /not/ checked.
divideInt :: Expr' tag Integer -> Expr' tag Integer -> Expr' tag Integer
divideInt (view ->  Const t) (view -> Const n) | n /= 0 = sConst (t `Boute.div` n) -- leave error case (division by zero) unevaluated
divideInt (view -> vet)         (view -> ven) = Expr (Divide vet ven)

-- | Apply operator Divide on the provided floating-point value expressions.
-- Preconditions are /not/ checked.
divideFloat :: Expr' tag Double -> Expr' tag Double -> Expr' tag Double
divideFloat (view ->  Const t) (view -> Const n) | n /= 0 = sConst (t / n) -- leave error case (division by zero) unevaluated
divideFloat (view -> vet)         (view -> ven) = Expr (DivideFloat vet ven)

-- Modulo

-- | Apply operator Modulo on the provided value expressions.
-- Preconditions are /not/ checked.
(.%) :: Expr' tag Integer -> Expr' tag Integer -> Expr' tag Integer
(.%) (view -> Const t) (view -> Const n) | n /= 0 = sConst (t `Boute.mod` n) -- leave error case (division by zero) unevaluated
(.%) (view -> vet)        (view -> ven) = Expr (Modulo vet ven)

infixl 7 .%

-- | Apply operator GEZ (Greater Equal Zero) on the provided integer value expression.
-- Preconditions are /not/ checked.
sIsNonNegativeInt :: Expr' tag Integer -> Expr' tag Bool
-- Simplification Values
sIsNonNegativeInt (view -> Const v) = sConst (0 <= v)
sIsNonNegativeInt (view -> Length _)   = sConst True        -- length of string is always Greater or equal to zero
sIsNonNegativeInt (view -> ve)         = Expr (GezInt ve)

-- | Apply operator GEZ (Greater Equal Zero) on the provided floating-point value expression.
-- Preconditions are /not/ checked.
sIsNonNegativeFloat :: Expr' tag Double -> Expr' tag Bool
sIsNonNegativeFloat (view -> Const v) = sConst (0 <= v)
sIsNonNegativeFloat (view -> ve)      = Expr (GezFloat ve)

class Ord t => ExprNum t where
    sSum :: Ord tag => FreeSum (Expr' tag t) -> Expr' tag t
    sProduct :: Ord tag => FreeProduct (Expr' tag t) -> Expr' tag t
    sIsNonNegative :: Ord tag => Expr' tag t -> Expr' tag Bool
    (./) :: Ord tag => Expr' tag t -> Expr' tag t -> Expr' tag t

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

-- | Apply operator Length on the provided value expression.
-- Preconditions are /not/ checked.
sLength :: Expr' tag String -> Expr' tag Integer
sLength (view -> Const s) = sConst (Prelude.toInteger (length s))
sLength (view -> v)             = Expr (Length v)

-- | Apply operator Concat on the provided sequence of value expressions.
-- Preconditions are /not/ checked.
sConcat :: Eq tag => [Expr' tag String] -> Expr' tag String
sConcat l =
    let n = (mergeVals . flatten . filter (sConst "" /= ) ) l in
        case n of
          [] -> sConst ""
          [x] -> x
          _ -> Expr (Concat $ fmap view n)

-- implementation details:
-- Properties incorporated
--    "" ++ x == x          - remove empty strings
--    "a" ++ "b" == "ab"    - concat consecutive string values
--   remove all nested sConcat, since (a ++ b) ++ (c ++ d) == (a ++ b ++ c ++ d)

mergeVals :: [Expr' tag String] -> [Expr' tag String]
mergeVals []            = []
mergeVals [x]           = [x]
mergeVals ( (view -> Const s1) : (view -> Const s2) : xs) =
                          mergeVals (sConst (s1 <> s2): xs)
mergeVals (x1:x2:xs)    = x1 : mergeVals (x2:xs)

flatten :: [Expr' tag String] -> [Expr' tag String]
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

-- See Note [Tags on Variables, Expressions, etc]
type TypedValuation tag t = Map.Map (Variable' tag) t
data Valuation' tag = Valuation {
    intValuation :: TypedValuation tag Integer,
    boolValuation :: TypedValuation tag Bool,
    stringValuation :: TypedValuation tag String,
    floatValuation :: TypedValuation tag Double
    }
    deriving (Eq, Ord)
type Valuation = Valuation' ()

instance Show Valuation where
    show (Valuation i b s f) = "{" ++ List.intercalate "," (printAsAssignments i ++ printAsAssignments b ++ printAsAssignments s ++ printAsAssignments f) ++ "}"
        where
        printAsAssignments :: Show t => Map.Map Variable t -> [String]
        printAsAssignments m = printAsAssignment <$> Map.toList m
        printAsAssignment (v,t) = varName v ++ ":=" ++ show t

toConstantsMap :: Ord tag => Valuation' tag -> Map.Map (Variable' tag) Constant
toConstantsMap valuation = Map.map Cint (intValuation valuation)
                            `Map.union` Map.map Cbool (boolValuation valuation)
                            `Map.union` Map.map Cstring (stringValuation valuation)
                            `Map.union` Map.map Cfloat (floatValuation valuation)

fromConstantsMap :: Ord tag => Map.Map (Variable' tag) Constant -> Valuation' tag
fromConstantsMap = assignValues . fmap (uncurry insertIntoValuation) . Map.toList

assignValues :: Ord tag => [Valuation' tag -> Valuation' tag] -> Valuation' tag
assignValues = foldr ($) emptyValuation

emptyValuation :: Ord tag => Valuation' tag
emptyValuation = Valuation Map.empty Map.empty Map.empty Map.empty

-- See Note [Tags on Variables, Expressions, etc]
type TypedVarModel tag t = Map.Map (Variable' tag) (Expr' tag t)
data VarModel' tag = VarModel {
    intVars :: TypedVarModel tag Integer,
    boolVars :: TypedVarModel tag Bool,
    stringVars :: TypedVarModel tag String,
    floatVars :: TypedVarModel tag Double
    }
    deriving (Eq, Ord)
type VarModel = VarModel' ()

assignment :: Ord tag => [VarModel' tag -> VarModel' tag] -> VarModel' tag
assignment = foldr ($) noAssignment

typedValuationToVarModel :: ExprType t => TypedValuation tag t -> TypedVarModel tag t
typedValuationToVarModel = Map.map sConst

valuationToVarModel :: Valuation' tag -> VarModel' tag
valuationToVarModel vals = VarModel {
    intVars = typedValuationToVarModel $ intValuation vals,
    boolVars = typedValuationToVarModel $ boolValuation vals,
    stringVars = typedValuationToVarModel $ stringValuation vals,
    floatVars = typedValuationToVarModel $ floatValuation vals
    }

getVariables :: Valuation' tag -> [Variable' tag]
getVariables vals =
    Map.keys (intValuation vals) ++
    Map.keys (boolValuation vals) ++
    Map.keys (stringValuation vals) ++
    Map.keys (floatValuation vals)

assignIdentity :: Variable -> VarModel -> VarModel
assignIdentity v@(Var _ IntType) = assign v (sVar v :: Expr Integer)
assignIdentity v@(Var _ BoolType) = assign v (sVar v :: Expr Bool)
assignIdentity v@(Var _ StringType) = assign v (sVar v :: Expr String)
assignIdentity v@(Var _ FloatType) = assign v (sVar v :: Expr Double)

identityVarModel :: [Variable] -> VarModel
identityVarModel vars = assignment $ assignIdentity <$> vars

varUnion :: VarModel -> VarModel -> VarModel
varUnion vars1 vars2 = VarModel {
    intVars = intVars vars1 `Map.union` intVars vars2,
    boolVars = boolVars vars1 `Map.union` boolVars vars2,
    stringVars = stringVars vars1 `Map.union` stringVars vars2,
    floatVars = floatVars vars1 `Map.union` floatVars vars2
    }

mapVars :: (Variable -> Variable) -> VarModel -> VarModel
mapVars f vars = VarModel {
    intVars = Map.mapKeys f $ intVars vars,
    boolVars = Map.mapKeys f $ boolVars vars,
    stringVars = Map.mapKeys f $ stringVars vars,
    floatVars = Map.mapKeys f $ floatVars vars
    }

mapVarExprs :: (Variable -> Variable) -> VarModel -> VarModel
mapVarExprs f vars = VarModel {
    intVars = Map.map (mapExpressionVars f) $ intVars vars,
    boolVars = Map.map (mapExpressionVars f) $ boolVars vars,
    stringVars = Map.map (mapExpressionVars f) $ stringVars vars,
    floatVars = Map.map (mapExpressionVars f) $ floatVars vars
    }

varsToGuard :: Ord tag => VarModel' tag -> Expr' tag Bool
varsToGuard vars = sAnd $ Set.fromList $
    typedVarsToBools (intVars vars) ++
    typedVarsToBools (boolVars vars) ++
    typedVarsToBools (stringVars vars) ++
    typedVarsToBools (floatVars vars)

typedVarsToBools :: (VarExpr t, EqExpr t) => TypedVarModel tag t -> [Expr' tag Bool]
typedVarsToBools = fmap (\(var, val) -> sVar var .== val) . Map.toList

insertIntoValuation :: Ord tag => Variable' tag -> Constant -> Valuation' tag -> Valuation' tag
insertIntoValuation v@(Var' name IntType tag) c = assignValue v (fromConst' c name IntType :: Integer)
insertIntoValuation v@(Var' name BoolType tag) c = assignValue v (fromConst' c name BoolType :: Bool)
insertIntoValuation v@(Var' name StringType tag) c = assignValue v (fromConst' c name StringType :: String)
insertIntoValuation v@(Var' name FloatType tag) c = assignValue v (fromConst' c name FloatType :: Double)
fromConst' :: (ConstType a, Show b) => Constant -> String -> b -> a
fromConst' smtValue name t = case fromConst smtValue of
    Left err -> error $ "error reading " ++ name ++ " as " ++ show t ++ ": " ++ err
    Right val -> val

class Assignable t where
    assign :: Ord tag => Variable' tag -> Expr' tag t -> VarModel' tag -> VarModel' tag
    assignValue :: Ord tag => Variable' tag -> t -> Valuation' tag -> Valuation' tag
    assignedExpr :: Ord tag => Variable' tag -> VarModel' tag -> Maybe (Expr' tag t)
    assignedExprWithDefault :: Ord tag => Variable' tag -> VarModel' tag -> Expr' tag t

(=:) :: (Assignable t, Ord tag) => Variable' tag -> Expr' tag t -> VarModel' tag -> VarModel' tag
(=:) = assign
infixr 0 =:

instance Assignable Integer where
    assign v@(Var' _ IntType _) e m = m {intVars = Map.insert v e (intVars m)}
    assign (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Integer, received " ++ show t
    assignValue v@(Var' _ IntType _) val m = m {intValuation = Map.insert v val (intValuation m)}
    assignValue (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Integer, received " ++ show t
    assignedExpr v@(Var' _ IntType _) (VarModel ints _bools _strings _floats) = Map.lookup v ints
    assignedExpr (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Integer"
    assignedExprWithDefault v@(Var' _ IntType _) (VarModel ints _bools _strings _floats) = Map.findWithDefault (sVar v) v ints
    assignedExprWithDefault (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Integer"

instance Assignable Bool where
    assign v@(Var' _ BoolType _) e m = m {boolVars = Map.insert v e (boolVars m)}
    assign (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Bool, received " ++ show t
    assignValue v@(Var' _ BoolType _) val m = m {boolValuation = Map.insert v val (boolValuation m)}
    assignValue (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Bool, received " ++ show t
    assignedExpr v@(Var' _ BoolType _) (VarModel _ints bools _strings _floats) = Map.lookup v bools
    assignedExpr (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Bool"
    assignedExprWithDefault v@(Var' _ BoolType _) (VarModel _ints bools _strings _floats) = Map.findWithDefault (sVar v) v bools
    assignedExprWithDefault (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Bool"

instance Assignable String where
    assign v@(Var' _ StringType _) e m = m {stringVars = Map.insert v e (stringVars m)}
    assign (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected String, received " ++ show t
    assignValue v@(Var' _ StringType _) val m = m {stringValuation = Map.insert v val (stringValuation m)}
    assignValue (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected String, received " ++ show t
    assignedExpr v@(Var' _ StringType _) (VarModel _ints _bools strings _floats) = Map.lookup v strings
    assignedExpr (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received String"
    assignedExprWithDefault v@(Var' _ StringType _) (VarModel _ints _bools strings _floats) = Map.findWithDefault (sVar v) v strings
    assignedExprWithDefault (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received String"

instance Assignable Double where
    assign v@(Var' _ FloatType _) e m = m {floatVars = Map.insert v e (floatVars m)}
    assign (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Real, received " ++ show t
    assignValue v@(Var' _ FloatType _) val m = m {floatValuation = Map.insert v val (floatValuation m)}
    assignValue (Var' n t _) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Real, received " ++ show t
    assignedExpr v@(Var' _ FloatType _) (VarModel _ints _bools _strings floats) = Map.lookup v floats
    assignedExpr (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Real"
    assignedExprWithDefault v@(Var' _ FloatType _) (VarModel _ints _bools _strings floats) = Map.findWithDefault (sVar v) v floats
    assignedExprWithDefault (Var' n t _) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Real"

noAssignment :: Ord tag => VarModel' tag
noAssignment = VarModel Map.empty Map.empty Map.empty Map.empty

instance Show VarModel where
    show (VarModel ints bools strings floats) = showMapList $ showList' ints ++ showList' bools ++ showList' strings ++ showList' floats
        where
        showMapList m' = "{" ++ List.intercalate ", " m' ++ "}"
        showList' m' = showAssign <$> Map.toList m'
        showAssign (v,e) = varName v ++ ":=" ++ show e

substConst :: (Ord tag, Assignable t) => Valuation' tag -> Expr' tag t -> Expr' tag t
substConst valuation = subst (valuationToVarModel valuation)

-- | Apply a substitution to the right-hand-side expressions of a 'VarModel', leaving its keys untouched.
-- Composing substitutions this way lets an assignment be resolved against an accumulated substitution:
-- @substVarModel sigma assign@ rewrites every value-expression in @assign@ according to @sigma@.
substVarModel :: Ord tag => VarModel' tag -> VarModel' tag -> VarModel' tag
substVarModel sigma (VarModel ints bools strings floats) = VarModel {
    intVars = Map.map (subst sigma) ints,
    boolVars = Map.map (subst sigma) bools,
    stringVars = Map.map (subst sigma) strings,
    floatVars = Map.map (subst sigma) floats
    }

-- | Substitute variables by value expressions in a value expression.
--
-- Preconditions are /not/ checked.
--
subst :: (Ord tag, Assignable t) => VarModel' tag -- ^ Map from variables to value expressions.
      -> Expr' tag t                   -- ^ Value expression where the
                                       -- substitution will take place.
      -> Expr' tag t
--subst ve _ x   | ve == Map.empty = x
subst ve x = subst' ve (view x)

subst' :: (Ord tag, Assignable t) => VarModel' tag -> ExprView' tag t -> Expr' tag t
subst' _  (Const const')          = sConst const'
subst' ve (EVar vid)              = assignedExprWithDefault vid ve
subst' ve (Ite cond vexp1 vexp2)  = sIfThenElse (subst' ve cond) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (Divide t n)            = (./) (subst' ve t) (subst' ve n)
subst' ve (Modulo t n)            = (.%) (subst' ve t) (subst' ve n)
subst' ve (DivideFloat t n)       = (./) (subst' ve t) (subst' ve n)
subst' ve (Sum s)                 = sSum $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT s
subst' ve (SumFloat s)            = sSum $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT s
subst' ve (Product p)             = sProduct $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT p
subst' ve (ProductFloat p)        = sProduct $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT p
subst' ve (Length vexp)           = sLength (subst' ve vexp)

subst' ve (GezInt v)                = sIsNonNegative (subst' ve v)
subst' ve (GezFloat v)              = sIsNonNegative (subst' ve v)
subst' ve (EqualInt vexp1 vexp2)    = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (EqualBool vexp1 vexp2)   = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (EqualString vexp1 vexp2) = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (EqualFloat vexp1 vexp2)  = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (And vexps)               = sAnd $ Set.map (subst' ve) vexps
subst' ve (Not vexp)                = sNot (subst' ve vexp)

subst' ve (Concat vexps)                = sConcat $ map (subst' ve) vexps

mapExpressionVars :: Ord tag2 => (Variable' tag1 -> Variable' tag2) -> Expr' tag1 t -> Expr' tag2 t
mapExpressionVars f = Expr . mapExpressionVars' f . view

mapExpressionVars' :: Ord tag2 => (Variable' tag1 -> Variable' tag2) -> ExprView' tag1 t -> ExprView' tag2 t
mapExpressionVars' _ (Const e) = Const e
mapExpressionVars' f (EVar v) = EVar $ f v -- this line is effectively the purpose of this function
mapExpressionVars' f (Ite cond vexp1 vexp2)  = Ite (mapExpressionVars' f cond) (mapExpressionVars' f vexp1) (mapExpressionVars' f vexp2)
mapExpressionVars' f (Divide t n)            = Divide (mapExpressionVars' f t) (mapExpressionVars' f n)
mapExpressionVars' f (Modulo t n)            = Modulo (mapExpressionVars' f t) (mapExpressionVars' f n)
mapExpressionVars' f (DivideFloat t n)       = DivideFloat (mapExpressionVars' f t) (mapExpressionVars' f n)
mapExpressionVars' f (Sum s)                 = Sum (FMX.mapTerms (SumTerm . mapExpressionVars' f . summand) s)
mapExpressionVars' f (SumFloat s)            = SumFloat (FMX.mapTerms (SumTerm . mapExpressionVars' f . summand) s)
mapExpressionVars' f (Product p)             = Product (FMX.mapTerms (ProductTerm . mapExpressionVars' f . factor) p)
mapExpressionVars' f (ProductFloat p)        = ProductFloat (FMX.mapTerms (ProductTerm . mapExpressionVars' f . factor) p)
mapExpressionVars' f (Length vexp)           = Length (mapExpressionVars' f vexp)

mapExpressionVars' f (GezInt v)                = GezInt (mapExpressionVars' f v)
mapExpressionVars' f (GezFloat v)              = GezFloat (mapExpressionVars' f v)
mapExpressionVars' f (EqualInt vexp1 vexp2)    = EqualInt (mapExpressionVars' f vexp1) (mapExpressionVars' f vexp2)
mapExpressionVars' f (EqualBool vexp1 vexp2)   = EqualBool (mapExpressionVars' f vexp1) (mapExpressionVars' f vexp2)
mapExpressionVars' f (EqualString vexp1 vexp2) = EqualString (mapExpressionVars' f vexp1) (mapExpressionVars' f vexp2)
mapExpressionVars' f (EqualFloat vexp1 vexp2)  = EqualFloat (mapExpressionVars' f vexp1) (mapExpressionVars' f vexp2)
mapExpressionVars' f (And vexps)               = And (Set.map (mapExpressionVars' f) vexps)
mapExpressionVars' f (Not vexp)                = Not (mapExpressionVars' f vexp)

mapExpressionVars' f (Concat vexps)            = Concat (fmap (mapExpressionVars' f) vexps)
