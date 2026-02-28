{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ValExprImpls
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Implementation file for Value Expressions.
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE FlexibleInstances #-}
module Lattest.Model.Symbolic.ValExpr.ValExprImpls
( -- * Constructors to create Value Expressions
  -- ** Constant value
  cons
  -- ** VarRef
, var
  -- ** General Operators to create Value Expressions
  -- *** Equal
, (.==)
  -- *** If Then Else
, ifThenElse
  -- *** Function Call
--, cstrFunc
  -- ** Boolean Operators to create Value Expressions
  -- *** Not
, neg
  -- *** And
, (.&&)
  -- ** Integer Operators to create Value Expressions
  -- *** Sum
, (.+)
  -- *** Product
, (.*)
  -- *** Divide
, (./)
  -- *** Modulo
, cstrModulo
  -- *** Comparisons GEZ
, cstrGEZ
  -- ** String Operators to create Value Expressions
  -- *** Length operator
, cstrLength
  -- *** At operator
, cstrAt
  -- *** Concat operator
, cstrConcat
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
, assign
, Valuation
, emptyValuation
, assignValues
, assignValue
, evalConst
, evalConst'
, subst
, assignedExpr
, assignment
, noAssignment
, (=:)
)
where

import           Control.Arrow   (first)
import           Control.Exception ( assert )
import qualified Data.List       as List
import qualified Data.Map        as Map
import           Data.Maybe      (fromMaybe)
import qualified Data.Set        as Set
import qualified Data.Text       as T
--import           Text.Regex.TDFA

import qualified Lattest.Model.Symbolic.ValExpr.Boute as Boute
import qualified Lattest.Model.Symbolic.ValExpr.FreeMonoidX        as FMX
import           Lattest.Model.Symbolic.ValExpr.Product as Product
--import           Lattest.Model.Symbolic.ValExpr.RegexXSD2Posix
import           Lattest.Model.Symbolic.ValExpr.Sum as Sum
import           Lattest.Model.Symbolic.ValExpr.ValExprDefs

-- | Create a function call.
-- Preconditions are /not/ checked.
{-cstrFunc :: (Variable v, Variable w) => Map.Map FuncId (FuncDef v) -> FuncId -> [ValExpr w] -> ValExpr w
cstrFunc fis fi arguments =
    case Map.lookup fi fis of
        Nothing ->
            -- When implementing the body of a recursive function, a function
            -- call is made while the implementation is not (yet) finished and
            -- available.
            ValExpr (Vfunc fi arguments)
        Just (FuncDef params body)->
            case view body of
                Vconst x -> cons x
                _        -> if all isConst arguments
                            then compSubst (Map.fromList (zip params arguments)) fis body
                            else ValExpr (Vfunc fi arguments)

-- | Apply ADT Constructor of constructor with CstrId and the provided arguments (the list of value expressions).
-- Preconditions are /not/ checked.
cstrCstr :: CstrId -> [ValExpr] -> ValExpr
cstrCstr c a = if all isConst a
                then cons (Ccstr c (map toConst a) )
                else ValExpr (Vcstr c a)
    where   toConst :: ValExpr -> Constant
            toConst (view -> Vconst v) = v
            toConst _                  = error "Impossible when all satisfy isConst"

-- | Is the provided value expression made by the ADT constructor with CstrId?
-- Preconditions are /not/ checked.
cstrIsCstr :: CstrId -> ValExpr -> ValExpr
cstrIsCstr c1 (view -> Vcstr c2 _)          = cons (Cbool (c1 == c2) )
cstrIsCstr c1 (view -> Vconst (Ccstr c2 _)) = cons (Cbool (c1 == c2) )
cstrIsCstr c e                              = ValExpr (Viscstr c e)

-- | Apply ADT Accessor of constructor with CstrId on field with given position on the provided value expression.
-- Preconditions are /not/ checked.
cstrAccess :: CstrId -> T.Text -> Int -> ValExpr -> ValExpr
cstrAccess c1 n1 p1 (view -> Vcstr c2 fields) =
    if c1 == c2 -- prevent crashes due to model errors
        then fields!!p1
        else error ("Error in model: Accessing field " ++ show n1 ++ " of constructor " ++ show c1 ++ " on instance from constructor " ++ show c2)
cstrAccess c1 n1 p1 (view -> Vconst (Ccstr c2 fields)) =
    if c1 == c2 -- prevent crashes due to model errors
        then cons (fields!!p1)
        else error ("Error in model: Accessing field " ++ show n1 ++ " of constructor " ++ show c1 ++ " on value from constructor " ++ show c2)
cstrAccess c n p e = ValExpr (Vaccess c n p e)
-}
-- | Is ValExpr a Constant/Value Expression?
--isConst :: ValExpr -> Bool
--isConst (view -> Vconst{}) = True
--isConst _                  = False

cons :: ExprType t => t -> Expr t
cons = Expr . Const

class VarExpr t where
    var :: Variable -> Expr t

instance VarExpr Integer where
    var v@(Variable _ IntType) = var' v
    var (Variable n t) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected Integer, received " ++ show t

instance VarExpr Bool where
    var v@(Variable _ BoolType) = var' v
    var (Variable n t) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected Bool, received " ++ show t

instance VarExpr String where
    var v@(Variable _ StringType) = var' v
    var (Variable n t) = error $ "Variable expression for '" ++ n ++ "' of wrong type: expected String, received " ++ show t

var' :: Variable -> Expr t
var' = Expr . Var

-- | Apply operator ITE (IF THEN ELSE) on the provided value expressions.
-- Preconditions are /not/ checked.
ifThenElse :: Expr Bool -> Expr t -> Expr t -> Expr t
ifThenElse (view -> Const True) t _ = t
ifThenElse (view -> Const False) _ f = f
ifThenElse (view -> c) (view -> t) (view -> f) = Expr $ Ite c t f

-- | Create a variable as a value expression.
-- typeclass because every type has its own ExprView-constructor
class EqExpr t where
    (.==) :: Expr t -> Expr t -> Expr Bool
    
instance EqExpr Integer where
    (.==) (view -> x) (view -> y) = Expr $ EqualInt x y

instance EqExpr Bool where
    (.==) (view -> x) (view -> y) = Expr $ EqualBool x y

instance EqExpr String where
    (.==) (view -> x) (view -> y) = Expr $ EqualString x y



{-
-- | Apply operator Equal on the provided value expressions.
-- Preconditions are /not/ checked.
(.==) :: Expr -> Expr -> Expr
-- Simplification a == a <==> True
(.==) ve1 ve2 | ve1 == ve2                      = cons (Cbool True)
-- Simplification Different Values <==> False : use Same Values are already detected in previous step
(.==) (view -> Vconst _) (view -> Vconst _)     = cons (Cbool False)
-- Simplification True == e <==> e (twice)
(.==) (view -> Vconst (Cbool True)) e           = e
(.==) e (view -> Vconst (Cbool True))           = e

-- Simplification False == e <==> not e (twice)
(.==) (view -> Vconst (Cbool False)) e              = neg e
(.==) e (view -> Vconst (Cbool False))              = neg e
-- Not x == x <==> false (twice)
(.==) e (view -> Vnot n) | e == n                   = cons (Cbool False)
(.==) (view -> Vnot n) e | e == n                   = cons (Cbool False)
-- Not x == Not y <==> x == y   -- same representation
(.==) (view -> Vnot n1) (view -> Vnot n2)     = (.==) n1 n2
-- Not a == b <==> a == Not b -- same representation (twice)
(.==) x@(view -> Vnot n) e                = if n <= e
                                                        then Expr (Vequal x e)
                                                        else Expr (Vequal (neg e) n)
(.==) e x@(view -> Vnot n)                = if n <= e
                                                        then Expr (Vequal x e)
                                                        else Expr (Vequal (neg e) n)
-- a == b <==> b == a -- same representation
(.==) ve1 ve2                                   = if ve1 <= ve2
                                                        then Expr (Vequal ve1 ve2)
                                                        else Expr (Vequal ve2 ve1)
-}

-- | Apply operator Not on the provided value expression.
-- Preconditions are /not/ checked.
neg :: Expr Bool -> Expr Bool
{-neg (view -> Vconst (Cbool True))       = cons (Cbool False)
neg (view -> Vconst (Cbool False))      = cons (Cbool True)
neg (view -> Vnot ve)                   = ve
-- not (if cs then tb else fb) == if cs then not (tb) else not (fb)
neg (view -> Vite cs tb fb)             = Expr (Vite cs (neg tb) (neg fb))-}
neg (view -> ve) = Expr $ Not ve

-- | Apply operator And on the provided set of value expressions.
-- Preconditions are /not/ checked.
(.&&) :: Set.Set (Expr Bool) -> Expr Bool
--(.&&) = (.&&)' . flattenAnd
(.&&) = Expr . And . flattenAnd
    where
        flattenAnd :: Set.Set (Expr Bool) -> Set.Set (ExprView Bool)
        flattenAnd = Set.unions . map fromExpr . Set.toList
        
        fromExpr :: Expr Bool -> Set.Set (ExprView Bool)
        fromExpr (view -> And a) = a
        fromExpr (view -> x) = Set.singleton x
{-
-- And doesn't contain elements of type Vand.
(.&&)' :: Set.Set Expr Bool -> Expr Bool
(.&&)' s =
    if Set.member (cons (Cbool False)) s
        then cons (Cbool False)
        else let s' = Set.delete (cons (Cbool True)) s in
                case Set.size s' of
                    0   -> cons (Cbool True)
                    1   -> head (Set.toList s')
                    _   ->  -- not(x) and x == False
                            let nots = filterNot (Set.toList s') in
                                if any (contains s') nots
                                    then cons (Cbool False)
--                                    else let ts = isCstrTuples (Set.toList s') in
--                                            if sameExpr ts
--                                                then cons (Cbool False)
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

(.+) :: FreeSum (Expr Integer) -> Expr Integer
(.+) = Expr . cstrSum . FMX.mapTerms (SumTerm . view . summand)

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

(.*) :: FreeProduct (Expr Integer) -> Expr Integer
(.*) = Expr . cstrPrd . FMX.mapTerms (ProductTerm . view . factor)

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
(./) _                     (view -> Const n) | n == 0 = error "Error in model: Division by Zero in Divide"
(./) (view ->  Const t) (view -> Const n) = cons (t `Boute.div` n)
(./) (view -> vet)         (view -> ven) = Expr (Divide vet ven)

-- Modulo

-- | Apply operator Modulo on the provided value expressions.
-- Preconditions are /not/ checked.
cstrModulo :: Expr Integer -> Expr Integer -> Expr Integer
cstrModulo _                    (view -> Const n) | n == 0 = error "Error in model: Division by Zero in Modulo"
cstrModulo (view -> Const t) (view -> Const n) = cons (t `Boute.mod` n)
cstrModulo (view -> vet)        (view -> ven) = Expr (Modulo vet ven)

-- | Apply operator GEZ (Greater Equal Zero) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGEZ :: Expr Integer -> Expr Bool
-- Simplification Values
cstrGEZ (view -> Const v) = cons (0 <= v)
cstrGEZ (view -> Length _)   = cons True        -- length of string is always Greater or equal to zero
cstrGEZ (view -> ve)         = Expr (GezInt ve)


-- | Apply operator Length on the provided value expression.
-- Preconditions are /not/ checked.
cstrLength :: Expr String -> Expr Integer
cstrLength (view -> Const s) = cons (Prelude.toInteger (length s))
cstrLength (view -> v)             = Expr (Length v)

-- | Apply operator At on the provided value expressions.
-- Preconditions are /not/ checked.
cstrAt :: Expr String -> Expr Integer -> Expr String
cstrAt (view -> Const s) (view -> Const i) =
    if i < 0 || i >= Prelude.toInteger (length s)
        then error ("Error in model: Accessing string " ++ show s ++ " of length " ++ show (length s) ++ " with illegal index "++ show i) 
        else cons (take 1 (drop (fromInteger i) s))
cstrAt (view -> ves) (view -> vei) = Expr $ At ves vei

-- | Apply operator Concat on the provided sequence of value expressions.
-- Preconditions are /not/ checked.
cstrConcat :: [Expr String] -> Expr String
cstrConcat l =
    let n = (mergeVals . flatten . filter (cons "" /= ) ) l in
        case Prelude.length n of
           0 -> cons ""
           1 -> head n
           _ -> Expr (Concat $ fmap view n)

-- implementation details:
-- Properties incorporated
--    "" ++ x == x          - remove empty strings
--    "a" ++ "b" == "ab"    - concat consecutive string values
--   remove all nested Concats, since (a ++ b) ++ (c ++ d) == (a ++ b ++ c ++ d)

mergeVals :: [Expr String] -> [Expr String]
mergeVals []            = []
mergeVals [x]           = [x]
mergeVals ( (view -> Const s1) : (view -> Const s2) : xs) =
                          mergeVals (cons (s1 <> s2): xs)
mergeVals (x1:x2:xs)    = x1 : mergeVals (x2:xs)

flatten :: [Expr String] -> [Expr String]
flatten []                       = []
flatten ((view -> Concat l):xs) = fmap Expr l ++ flatten xs
flatten (x:xs)                   = x : flatten xs

-- | Apply String In Regular Expression operator on the provided value expressions.
-- Preconditions are /not/ checked.
--cstrStrInRe :: Expr -> Expr -> Expr
--cstrStrInRe (view -> Vconst (Cstring s)) (view -> Vconst (Cregex r)) = cons (Cbool (T.unpack s =~ T.unpack (xsd2posix r) ) )
--cstrStrInRe s r                                                      = Expr (Vstrinre s r)

{-
-- | Create a call to a predefined function as a value expression.
cstrPredef :: PredefKind -> FuncId -> [Expr] -> Expr
cstrPredef p f a = Expr (Vpredef p f a)
-}

type TypedValuation t = Map.Map Variable t
data Valuation = Valuation {
    intValuation :: TypedValuation Integer,
    boolValuation :: TypedValuation Bool,
    stringValuation :: TypedValuation String
    }
    deriving (Eq, Ord)

assignValues :: [Valuation -> Valuation] -> Valuation
assignValues fs = foldr ($) emptyValuation fs

emptyValuation :: Valuation
emptyValuation = Valuation Map.empty Map.empty Map.empty

type TypedVarModel t = Map.Map Variable (Expr t)
data VarModel = VarModel {
    intVars :: TypedVarModel Integer,
    boolVars :: TypedVarModel Bool,
    stringVars :: TypedVarModel String
    }
    deriving (Eq, Ord)

assignment :: [VarModel -> VarModel] -> VarModel
assignment fs = foldr ($) noAssignment fs

typedValuationToVarModel :: ExprType t => TypedValuation t -> TypedVarModel t
typedValuationToVarModel vals = Map.map cons vals

valuationToVarModel :: Valuation -> VarModel
valuationToVarModel vals = VarModel {
    intVars = typedValuationToVarModel $ intValuation vals,
    boolVars = typedValuationToVarModel $ boolValuation vals,
    stringVars = typedValuationToVarModel $ stringValuation vals
    }

class Assignable t where
    assign :: Variable -> Expr t -> VarModel -> VarModel
    assignValue :: Variable -> t -> Valuation -> Valuation
    assignedExpr :: Variable -> VarModel -> Maybe (Expr t)
    assignedExprWithDefault :: Variable -> VarModel -> Expr t

(=:) :: Assignable t => Variable -> Expr t -> VarModel -> VarModel
(=:) = assign
infixr 0 =:

instance Assignable Integer where
    assign v@(Variable _ IntType) e m = m {intVars = Map.insert v e (intVars m)}
    assign (Variable n t) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Integer, received " ++ show t
    assignValue v@(Variable _ IntType) val m = m {intValuation = Map.insert v val (intValuation m)}
    assignValue (Variable n t) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Integer, received " ++ show t
    assignedExpr v@(Variable _ IntType) (VarModel ints bools strings) = Map.lookup v ints
    assignedExpr (Variable n t) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Integer"
    assignedExprWithDefault v@(Variable _ IntType) (VarModel ints bools strings) = Map.findWithDefault (var v) v ints
    assignedExprWithDefault (Variable n t) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Integer"

instance Assignable Bool where
    assign v@(Variable _ BoolType) e m = m {boolVars = Map.insert v e (boolVars m)}
    assign (Variable n t) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Bool, received " ++ show t
    assignValue v@(Variable _ BoolType) val m = m {boolValuation = Map.insert v val (boolValuation m)}
    assignValue (Variable n t) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected Bool, received " ++ show t
    assignedExpr v@(Variable _ BoolType) (VarModel ints bools strings) = Map.lookup v bools
    assignedExpr (Variable n t) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Bool"
    assignedExprWithDefault v@(Variable _ BoolType) (VarModel ints bools strings) = Map.findWithDefault (var v) v bools
    assignedExprWithDefault (Variable n t) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received Bool"

instance Assignable String where
    assign v@(Variable _ StringType) e m = m {stringVars = Map.insert v e (stringVars m)}
    assign (Variable n t) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected String, received " ++ show t
    assignValue v@(Variable _ StringType) val m = m {stringValuation = Map.insert v val (stringValuation m)}
    assignValue (Variable n t) _ _ = error $ "Assignment to '" ++ n ++ "' to wrong type: expected String, received " ++ show t
    assignedExpr v@(Variable _ StringType) (VarModel ints bools strings) = Map.lookup v strings
    assignedExpr (Variable n t) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received String"
    assignedExprWithDefault v@(Variable _ StringType) (VarModel ints bools strings) = Map.findWithDefault (var v) v strings
    assignedExprWithDefault (Variable n t) _ = error $ "Assignment from '" ++ n ++ "' to wrong type: expected " ++ show t ++ ", received String"

noAssignment :: VarModel
noAssignment = VarModel Map.empty Map.empty Map.empty

instance Show VarModel where
    show (VarModel ints bools strings) = showMapList $ showList ints ++ showList bools ++ showList strings
        where
        showMapList map = "{" ++ (List.intercalate ", " map) ++ "}"
        showList map = showAssign <$> Map.toList map
        showAssign (v,e) = show v ++ ":=" ++ show e

evalConst :: Assignable t => Valuation -> Expr t -> Either String t
evalConst valuation = eval . evalConst' valuation


evalConst' :: Assignable t => Valuation -> Expr t -> Expr t
evalConst' valuation e = subst (valuationToVarModel valuation) e

-- | Substitute variables by value expressions in a value expression.
--
-- Preconditions are /not/ checked.
--
subst :: Assignable t => VarModel      -- ^ Map from variables to value expressions.
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

subst' :: Assignable t => VarModel -> ExprView t -> Expr t
subst' _  (Const const')          = cons const'
subst' ve (Var vid)               = assignedExprWithDefault vid ve
subst' ve (Ite cond vexp1 vexp2)  = ifThenElse (subst' ve cond) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (Divide t n)            = (./) (subst' ve t) (subst' ve n)
subst' ve (Modulo t n)            = cstrModulo (subst' ve t) (subst' ve n)
subst' ve (Sum s)                 = (.+) $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT s
subst' ve (Product p)             = (.*) $ FMX.fromOccurListT $ map (first (subst' ve)) $ FMX.toDistinctAscOccurListT p
subst' ve (Length vexp)           = cstrLength (subst' ve vexp)

subst' ve (GezInt v)                = cstrGEZ (subst' ve v)
subst' ve (EqualInt vexp1 vexp2)    = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (EqualBool vexp1 vexp2)   = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (EqualString vexp1 vexp2) = (.==) (subst' ve vexp1) (subst' ve vexp2)
subst' ve (And vexps)               = (.&&) $ Set.map (subst' ve) vexps
subst' ve (Not vexp)                = neg (subst' ve vexp)

subst' ve (At s p)                      = cstrAt (subst' ve s) (subst' ve p)
subst' ve (Concat vexps)                = cstrConcat $ map (subst' ve) vexps

