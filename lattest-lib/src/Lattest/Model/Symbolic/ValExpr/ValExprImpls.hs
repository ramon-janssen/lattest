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
  cstrConst
  -- ** VarRef
, cstrVar
  -- ** General Operators to create Value Expressions
  -- *** Equal
, cstrEqual
  -- *** If Then Else
, cstrITE
  -- *** Function Call
--, cstrFunc
  -- ** Boolean Operators to create Value Expressions
  -- *** Not
, cstrNot
  -- *** And
, cstrAnd
  -- ** Integer Operators to create Value Expressions
  -- *** Sum
, cstrSum
  -- *** Product
, cstrProduct
  -- *** Divide
, cstrDivide
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
, evalConst
, evalConst'
, Subst
, subst
, compSubst         -- changes type
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
import           Lattest.Model.Symbolic.ValExpr.Constant
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
                Vconst x -> cstrConst x
                _        -> if all isConst arguments
                            then compSubst (Map.fromList (zip params arguments)) fis body
                            else ValExpr (Vfunc fi arguments)

-- | Apply ADT Constructor of constructor with CstrId and the provided arguments (the list of value expressions).
-- Preconditions are /not/ checked.
cstrCstr :: CstrId -> [ValExpr] -> ValExpr
cstrCstr c a = if all isConst a
                then cstrConst (Ccstr c (map toConst a) )
                else ValExpr (Vcstr c a)
    where   toConst :: ValExpr -> Constant
            toConst (view -> Vconst v) = v
            toConst _                  = error "Impossible when all satisfy isConst"

-- | Is the provided value expression made by the ADT constructor with CstrId?
-- Preconditions are /not/ checked.
cstrIsCstr :: CstrId -> ValExpr -> ValExpr
cstrIsCstr c1 (view -> Vcstr c2 _)          = cstrConst (Cbool (c1 == c2) )
cstrIsCstr c1 (view -> Vconst (Ccstr c2 _)) = cstrConst (Cbool (c1 == c2) )
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
        then cstrConst (fields!!p1)
        else error ("Error in model: Accessing field " ++ show n1 ++ " of constructor " ++ show c1 ++ " on value from constructor " ++ show c2)
cstrAccess c n p e = ValExpr (Vaccess c n p e)
-}
-- | Is ValExpr a Constant/Value Expression?
--isConst :: ValExpr -> Bool
--isConst (view -> Vconst{}) = True
--isConst _                  = False

cstrConst :: ExprType t => t -> Expr t
cstrConst = Const

cstrVar :: Variable t -> Expr t
cstrVar = Var

-- | Apply operator ITE (IF THEN ELSE) on the provided value expressions.
-- Preconditions are /not/ checked.
cstrITE :: Expr Bool -> Expr t -> Expr t -> Expr t
cstrITE (view -> Const True) t _ = t
cstrITE (view -> Const False) _ f = f
cstrITE c t f = Ite c t f

-- | Create a variable as a value expression.
-- typeclass because every type has its own ExprView-constructor
class EqExpr t where
    cstrEqual :: Expr t -> Expr t -> Expr Bool
    
instance EqExpr Integer where
    cstrEqual (view -> x) (view -> y) = Expr $ EqualInt x y

instance EqExpr Bool where
    cstrEqual (view -> x) (view -> y) = Expr $ EqualBool x y

instance EqExpr String where
    cstrEqual (view -> x) (view -> y) = Expr $ EqualString x y



{-
-- | Apply operator Equal on the provided value expressions.
-- Preconditions are /not/ checked.
cstrEqual :: Expr -> Expr -> Expr
-- Simplification a == a <==> True
cstrEqual ve1 ve2 | ve1 == ve2                      = cstrConst (Cbool True)
-- Simplification Different Values <==> False : use Same Values are already detected in previous step
cstrEqual (view -> Vconst _) (view -> Vconst _)     = cstrConst (Cbool False)
-- Simplification True == e <==> e (twice)
cstrEqual (view -> Vconst (Cbool True)) e           = e
cstrEqual e (view -> Vconst (Cbool True))           = e

-- Simplification False == e <==> not e (twice)
cstrEqual (view -> Vconst (Cbool False)) e              = cstrNot e
cstrEqual e (view -> Vconst (Cbool False))              = cstrNot e
-- Not x == x <==> false (twice)
cstrEqual e (view -> Vnot n) | e == n                   = cstrConst (Cbool False)
cstrEqual (view -> Vnot n) e | e == n                   = cstrConst (Cbool False)
-- Not x == Not y <==> x == y   -- same representation
cstrEqual (view -> Vnot n1) (view -> Vnot n2)     = cstrEqual n1 n2
-- Not a == b <==> a == Not b -- same representation (twice)
cstrEqual x@(view -> Vnot n) e                = if n <= e
                                                        then Expr (Vequal x e)
                                                        else Expr (Vequal (cstrNot e) n)
cstrEqual e x@(view -> Vnot n)                = if n <= e
                                                        then Expr (Vequal x e)
                                                        else Expr (Vequal (cstrNot e) n)
-- a == b <==> b == a -- same representation
cstrEqual ve1 ve2                                   = if ve1 <= ve2
                                                        then Expr (Vequal ve1 ve2)
                                                        else Expr (Vequal ve2 ve1)
-}

-- | Apply operator Not on the provided value expression.
-- Preconditions are /not/ checked.
cstrNot :: Expr Bool -> Expr Bool
{-cstrNot (view -> Vconst (Cbool True))       = cstrConst (Cbool False)
cstrNot (view -> Vconst (Cbool False))      = cstrConst (Cbool True)
cstrNot (view -> Vnot ve)                   = ve
-- not (if cs then tb else fb) == if cs then not (tb) else not (fb)
cstrNot (view -> Vite cs tb fb)             = Expr (Vite cs (cstrNot tb) (cstrNot fb))-}
cstrNot (view -> ve) = Expr $ Not ve

-- | Apply operator And on the provided set of value expressions.
-- Preconditions are /not/ checked.
cstrAnd :: Set.Set (Expr Bool) -> Expr Bool
--cstrAnd = cstrAnd' . flattenAnd
cstrAnd = Expr . And . flattenAnd
    where
        flattenAnd :: Set.Set (Expr Bool) -> Set.Set (ExprView Bool)
        flattenAnd = Set.unions . map fromExpr . Set.toList
        
        fromExpr :: Expr Bool -> Set.Set (ExprView Bool)
        fromExpr (view -> And a) = a
        fromExpr (view -> x) = Set.singleton x
{-
-- And doesn't contain elements of type Vand.
cstrAnd' :: Set.Set Expr Bool -> Expr Bool
cstrAnd' s =
    if Set.member (cstrConst (Cbool False)) s
        then cstrConst (Cbool False)
        else let s' = Set.delete (cstrConst (Cbool True)) s in
                case Set.size s' of
                    0   -> cstrConst (Cbool True)
                    1   -> head (Set.toList s')
                    _   ->  -- not(x) and x == False
                            let nots = filterNot (Set.toList s') in
                                if any (contains s') nots
                                    then cstrConst (Cbool False)
--                                    else let ts = isCstrTuples (Set.toList s') in
--                                            if sameExpr ts
--                                                then cstrConst (Cbool False)
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
{-
-- | Is Expr a Sum Expression?
isSum :: Expr Integer -> Bool
isSum (view -> Sum _) = True
isSum _ = False

getSum :: ExprView Integer -> FreeSum (ExprView Integer)
getSum (Sum s) = s
getSum _ = error "ExprImpls.hs - getSum - Unexpected Expr "

-- | Apply operator sum on the provided sum of value expressions.
-- Preconditions are /not/ checked.
cstrSum ::  FreeSum (Expr Integer) -> Expr Integer
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the sum of all values
--         special case if the sum is zero, no value is inserted since v == v+0
--    remove all nested sums, since (a+b) + (c+d) == (a+b+c+d)
cstrSum ms = cstrSum' $ nonadds <> FMX.flatten sumOfAdds
    where
      (adds, nonadds) = FMX.partitionT isSum ms
      sumOfAdds :: FMX.FreeMonoidX (FMX.FreeMonoidX (SumTerm (Expr Integer)))
      sumOfAdds = FMX.mapTerms (getSum . summand) adds

-- Sum doesn't contain elements of type VExprSum
cstrSum' :: FreeSum (ExprView Integer) -> ExprView Integer
cstrSum' ms =
    let (vals, nonvals) = FMX.partitionT (isConst . view) ms
        sumVals = summand $ FMX.foldFMX (FMX.mapTerms (SumTerm . getIntVal . summand) vals)
        retMS = case sumVals of
                    0 -> nonvals                                      -- 0 + x == x
                    _ -> Sum.add (cstrConst (Cint sumVals)) nonvals
    in
        case FMX.toOccurList retMS of
            []         -> cstrConst (Cint 0)                                -- sum of nothing equal zero
            [(term,1)] -> summand term
            _          -> Expr (Sum retMS)

getIntVal :: ExprView Integer -> Integer
getIntVal (Const i) = i 

-- Product

-- | Is Expr a Product Expression?
isProduct :: ExprView Integer -> Bool
isProduct (Product _) = True
isProduct _ = False

getProduct :: ExprView Integer -> FreeProduct (ExprView Integer)
getProduct (Product p) = p
getProduct _ = error "ExprImpls.hs - getProduct - Unexpected Expr "

-- | Apply operator product on the provided product of value expressions.
-- Be aware that division is not associative for Integer, so only use power >= 0.
-- Preconditions are /not/ checked.
cstrProduct :: FreeProduct (Expr Integer) -> Expr Integer
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the product of all values
--         special case if the product is one, no value is inserted since v == v*1
--    remove all nested products, since (a*b) * (c*d) == (a*b*c*d)
cstrProduct ms =
    cstrProduct' $ noprods <> FMX.flatten prodOfProds
    where
      (prods, noprods) = FMX.partitionT isProduct ms
      prodOfProds :: FMX.FreeMonoidX (FMX.FreeMonoidX (ProductTerm (Expr Integer)))
      prodOfProds = FMX.mapTerms (view . getProduct . factor) prods

-- Product doesn't contain elements of type VExprProduct
cstrProduct' :: FreeProduct (Expr Integer) -> Expr Integer
cstrProduct' ms =
    let (vals, nonvals) = FMX.partitionT (isConst . view) ms
        (zeros, _) = FMX.partitionT isZero vals
    in
        case FMX.nrofDistinctTerms zeros of
            0   ->  -- let productVals = Product.foldPower timesVal 1 vals in
                    let intProducts = FMX.mapTerms (getIntVal <$>) vals
                        productVals = factor (FMX.foldFMX intProducts)
                    in
                        case FMX.toDistinctAscOccurListT nonvals of
                            []          ->  cstrConst (Cint productVals)
                            [(term, 1)] ->  cstrSum (FMX.fromOccurList [(SumTerm term, productVals)])                           -- term can be Sum -> rewrite needed
                            _           ->  cstrSum (FMX.fromOccurList [(SumTerm (Expr (Product nonvals)), productVals)])  -- productVals can be 1 -> rewrite possible
            _   ->  let (_, n) = Product.fraction zeros in
                        case FMX.nrofDistinctTerms n of
                            0   ->  cstrConst (Cint 0)      -- 0 * x == 0
                            _   ->  error "Error in model: Division by Zero in Product (via negative power)"
    where
        isZero :: Expr Integer -> Bool
        isZero (view -> Const 0) = True
        isZero _                            = False
-}
-- Divide

-- | Apply operator Divide on the provided value expressions.
-- Preconditions are /not/ checked.
cstrDivide :: Expr Integer -> Expr Integer -> Expr Integer
cstrDivide _                     (view -> Const n) | n == 0 = error "Error in model: Division by Zero in Divide"
cstrDivide (view ->  Const t) (view -> Const n) = cstrConst (t `Boute.div` n)
cstrDivide (view -> vet)         (view -> ven) = Expr (Divide vet ven)

-- Modulo

-- | Apply operator Modulo on the provided value expressions.
-- Preconditions are /not/ checked.
cstrModulo :: Expr Integer -> Expr Integer -> Expr Integer
cstrModulo _                    (view -> Const n) | n == 0 = error "Error in model: Division by Zero in Modulo"
cstrModulo (view -> Const t) (view -> Const n) = cstrConst (t `Boute.mod` n)
cstrModulo (view -> vet)        (view -> ven) = Expr (Modulo vet ven)

-- | Apply operator GEZ (Greater Equal Zero) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGEZ :: Expr Integer -> Expr Bool
-- Simplification Values
cstrGEZ (view -> Const v) = cstrConst (0 <= v)
cstrGEZ (view -> Length _)   = cstrConst True        -- length of string is always Greater or equal to zero
cstrGEZ (view -> ve)         = Expr (GezInt ve)


-- | Apply operator Length on the provided value expression.
-- Preconditions are /not/ checked.
cstrLength :: Expr String -> Expr Integer
cstrLength (view -> Const s) = cstrConst (Prelude.toInteger (length s))
cstrLength (view -> v)             = Expr (Length v)

-- | Apply operator At on the provided value expressions.
-- Preconditions are /not/ checked.
cstrAt :: Expr String -> Expr Integer -> Expr String
cstrAt (view -> Const s) (view -> Const i) =
    if i < 0 || i >= Prelude.toInteger (length s)
        then error ("Error in model: Accessing string " ++ show s ++ " of length " ++ show (length s) ++ " with illegal index "++ show i) 
        else cstrConst (take 1 (drop (fromInteger i) s))
cstrAt (view -> ves) (view -> vei) = Expr $ At ves vei

-- | Apply operator Concat on the provided sequence of value expressions.
-- Preconditions are /not/ checked.
cstrConcat :: [Expr String] -> Expr String
cstrConcat l =
    let n = (mergeVals . flatten . filter (cstrConst "" /= ) ) l in
        case Prelude.length n of
           0 -> cstrConst ""
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
                          mergeVals (cstrConst (s1 <> s2): xs)
mergeVals (x1:x2:xs)    = x1 : mergeVals (x2:xs)

flatten :: [Expr String] -> [Expr String]
flatten []                       = []
flatten ((view -> Concat l):xs) = fmap Expr l ++ flatten xs
flatten (x:xs)                   = x : flatten xs

-- | Apply String In Regular Expression operator on the provided value expressions.
-- Preconditions are /not/ checked.
--cstrStrInRe :: Expr -> Expr -> Expr
--cstrStrInRe (view -> Vconst (Cstring s)) (view -> Vconst (Cregex r)) = cstrConst (Cbool (T.unpack s =~ T.unpack (xsd2posix r) ) )
--cstrStrInRe s r                                                      = Expr (Vstrinre s r)

{-
-- | Create a call to a predefined function as a value expression.
cstrPredef :: PredefKind -> FuncId -> [Expr] -> Expr
cstrPredef p f a = Expr (Vpredef p f a)
-}

type TypedValuation t = Map.Map (Variable t) t
data Valuation = Valuation {
    intValuation :: TypedValuation Integer,
    boolValuation :: TypedValuation Bool,
    stringValuation :: TypedValuation String
    }
    deriving (Eq, Ord)

type TypedVarModel t = Map.Map (Variable t) (Expr t)
data VarModel = VarModel {
    intVars :: TypedVarModel Integer,
    boolVars :: TypedVarModel Bool,
    stringVars :: TypedVarModel String
    }
    deriving (Eq, Ord)

assignment :: [VarModel -> VarModel] -> VarModel
assignment fs = foldr ($) noAssignment fs

class Assignable t where
    assign :: Variable t -> Expr t -> VarModel -> VarModel
    assignedExpr :: Variable t -> VarModel -> Maybe (Expr t)
    assignedExprWithDefault :: Variable -> VarModel -> Expr t

(=:) :: Assignable t => Variable -> Expr t -> VarModel -> VarModel
(=:) = assign
infixr 0 =:

instance Assignable Integer where
    assign v e m = case varType v of
        IntType -> assignInt v e m
        _ -> error $ "assigned Integer expression to Variable " ++ show v
    assignedExpr v (VarModel ints bools strings) = case varType v of
        IntType -> Map.lookup v ints
        _ -> error $ "cannot lookup Integer Value for variable " ++ show v
    assignedExprWithDefault v (VarModel ints bools strings) =  case varType v of
        IntType -> Map.findWithDefault (cstrVar v) v ints
        _ -> error $ "cannot lookup Integer Value for variable " ++ show v
assignInt :: Variable -> Expr Integer -> VarModel -> VarModel
assignInt v e m = m {intVars = Map.insert v e (intVars m)}

instance Assignable (ExprView Bool) where
    assign v e m = case varType v of
        BoolType -> assignBool v e m
        _ -> error $ "assigned Bool expression to Variable " ++ show v
    assignedExpr v (VarModel ints bools strings) = case varType v of
        BoolType -> Map.lookup v bools
        _ -> error $ "cannot lookup Bool Value for variable " ++ show v
    assignedExprWithDefault v (VarModel ints bools strings) =  case varType v of
        BoolType -> Map.findWithDefault (cstrVar v) v bools
        _ -> error $ "cannot lookup Bool Value for variable " ++ show v
assignBool :: Variable -> Expr Bool -> VarModel -> VarModel
assignBool v e m = m {boolVars = Map.insert v e (boolVars m)}

instance Assignable (ExprView String) where
    assign v e m = case varType v of
        StringType -> assignString v e m
        _ -> error $ "assigned String expression to Variable " ++ show v
    assignedExpr v (VarModel ints bools strings) = case varType v of
        StringType -> Map.lookup v strings
        _ -> error $ "cannot lookup String Value for variable " ++ show v
    assignedExprWithDefault v (VarModel ints bools strings) =  case varType v of
        StringType -> Map.findWithDefault (cstrVar v) v strings
        _ -> error $ "cannot lookup String Value for variable " ++ show v
assignString :: Variable -> Expr String -> VarModel -> VarModel
assignString v e m = m {stringVars = Map.insert v e (stringVars m)}

noAssignment :: VarModel
noAssignment = VarModel Map.empty Map.empty Map.empty

instance Show VarModel where
    show (VarModel ints bools strings) = showMapList $ showList ints ++ showList bools ++ showList strings
        where
        showMapList map = "{" ++ (List.intercalate ", " map) ++ "}"
        showList map = showAssign <$> Map.toList map
        showAssign (v,e) = show v ++ ":=" ++ show e

evalConst :: (Subst t) => Valuation -> (Expr t) -> Either String Constant
evalConst valuation = eval . evalConst' valuation

valuationToVarModel :: Valuation -> VarModel
valuationToVarModel vals = foldr (uncurry assignConstant) noAssignment $ Map.toList vals

assignConstant :: Variable -> Constant -> VarModel -> VarModel
assignConstant var@(Variable _ IntType) val@(Cint _) = assignInt var (cstrConst val)
assignConstant var@(Variable _ BoolType) val@(Cbool _) = assignBool var (cstrConst val)
assignConstant var@(Variable _ StringType) val@(Cstring _) = assignString var (cstrConst val)
assignConstant var val = error $ "cannot assign value " ++ show val ++ " to variable " ++ show var

evalConst' :: Subst t => Valuation -> (Expr t) -> (Expr t)
evalConst' valuation e = subst (valuationToVarModel valuation) e

-- | Substitute variables by value expressions in a value expression.
--
-- Preconditions are /not/ checked.
--
subst :: Subst e
      => VarModel      -- ^ Map from variables to value expressions.
{-      -> Map.Map FuncId (FuncDef w e) -- ^ Map from identifiers to their
                                    -- definitions, this is used to replace
                                    -- function calls by their bodies if all
                                    -- the arguments of the function are
                                    -- constant.-}
      -> Expr e                -- ^ Value expression where the
                                    -- substitution will take place.
      -> Expr e
--subst ve _ x   | ve == Map.empty = x
subst ve x = subst' ve (view x)

class Subst e where
    subst' :: VarModel -> e -> Expr e

instance Subst (ExprView Integer) where
    --subst' :: VarModel -> Map.Map FuncId (FuncDef w e) -> ExprView Bool -> Expr e
    subst' _    (Const const')          = cstrConst const'
    subst' ve   (Var vid)               = assignedExprWithDefault vid ve
    --subst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (subst' ve fis . view) vexp)
    subst' ve (Ite cond vexp1 vexp2)  = cstrITE ( (subst' ve . view) cond) ( (subst' ve . view) vexp1) ( (subst' ve . view) vexp2)
    subst' ve (Divide t n)            = cstrDivide ( (subst' ve . view) t) ( (subst' ve . view) n)
    subst' ve (Modulo t n)            = cstrModulo ( (subst' ve . view) t) ( (subst' ve . view) n)
    subst' ve (Sum s)                 = cstrSum $ FMX.fromOccurListT $ map (first (subst' ve . view)) $ FMX.toDistinctAscOccurListT s
    subst' ve (Product p)             = cstrProduct $ FMX.fromOccurListT $ map (first (subst' ve . view)) $ FMX.toDistinctAscOccurListT p
    subst' ve (Length vexp)              = cstrLength ( (subst' ve . view) vexp)
    --subst' ve fis (Vstrinre s r)           = cstrStrInRe ( (subst' ve fis . view) s) ( (subst' ve fis . view) r)
    --subst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (subst' ve fis . view) vexps)

instance Subst (ExprView Bool) where
    --subst' :: VarModel -> Map.Map FuncId (FuncDef w e) -> ExprView Bool -> Expr e
    subst' _    (Const const')         = cstrConst const'
    subst' ve   (Var vid)              = assignedExprWithDefault vid ve
    --subst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (subst' ve fis . view) vexp)
    subst' ve (Var cond vexp1 vexp2)= cstrITE ( (subst' ve . view) cond) ( (subst' ve . view) vexp1) ( (subst' ve . view) vexp2)
    subst' ve (GezInt v)                = cstrGEZ ( (subst' ve . view) v)
    subst' ve (EqualInt vexp1 vexp2)    = cstrEqual ( (subst' ve . view) vexp1) ( (subst' ve . view) vexp2)
    subst' ve (EqualBool vexp1 vexp2)   = cstrEqual ( (subst' ve . view) vexp1) ( (subst' ve . view) vexp2)
    subst' ve (EqualString vexp1 vexp2) = cstrEqual ( (subst' ve . view) vexp1) ( (subst' ve . view) vexp2)
    subst' ve (And vexps)               = cstrAnd $ Set.map (subst' ve . view) vexps
    subst' ve (Not vexp)                = cstrNot ( (subst' ve . view) vexp)
    --subst' ve fis (Vstrinre s r)           = cstrStrInRe ( (subst' ve fis . view) s) ( (subst' ve fis . view) r)
    --subst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (subst' ve fis . view) vexps)

instance Subst (ExprView String) where
    --subst' :: VarModel -> Map.Map FuncId (FuncDef w e) -> ExprView Bool -> Expr e
    subst' _    (Const const')          = cstrConst const'
    subst' ve   (Var vid)               = assignedExprWithDefault vid ve
    --subst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (subst' ve fis . view) vexp)
    subst' ve (Ite cond vexp1 vexp2)  = cstrITE ( (subst' ve . view) cond) ( (subst' ve . view) vexp1) ( (subst' ve . view) vexp2)
    subst' ve (At s p)                      = cstrAt ( (subst' ve . view) s) ( (subst' ve . view) p)
    subst' ve (Concat vexps)                = cstrConcat $ map (subst' ve . view) vexps
    --subst' ve fis (Vstrinre s r)           = cstrStrInRe ( (subst' ve fis . view) s) ( (subst' ve fis . view) r)
    --subst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (subst' ve fis . view) vexps)

compSubst :: CompSubst t => VarModel -> Expr t -> Expr t
-- compSubst ve _ _ | ve == Map.empty = error "TXS Subst compSubst: variables must be substitute, yet varenv empty\n"
compSubst ve x                 = compSubst' ve (view x)

class CompSubst e where
    compSubst' :: VarModel ->  e -> Expr e

instance CompSubst (ExprView Integer) where
    -- | Substitute variables by value expressions in a value expression (change variable kind).
    -- Preconditions are /not/ checked.
    --compSubst' _  _   (Vconst const')          = cstrConst const'
    compSubst' ve   (Var vid)               = fromMaybe
                                                        (error ("TXS Subst compSubst: incomplete (vid = " ++ show vid ++ "; map = " ++ show ve ++ ")"))
                                                        (assignedExpr vid ve)
    --compSubst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (compSubst' ve fis . view) vexp)
    compSubst' ve (Ite cond vexp1 vexp2)  = cstrITE ( (compSubst' ve . view) cond) ( (compSubst' ve . view) vexp1) ( (compSubst' ve . view) vexp2)
    compSubst' ve (Divide t n)            = cstrDivide ( (compSubst' ve . view) t) ( (compSubst' ve . view) n)
    compSubst' ve (Modulo t n)            = cstrModulo ( (compSubst' ve . view) t) ( (compSubst' ve . view) n)
    compSubst' ve (Sum s)                 = cstrSum $ FMX.fromOccurListT $ map (first (compSubst' ve . view)) $ FMX.toDistinctAscOccurListT s
    compSubst' ve (Product p)             = cstrProduct $ FMX.fromOccurListT $ map (first (compSubst' ve . view)) $ FMX.toDistinctAscOccurListT p
    compSubst' ve (Length vexp)           = cstrLength ( (compSubst' ve . view) vexp)
    --compSubst' ve fis (Vstrinre s r)           = cstrStrInRe ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) r)
    --compSubst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (compSubst' ve fis . view) vexps)

instance CompSubst (ExprView Bool) where
    -- | Substitute variables by value expressions in a value expression (change variable kind).
    -- Preconditions are /not/ checked.
    --compSubst' _  _   (Vconst const')          = cstrConst const'
    compSubst' ve   (Var vid)               = fromMaybe
                                                        (error ("TXS Subst compSubst: incomplete (vid = " ++ show vid ++ "; map = " ++ show ve ++ ")"))
                                                        (assignedExpr vid ve)
    --compSubst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (compSubst' ve fis . view) vexp)
    compSubst' ve (Var cond vexp1 vexp2) = cstrITE ( (compSubst' ve . view) cond) ( (compSubst' ve . view) vexp1) ( (compSubst' ve . view) vexp2)
    compSubst' ve (GezInt v)                = cstrGEZ ( (compSubst' ve . view) v)
    compSubst' ve (EqualInt vexp1 vexp2)     = cstrEqual ( (compSubst' ve . view) vexp1) ( (compSubst' ve . view) vexp2)
    compSubst' ve (EqualBool vexp1 vexp2)    = cstrEqual ( (compSubst' ve . view) vexp1) ( (compSubst' ve . view) vexp2)
    compSubst' ve (EqualString vexp1 vexp2)  = cstrEqual ( (compSubst' ve . view) vexp1) ( (compSubst' ve . view) vexp2)
    compSubst' ve (And vexps)                = cstrAnd $ Set.map (compSubst' ve . view) vexps
    compSubst' ve (Not vexp)                 = cstrNot ( (compSubst' ve . view) vexp)
    --compSubst' ve fis (Vstrinre s r)           = cstrStrInRe ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) r)
    --compSubst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (compSubst' ve fis . view) vexps)

instance CompSubst (ExprView String) where
    -- | Substitute variables by value expressions in a value expression (change variable kind).
    -- Preconditions are /not/ checked.
    --compSubst' _  _   (Vconst const')          = cstrConst const'
    compSubst' ve   (Var vid)               = fromMaybe
                                                        (error ("TXS Subst compSubst: incomplete (vid = " ++ show vid ++ "; map = " ++ show ve ++ ")"))
                                                        (assignedExpr vid ve)
    --compSubst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (compSubst' ve fis . view) vexp)
    compSubst' ve (Ite cond vexp1 vexp2)  = cstrITE ( (compSubst' ve . view) cond) ( (compSubst' ve . view) vexp1) ( (compSubst' ve . view) vexp2)
    compSubst' ve (At s p)                      = cstrAt ( (compSubst' ve . view) s) ( (compSubst' ve . view) p)
    compSubst' ve (Concat vexps)                = cstrConcat $ map (compSubst' ve . view) vexps
    --compSubst' ve fis (Vstrinre s r)           = cstrStrInRe ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) r)
    --compSubst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (compSubst' ve fis . view) vexps)

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
