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
, subst
, compSubst         -- changes type
, assignedExpr
, assignment
, noAssignment
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
import           Lattest.Model.Symbolic.ValExpr.CstrId
import qualified Lattest.Model.Symbolic.ValExpr.FreeMonoidX        as FMX
import           Lattest.Model.Symbolic.ValExpr.FuncDef
import           Lattest.Model.Symbolic.ValExpr.FuncId
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

-- | Get the integer value of a constant.
getIntVal :: ValExprInt -> Integer
getIntVal (view -> VIntConst (Cint i)) = i
getIntVal (view -> VIntConst _)        =
    error "ValExprImpls.hs - getIntVal - Unexpected Constant"
getIntVal _                         =
    error "ValExprImpls.hs - getIntVal - Unexpected ValExpr"

-- TODO These functions can directly typecheck the type of the constant. Maybe remove the Constant layer entirely, and directly supply an Int,...?
-- | Create a constant as a value expression.
class ConstExpr t where
    cstrConst :: Constant -> ValExpr t

instance ConstExpr ValExprIntView where
    cstrConst = ValExpr . VIntConst

instance ConstExpr ValExprBoolView where
    cstrConst = ValExpr . VBoolConst

instance ConstExpr ValExprStringView where
    cstrConst = ValExpr . VStringConst

-- | Create a variable as a value expression.
class VarExpr t where
    cstrVar :: Variable -> ValExpr t

instance VarExpr ValExprIntView where
    cstrVar = ValExpr . VIntVar

instance VarExpr ValExprBoolView where
    cstrVar = ValExpr . VBoolVar

instance VarExpr ValExprStringView where
    cstrVar = ValExpr . VStringVar

-- | Apply operator ITE (IF THEN ELSE) on the provided value expressions.
-- Preconditions are /not/ checked.
class IteExpr t where
    cstrITE :: ValExprBool -> ValExpr t -> ValExpr t -> ValExpr t

instance IteExpr ValExprIntView where
    cstrITE (view -> VBoolConst (Cbool True))  tb _ = tb
    cstrITE (view -> VBoolConst (Cbool False)) _ fb = fb
    -- if q then p else False fi <==> q /\ p : Note: p is boolean expression (otherwise different sorts in branches) 
    -- Not implemented to enable conditional evaluation 
    -- if c then a else a <==> a
{-    cstrITE _ tb fb | tb == fb = tb
    -- Simplification: if c then True else False <==> c
    cstrITE c (view -> VBoolConst (Cbool True)) (view -> Vconst (Cbool False)) = c
    -- Simplification: if c then False else True <==> not c
    cstrITE c (view -> VBoolConst (Cbool False)) (view -> Vconst (Cbool True)) = cstrNot c
    -- if (not c) then tb else fb <==> if c then fb else tb
    cstrITE (view -> Vnot n) tb fb              = ValExpr (Vite n fb tb)-}
    cstrITE cs tb fb                            = ValExpr (VIntIte cs tb fb)

instance IteExpr ValExprBoolView where
    cstrITE (view -> VBoolConst (Cbool True))  tb _ = tb
    cstrITE (view -> VBoolConst (Cbool False)) _ fb = fb
    -- if q then p else False fi <==> q /\ p : Note: p is boolean expression (otherwise different sorts in branches) 
    -- Not implemented to enable conditional evaluation 
    -- if c then a else a <==> a
{-    cstrITE _ tb fb | tb == fb = tb
    -- Simplification: if c then True else False <==> c
    cstrITE c (view -> VBoolConst (Cbool True)) (view -> Vconst (Cbool False)) = c
    -- Simplification: if c then False else True <==> not c
    cstrITE c (view -> VBoolConst (Cbool False)) (view -> Vconst (Cbool True)) = cstrNot c
    -- if (not c) then tb else fb <==> if c then fb else tb
    cstrITE (view -> Vnot n) tb fb              = ValExpr (Vite n fb tb)-}
    cstrITE cs tb fb                            = ValExpr (VBoolIte cs tb fb)

instance IteExpr ValExprStringView where
    cstrITE (view -> VBoolConst (Cbool True))  tb _ = tb
    cstrITE (view -> VBoolConst (Cbool False)) _ fb = fb
    -- if q then p else False fi <==> q /\ p : Note: p is boolean expression (otherwise different sorts in branches) 
    -- Not implemented to enable conditional evaluation 
    -- if c then a else a <==> a
{-    cstrITE _ tb fb | tb == fb = tb
    -- Simplification: if c then True else False <==> c
    cstrITE c (view -> VBoolConst (Cbool True)) (view -> Vconst (Cbool False)) = c
    -- Simplification: if c then False else True <==> not c
    cstrITE c (view -> VBoolConst (Cbool False)) (view -> Vconst (Cbool True)) = cstrNot c
    -- if (not c) then tb else fb <==> if c then fb else tb
    cstrITE (view -> Vnot n) tb fb              = ValExpr (Vite n fb tb)-}
    cstrITE cs tb fb                            = ValExpr (VStringIte cs tb fb)

-- | Create a variable as a value expression.
class EqExpr t where
    cstrEqual :: ValExpr t -> ValExpr t -> ValExprBool
    
instance EqExpr ValExprIntView where
    cstrEqual x y = ValExpr $ VEqualInt x y

instance EqExpr ValExprBoolView where
    cstrEqual x y = ValExpr $ VEqualBool x y

instance EqExpr ValExprStringView where
    cstrEqual x y = ValExpr $ VEqualString x y



{-
-- | Apply operator Equal on the provided value expressions.
-- Preconditions are /not/ checked.
cstrEqual :: ValExpr -> ValExpr -> ValExpr
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
                                                        then ValExpr (Vequal x e)
                                                        else ValExpr (Vequal (cstrNot e) n)
cstrEqual e x@(view -> Vnot n)                = if n <= e
                                                        then ValExpr (Vequal x e)
                                                        else ValExpr (Vequal (cstrNot e) n)
-- a == b <==> b == a -- same representation
cstrEqual ve1 ve2                                   = if ve1 <= ve2
                                                        then ValExpr (Vequal ve1 ve2)
                                                        else ValExpr (Vequal ve2 ve1)
-}

-- | Apply operator Not on the provided value expression.
-- Preconditions are /not/ checked.
cstrNot :: ValExprBool -> ValExprBool
{-cstrNot (view -> Vconst (Cbool True))       = cstrConst (Cbool False)
cstrNot (view -> Vconst (Cbool False))      = cstrConst (Cbool True)
cstrNot (view -> Vnot ve)                   = ve
-- not (if cs then tb else fb) == if cs then not (tb) else not (fb)
cstrNot (view -> Vite cs tb fb)             = ValExpr (Vite cs (cstrNot tb) (cstrNot fb))-}
cstrNot ve                                  = ValExpr (VNot ve)

-- | Apply operator And on the provided set of value expressions.
-- Preconditions are /not/ checked.
cstrAnd :: Set.Set ValExprBool -> ValExprBool
--cstrAnd = cstrAnd' . flattenAnd
cstrAnd = ValExpr . VAnd . flattenAnd
    where
        flattenAnd :: Set.Set ValExprBool -> Set.Set ValExprBool
        flattenAnd = Set.unions . map fromValExpr . Set.toList
        
        fromValExpr :: ValExprBool -> Set.Set ValExprBool
        fromValExpr (view -> VAnd a) = a
        fromValExpr x                = Set.singleton x
{-
-- And doesn't contain elements of type Vand.
cstrAnd' :: Set.Set ValExprBool -> ValExprBool
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
--                                            if sameValExpr ts
--                                                then cstrConst (Cbool False)
                                                else ValExpr (Vand s')
    where
        filterNot :: [ValExpr] -> [ValExpr]
        filterNot [] = []
        filterNot (x:xs) = case view x of
                            Vnot n -> n : filterNot xs
                            _      ->     filterNot xs
        
        contains :: Set.Set ValExpr -> ValExpr -> Bool
        contains set (view -> Vand a) = all (`Set.member` set) (Set.toList a)
        contains set a                = Set.member a set
{-
        isCstrTuples :: [ValExpr] -> [(CstrId, ValExpr)]
        isCstrTuples [] = []
        isCstrTuples (x:xs) = case view x of
                                Viscstr c v -> (c,v) : isCstrTuples xs
                                _           ->         isCstrTuples xs
-}
        sameValExpr :: [(CstrId, ValExpr)] ->  Bool
        sameValExpr []     = False
        sameValExpr (x:xs) = containValExpr x xs
            where
                containValExpr :: (CstrId, ValExpr) -> [(CstrId, ValExpr)] ->  Bool
                containValExpr _      []             = False
                containValExpr (c1,x1) ((c2,x2):cxs) = if x1 == x2 
                                                        then assert (c1 /= c2) True
                                                        else containValExpr (c1,x1) cxs
-}

-- * Sum

-- | Is ValExpr a Sum Expression?
isSum :: ValExprInt -> Bool
isSum (view -> VIntSum{}) = True
isSum _                = False

getSum :: ValExprInt -> FreeSum ValExprInt
getSum (view -> VIntSum s) = s
getSum _ = error "ValExprImpls.hs - getSum - Unexpected ValExpr "

-- | Apply operator sum on the provided sum of value expressions.
-- Preconditions are /not/ checked.
cstrSum ::  FreeSum ValExprInt -> ValExprInt
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the sum of all values
--         special case if the sum is zero, no value is inserted since v == v+0
--    remove all nested sums, since (a+b) + (c+d) == (a+b+c+d)
cstrSum ms =
    cstrSum' $ nonadds <> FMX.flatten sumOfAdds
    where
      (adds, nonadds) = FMX.partitionT isSum ms
      sumOfAdds :: FMX.FreeMonoidX (FMX.FreeMonoidX (SumTerm ValExprInt))
      sumOfAdds = FMX.mapTerms (getSum . summand) adds

-- Sum doesn't contain elements of type VExprSum
cstrSum' :: FreeSum ValExprInt -> ValExprInt
cstrSum' ms =
    let (vals, nonvals) = FMX.partitionT isConst ms
        sumVals = summand $ FMX.foldFMX (FMX.mapTerms (SumTerm . getIntVal . summand) vals)
        retMS = case sumVals of
                    0 -> nonvals                                      -- 0 + x == x
                    _ -> Sum.add (cstrConst (Cint sumVals)) nonvals
    in
        case FMX.toOccurList retMS of
            []         -> cstrConst (Cint 0)                                -- sum of nothing equal zero
            [(term,1)] -> summand term
            _          -> ValExpr (VIntSum retMS)

-- Product

-- | Is ValExpr a Product Expression?
isProduct :: ValExprInt -> Bool
isProduct (view -> VIntProduct{}) = True
isProduct _                    = False

getProduct :: ValExprInt -> FreeProduct ValExprInt
getProduct (view -> VIntProduct p) = p
getProduct _ = error "ValExprImpls.hs - getProduct - Unexpected ValExpr "

-- | Apply operator product on the provided product of value expressions.
-- Be aware that division is not associative for Integer, so only use power >= 0.
-- Preconditions are /not/ checked.
cstrProduct :: forall v . FreeProduct ValExprInt -> ValExprInt
-- implementation details:
-- Properties incorporated
--    at most one value: the value is the product of all values
--         special case if the product is one, no value is inserted since v == v*1
--    remove all nested products, since (a*b) * (c*d) == (a*b*c*d)
cstrProduct ms =
    cstrProduct' $ noprods <> FMX.flatten prodOfProds
    where
      (prods, noprods) = FMX.partitionT isProduct ms
      prodOfProds :: FMX.FreeMonoidX (FMX.FreeMonoidX (ProductTerm ValExprInt))
      prodOfProds = FMX.mapTerms (getProduct . factor) prods

-- Product doesn't contain elements of type VExprProduct
cstrProduct' :: FreeProduct ValExprInt -> ValExprInt
cstrProduct' ms =
    let (vals, nonvals) = FMX.partitionT isConst ms
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
                            _           ->  cstrSum (FMX.fromOccurList [(SumTerm (ValExpr (VIntProduct nonvals)), productVals)])  -- productVals can be 1 -> rewrite possible
            _   ->  let (_, n) = Product.fraction zeros in
                        case FMX.nrofDistinctTerms n of
                            0   ->  cstrConst (Cint 0)      -- 0 * x == 0
                            _   ->  error "Error in model: Division by Zero in Product (via negative power)"
    where
        isZero :: ValExprInt -> Bool
        isZero (view -> VIntConst (Cint 0)) = True
        isZero _                            = False

-- Divide

-- | Apply operator Divide on the provided value expressions.
-- Preconditions are /not/ checked.
cstrDivide :: ValExprInt -> ValExprInt -> ValExprInt
cstrDivide _                          (view -> VIntConst (Cint n)) | n == 0 = error "Error in model: Division by Zero in Divide"
cstrDivide (view ->  VIntConst (Cint t)) (view -> VIntConst (Cint n)) = cstrConst (Cint (t `Boute.div` n) )
cstrDivide vet ven = ValExpr (VIntDivide vet ven)

-- Modulo

-- | Apply operator Modulo on the provided value expressions.
-- Preconditions are /not/ checked.
cstrModulo :: ValExprInt -> ValExprInt -> ValExprInt
cstrModulo _                         (view -> VIntConst (Cint n)) | n == 0 = error "Error in model: Division by Zero in Modulo"
cstrModulo (view -> VIntConst (Cint t)) (view -> VIntConst (Cint n)) = cstrConst (Cint (t `Boute.mod` n) )
cstrModulo vet ven = ValExpr (VIntModulo vet ven)

-- | Apply operator GEZ (Greater Equal Zero) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGEZ :: ValExprInt -> ValExprBool
-- Simplification Values
cstrGEZ (view -> VIntConst (Cint v)) = cstrConst (Cbool (0 <= v))
cstrGEZ (view -> VLength _)       = cstrConst (Cbool True)        -- length of string is always Greater or equal to zero
cstrGEZ ve                        = ValExpr (VGezInt ve)


-- | Apply operator Length on the provided value expression.
-- Preconditions are /not/ checked.
cstrLength :: ValExprString -> ValExprInt
cstrLength (view -> VStringConst (Cstring s)) = cstrConst (Cint (Prelude.toInteger (T.length s)))
cstrLength v                            = ValExpr (VLength v)

-- | Apply operator At on the provided value expressions.
-- Preconditions are /not/ checked.
cstrAt :: ValExprString -> ValExprInt -> ValExprString
cstrAt (view -> VStringConst (Cstring s)) (view -> VIntConst (Cint i)) =
    if i < 0 || i >= Prelude.toInteger (T.length s)
        then error ("Error in model: Accessing string " ++ show s ++ " of length " ++ show (T.length s) ++ " with illegal index "++ show i) 
        else cstrConst (Cstring (T.take 1 (T.drop (fromInteger i) s)))
cstrAt ves vei = ValExpr (VAt ves vei)

-- | Apply operator Concat on the provided sequence of value expressions.
-- Preconditions are /not/ checked.
cstrConcat :: [ValExprString] -> ValExprString
cstrConcat l =
    let n = (mergeVals . flatten . filter (cstrConst (Cstring "") /= ) ) l in
        case Prelude.length n of
           0 -> cstrConst (Cstring "")
           1 -> head n
           _ -> ValExpr (VConcat n)

-- implementation details:
-- Properties incorporated
--    "" ++ x == x          - remove empty strings
--    "a" ++ "b" == "ab"    - concat consecutive string values
--   remove all nested Concats, since (a ++ b) ++ (c ++ d) == (a ++ b ++ c ++ d)

mergeVals :: [ValExprString] -> [ValExprString]
mergeVals []            = []
mergeVals [x]           = [x]
mergeVals ( (view -> VStringConst (Cstring s1)) : (view -> VStringConst (Cstring s2)) : xs) =
                          mergeVals (cstrConst (Cstring (s1 <> s2)): xs)
mergeVals (x1:x2:xs)    = x1 : mergeVals (x2:xs)

flatten :: [ValExprString] -> [ValExprString]
flatten []                       = []
flatten ((view -> VConcat l):xs) = l ++ flatten xs
flatten (x:xs)                   = x : flatten xs

-- | Apply String In Regular Expression operator on the provided value expressions.
-- Preconditions are /not/ checked.
--cstrStrInRe :: ValExpr -> ValExpr -> ValExpr
--cstrStrInRe (view -> Vconst (Cstring s)) (view -> Vconst (Cregex r)) = cstrConst (Cbool (T.unpack s =~ T.unpack (xsd2posix r) ) )
--cstrStrInRe s r                                                      = ValExpr (Vstrinre s r)

{-
-- | Create a call to a predefined function as a value expression.
cstrPredef :: PredefKind -> FuncId -> [ValExpr] -> ValExpr
cstrPredef p f a = ValExpr (Vpredef p f a)
-}

type Valuation = Map.Map Variable Constant

-- TODO ideally we statically match the variable and expr types, see remark at the definition of Variable
data VarModel = VarModel {
    intVars :: Map.Map Variable ValExprInt,
    boolVars :: Map.Map Variable ValExprBool,
    stringVars :: Map.Map Variable ValExprString
    }


assignedExprWithDefault :: Variable -> VarModel -> ValExpr t
assignedExprWithDefault v (VarModel ints bools strings) =  case varType v of
    IntType -> Map.findWithDefault (cstrVar v) v ints
    BoolType -> Map.findWithDefault (cstrVar v) v bools
    StringType -> Map.findWithDefault (cstrVar v) v strings

assignment :: [VarModel -> VarModel] -> VarModel
assignment fs = foldr assign noAssignment fs

class Assignable t where
    assign :: Variable -> ValExpr t -> VarModel -> VarModel
    assignedExpr :: Variable -> VarModel -> Maybe (ValExpr t)

--(:=) = assign

instance Assignable ValExprIntView where
    assign v e m = case varType v of
        IntType -> m {intVars = Map.insert v e (intVars m)}
        _ -> error $ "assigned Integer expression to Variable " ++ show v
    assignedExpr v (VarModel ints bools strings) = case varType v of
        IntType -> Map.lookup v ints
        _ -> error $ "cannot lookup Integer Value for variable " ++ show v


instance Assignable ValExprBoolView where
    assign v e m = case varType v of
        BoolType -> m {boolVars = Map.insert v e (boolVars m)}
        _ -> error $ "assigned Bool expression to Variable " ++ show v
    assignedExpr v (VarModel ints bools strings) = case varType v of
        BoolType -> Map.lookup v bools
        _ -> error $ "cannot lookup Bool Value for variable " ++ show v

instance Assignable ValExprStringView where
    assign v e m = case varType v of
        StringType -> m {stringVars = Map.insert v e (stringVars m)}
        _ -> error $ "assigned String expression to Variable " ++ show v
    assignedExpr v (VarModel ints bools strings) = case varType v of
        StringType -> Map.lookup v strings
        _ -> error $ "cannot lookup String Value for variable " ++ show v

noAssignment :: VarModel
noAssignment = VarModel Map.empty Map.empty Map.empty

instance Show VarModel where
    show (VarModel map) = "{" ++ (List.intercalate ", " showList) ++ "}"
        where
        showList = showAssign <$> Map.toList map
        showAssign (v,e) = show v ++ ":=" ++ show e

evalConst :: Valuation -> (ValExpr t) -> Either String Constant
evalConst valuation = eval . evalConst' valuation

evalConst' :: Valuation -> (ValExpr t) -> (ValExpr t)
evalConst' valuation e = subst (VarModel $ Map.map cstrConst valuation) Map.empty e

-- | Substitute variables by value expressions in a value expression.
--
-- Preconditions are /not/ checked.
--
subst :: Subst e
      => VarModel      -- ^ Map from variables to value expressions.
      -> Map.Map FuncId (FuncDef w t) -- ^ Map from identifiers to their
                                    -- definitions, this is used to replace
                                    -- function calls by their bodies if all
                                    -- the arguments of the function are
                                    -- constant.
      -> ValExpr e                -- ^ Value expression where the
                                    -- substitution will take place.
      -> ValExpr e
--subst ve _ x   | ve == Map.empty = x
subst ve fis x = subst' ve fis (view x)

class Subst e where
    subst' :: VarModel -> Map.Map FuncId (FuncDef w e) -> e -> ValExpr e

instance Subst ValExprIntView where
    subst' :: VarModel -> Map.Map FuncId (FuncDef w e) -> ValExprBoolView -> ValExpr
    subst' _  _   (VIntConst const')          = cstrConst const'
    subst' ve _   (VIntVar vid)               = assignedExprWithDefault vid ve
    --subst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (subst' ve fis . view) vexp)
    subst' ve fis (VIntIte cond vexp1 vexp2)  = cstrITE ( (subst' ve fis . view) cond) ( (subst' ve fis . view) vexp1) ( (subst' ve fis . view) vexp2)
    subst' ve fis (VIntDivide t n)            = cstrDivide ( (subst' ve fis . view) t) ( (subst' ve fis . view) n)
    subst' ve fis (VIntModulo t n)            = cstrModulo ( (subst' ve fis . view) t) ( (subst' ve fis . view) n)
    subst' ve fis (VIntSum s)                 = cstrSum $ FMX.fromOccurListT $ map (first (subst' ve fis . view)) $ FMX.toDistinctAscOccurListT s
    subst' ve fis (VIntProduct p)             = cstrProduct $ FMX.fromOccurListT $ map (first (subst' ve fis . view)) $ FMX.toDistinctAscOccurListT p
    subst' ve fis (VLength vexp)              = cstrLength ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vstrinre s r)           = cstrStrInRe ( (subst' ve fis . view) s) ( (subst' ve fis . view) r)
    --subst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (subst' ve fis . view) vexps)

instance Subst ValExprBoolView where
    subst' :: VarModel -> Map.Map FuncId (FuncDef w e) -> ValExprBoolView -> ValExpr
    subst' _  _   (VBoolConst const')         = cstrConst const'
    subst' ve _   (VBoolVar vid)              = assignedExprWithDefault vid ve
    --subst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (subst' ve fis . view) vexp)
    subst' ve fis (VBoolIte cond vexp1 vexp2)= cstrITE ( (subst' ve fis . view) cond) ( (subst' ve fis . view) vexp1) ( (subst' ve fis . view) vexp2)
    subst' ve fis (VGezInt v)                = cstrGEZ ( (subst' ve fis . view) v)
    subst' ve fis (VEqualInt vexp1 vexp2)    = cstrEqual ( (subst' ve fis . view) vexp1) ( (subst' ve fis . view) vexp2)
    subst' ve fis (VEqualBool vexp1 vexp2)   = cstrEqual ( (subst' ve fis . view) vexp1) ( (subst' ve fis . view) vexp2)
    subst' ve fis (VEqualString vexp1 vexp2) = cstrEqual ( (subst' ve fis . view) vexp1) ( (subst' ve fis . view) vexp2)
    subst' ve fis (VAnd vexps)               = cstrAnd $ Set.map (subst' ve fis . view) vexps
    subst' ve fis (VNot vexp)                = cstrNot ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vstrinre s r)           = cstrStrInRe ( (subst' ve fis . view) s) ( (subst' ve fis . view) r)
    --subst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (subst' ve fis . view) vexps)

instance Subst ValExprStringView where
    subst' :: VarModel -> Map.Map FuncId (FuncDef w) -> ValExprBoolView -> ValExpr
    subst' _  _   (VStringConst const')          = cstrConst const'
    subst' ve _   (VStringVar vid)               = assignedExprWithDefault vid ve
    --subst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (subst' ve fis . view) vexps)
    --subst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (subst' ve fis . view) vexp)
    --subst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (subst' ve fis . view) vexp)
    subst' ve fis (VStringIte cond vexp1 vexp2)  = cstrITE ( (subst' ve fis . view) cond) ( (subst' ve fis . view) vexp1) ( (subst' ve fis . view) vexp2)
    subst' ve fis (VAt s p)                      = cstrAt ( (subst' ve fis . view) s) ( (subst' ve fis . view) p)
    subst' ve fis (VConcat vexps)                = cstrConcat $ map (subst' ve fis . view) vexps
    --subst' ve fis (Vstrinre s r)           = cstrStrInRe ( (subst' ve fis . view) s) ( (subst' ve fis . view) r)
    --subst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (subst' ve fis . view) vexps)

compSubst :: CompSubst t => VarModel -> Map.Map FuncId (FuncDef v t) -> ValExpr t -> ValExpr t
-- compSubst ve _ _ | ve == Map.empty = error "TXS Subst compSubst: variables must be substitute, yet varenv empty\n"
compSubst ve fis x                 = compSubst' ve fis (view x)

class CompSubst e where
    compSubst' :: VarModel -> Map.Map FuncId (FuncDef v e) -> e -> ValExpr e

instance CompSubst ValExprIntView where
    -- | Substitute variables by value expressions in a value expression (change variable kind).
    -- Preconditions are /not/ checked.
    --compSubst' _  _   (Vconst const')          = cstrConst const'
    compSubst' ve _   (VIntVar vid)               = fromMaybe
                                                        (error ("TXS Subst compSubst: incomplete (vid = " ++ show vid ++ "; map = " ++ show ve ++ ")"))
                                                        (assignedExpr vid ve)
    --compSubst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (compSubst' ve fis . view) vexp)
    compSubst' ve fis (VIntIte cond vexp1 vexp2)  = cstrITE ( (compSubst' ve fis . view) cond) ( (compSubst' ve fis . view) vexp1) ( (compSubst' ve fis . view) vexp2)
    compSubst' ve fis (VIntDivide t n)            = cstrDivide ( (compSubst' ve fis . view) t) ( (compSubst' ve fis . view) n)
    compSubst' ve fis (VIntModulo t n)            = cstrModulo ( (compSubst' ve fis . view) t) ( (compSubst' ve fis . view) n)
    compSubst' ve fis (VIntSum s)                 = cstrSum $ FMX.fromOccurListT $ map (first (compSubst' ve fis . view)) $ FMX.toDistinctAscOccurListT s
    compSubst' ve fis (VIntProduct p)             = cstrProduct $ FMX.fromOccurListT $ map (first (compSubst' ve fis . view)) $ FMX.toDistinctAscOccurListT p
    compSubst' ve fis (VLength vexp)           = cstrLength ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vstrinre s r)           = cstrStrInRe ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) r)
    --compSubst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (compSubst' ve fis . view) vexps)

instance CompSubst ValExprBoolView where
    -- | Substitute variables by value expressions in a value expression (change variable kind).
    -- Preconditions are /not/ checked.
    --compSubst' _  _   (Vconst const')          = cstrConst const'
    compSubst' ve _   (VBoolVar vid)               = fromMaybe
                                                        (error ("TXS Subst compSubst: incomplete (vid = " ++ show vid ++ "; map = " ++ show ve ++ ")"))
                                                        (assignedExpr vid ve)
    --compSubst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (compSubst' ve fis . view) vexp)
    compSubst' ve fis (VBoolIte cond vexp1 vexp2) = cstrITE ( (compSubst' ve fis . view) cond) ( (compSubst' ve fis . view) vexp1) ( (compSubst' ve fis . view) vexp2)
    compSubst' ve fis (VGezInt v)                = cstrGEZ ( (compSubst' ve fis . view) v)
    compSubst' ve fis (VEqualInt vexp1 vexp2)     = cstrEqual ( (compSubst' ve fis . view) vexp1) ( (compSubst' ve fis . view) vexp2)
    compSubst' ve fis (VEqualBool vexp1 vexp2)    = cstrEqual ( (compSubst' ve fis . view) vexp1) ( (compSubst' ve fis . view) vexp2)
    compSubst' ve fis (VEqualString vexp1 vexp2)  = cstrEqual ( (compSubst' ve fis . view) vexp1) ( (compSubst' ve fis . view) vexp2)
    compSubst' ve fis (VAnd vexps)                = cstrAnd $ Set.map (compSubst' ve fis . view) vexps
    compSubst' ve fis (VNot vexp)                 = cstrNot ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vstrinre s r)           = cstrStrInRe ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) r)
    --compSubst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (compSubst' ve fis . view) vexps)

instance CompSubst ValExprStringView where
    -- | Substitute variables by value expressions in a value expression (change variable kind).
    -- Preconditions are /not/ checked.
    --compSubst' _  _   (Vconst const')          = cstrConst const'
    compSubst' ve _   (VStringVar vid)               = fromMaybe
                                                        (error ("TXS Subst compSubst: incomplete (vid = " ++ show vid ++ "; map = " ++ show ve ++ ")"))
                                                        (assignedExpr vid ve)
    --compSubst' ve fis (Vfunc fid vexps)        = cstrFunc fis fid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Vcstr cid vexps)        = cstrCstr cid (map (compSubst' ve fis . view) vexps)
    --compSubst' ve fis (Viscstr cid vexp)       = cstrIsCstr cid ( (compSubst' ve fis . view) vexp)
    --compSubst' ve fis (Vaccess cid n p vexp)   = cstrAccess cid n p ( (compSubst' ve fis . view) vexp)
    compSubst' ve fis (VStringIte cond vexp1 vexp2)  = cstrITE ( (compSubst' ve fis . view) cond) ( (compSubst' ve fis . view) vexp1) ( (compSubst' ve fis . view) vexp2)
    compSubst' ve fis (VAt s p)                      = cstrAt ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) p)
    compSubst' ve fis (VConcat vexps)                = cstrConcat $ map (compSubst' ve fis . view) vexps
    --compSubst' ve fis (Vstrinre s r)           = cstrStrInRe ( (compSubst' ve fis . view) s) ( (compSubst' ve fis . view) r)
    --compSubst' ve fis (Vpredef kd fid vexps)   = cstrPredef kd fid (map (compSubst' ve fis . view) vexps)

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
