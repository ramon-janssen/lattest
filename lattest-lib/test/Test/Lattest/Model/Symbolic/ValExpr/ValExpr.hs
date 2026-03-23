{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedLists #-}

module Test.Lattest.Model.Symbolic.ValExpr.ValExpr (
prop_evalSymbolic,
PropEvalSymbolic,
valExprTests
)
where

import Lattest.Model.Symbolic.ValExpr.FreeMonoidX as FM
import Lattest.Model.Symbolic.ValExpr.ValExpr
import Lattest.Model.Symbolic.ValExpr.ValExprDefs(Expr(Expr), allTypes)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Debug.Trace as Trace
import qualified Control.Monad as CM
import Test.HUnit
import Test.QuickCheck

instance (Arbitrary a, ConcreteGenExpr a) => Arbitrary (Expr a) where
    arbitrary = Expr <$> arbitrary
    shrink (view -> e) = Expr <$> shrink e

instance (Arbitrary a, ConcreteGenExpr a) => Arbitrary (ExprView a) where
    arbitrary = sized genExpr
    shrink (Var _) = []
    shrink (Const c) = Const <$> shrinkConst c
    shrink (Ite i t e) = [Ite i' t' e' | (i', t', e') <- shrink (i, t, e)] ++ shrink t ++ shrink e
    shrink (EqualInt e1 e2) = [EqualInt e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ [Const True, Const False]
    shrink (EqualBool e1 e2) = [EqualBool e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ [Const True, Const False]
    shrink (EqualString e1 e2) = [EqualString e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ [Const True, Const False]
    shrink (Divide e1 e2) = [Divide e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ shrink e1
    shrink (Modulo e1 e2) = [Modulo e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ shrink e1 ++ shrink e2
    shrink (Sum es) = [] -- shrinkListExpr (Sum . FM.fromListT) (FM.toListT es)
    shrink (Product es) = [] -- shrinkListExpr (Product . FM.fromListT) (FM.toList es)
    shrink (Length e) = Length <$> shrink e
    shrink (GezInt e) = GezInt <$> shrink e
    shrink (Not e) = [e]
    shrink (And es) = shrinkListExpr (And . Set.fromList) (Set.toList es)
    shrink (At e1 e2) = [At e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ shrink e1
    shrink (Concat es) = Concat <$> shrinkList shrink es

shrinkListExpr :: Arbitrary t1 => (t1 -> t2) -> t1 -> [t2]
shrinkListExpr op es = fmap op (shrink es)

class ConcreteGenExpr t where
    genExpr :: Int -> Gen (ExprView t)
    shrinkConst :: t -> [t]

instance ConcreteGenExpr Integer where
    genExpr 0 = oneof [
        arbitraryVar,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        arbitraryVar,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 Divide subexpr2 subexpr2,
        CM.liftM2 Modulo subexpr2 subexpr2,
        CM.liftM Sum (FM.fromListT <$> listOf subexpr2),
        CM.liftM Product (FM.fromListT <$> listOf subexpr2),
        CM.liftM Length subexpr
        ]
        where
        subexpr :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr2 = genExpr (n `div` 2)
        subexpr3 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr3 = genExpr (n `div` 3)
    shrinkConst = shrink

instance ConcreteGenExpr Bool where
    genExpr 0 = oneof [
        arbitraryVar,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        arbitraryVar,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 EqualInt subexpr2 subexpr2,
        CM.liftM2 EqualBool subexpr2 subexpr2,
        CM.liftM2 EqualString subexpr2 subexpr2,
        CM.liftM GezInt subexpr,
        CM.liftM Not subexpr,
        CM.liftM And (Set.fromList <$> listOf subexpr2)
        ]
        where
        subexpr :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr2 = genExpr (n `div` 2)
        subexpr3 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr3 = genExpr (n `div` 3)
    shrinkConst = shrink

instance ConcreteGenExpr String where
    genExpr 0 = oneof [
        arbitraryVar,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        arbitraryVar,
        CM.liftM Const stringExpr,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 At subexpr2 subexpr2,
        CM.liftM Concat (listOf subexpr2)
        ]
        where
        subexpr :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr2 = genExpr (n `div` 2)
        subexpr3 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr3 = genExpr (n `div` 3)
        stringExpr = listOf $ elements $ ['A'..'Z'] ++ ['a'..'z']
    shrinkConst xs = concat [ removes k n xs | k <- takeWhile (>0) (iterate (`div`2) n) ]
        where
        n = length xs
        removes k n xs
            | k > n     = []
            | null xs2  = [[]]
            | otherwise = xs2 : map (xs1 ++) (removes k (n-k) xs2)
            where
            xs1 = take k xs
            xs2 = drop k xs


prop_symbolicEval :: Expr Integer -> Bool
prop_symbolicEval e = rightToMaybe (eval e) == concreteEval e
    where
    rightToMaybe (Left _) = Nothing
    rightToMaybe (Right x) = Just x
    concreteEval = concreteEval' . view

arbitraryVar = CM.liftM2 (\n t -> Var $ Variable n t) arbitrary (elements allTypes)

type PropEvalSymbolic t = Expr t -> Bool

prop_evalSymbolic :: (Show t, Eq t, ConcreteEval t) => Expr t -> Bool
prop_evalSymbolic e =
    let l = concreteEval e
        r = symbolicEval e
    in if l == r then True else Trace.trace ("concrete eval: " ++ show l ++ "\nsymbolic eval: " ++ show r ++ "\n") False

symbolicEval :: Expr t -> Maybe t
symbolicEval = rightToMaybe . eval
    where
    rightToMaybe :: Either a b -> Maybe b
    rightToMaybe (Left _) = Nothing
    rightToMaybe (Right b) = Just b

concreteEval :: ConcreteEval t => Expr t -> Maybe t
concreteEval = concreteEval' . view

class ConcreteEval t where
    concreteEval' :: ExprView t -> Maybe t

instance ConcreteEval Integer where
    concreteEval' (Var v) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Divide e1 e2) = concreteBinOpMaybe (safeZero div) e1 e2
    concreteEval' (Modulo e1 e2) = concreteBinOpMaybe (safeZero mod) e1 e2
    concreteEval' (Length e) = concreteUnaryOp (Prelude.toInteger . length) e
    concreteEval' (Sum es) = foldOccurList 0 (+) (*) es
    concreteEval' (Product es) = foldOccurList 1 (*) (^) es

safeZero :: (Integer -> Integer -> Integer) -> (Integer -> Integer -> Maybe Integer)
safeZero _ _ 0 = Nothing
safeZero op n m = Just $ n `op` m

foldOccurList :: TermWrapper t => Integer -> (Integer -> Integer -> Integer) -> (Integer -> Integer -> Integer) -> FreeMonoidX (t (ExprView Integer)) -> Maybe Integer
foldOccurList zero add mult monoid = (foldr add zero) <$> sequence (maybeEvalTerm <$> FM.toOccurListT monoid)
    where
    maybeEvalTerm :: (ExprView Integer, Integer) -> Maybe Integer
    maybeEvalTerm (x, n) = case concreteEval' x of
        Just y -> Just (y `mult` n)
        Nothing -> Nothing


instance ConcreteEval Bool where
    concreteEval' (Var v) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (EqualInt e1 e2) = concreteBinOp (==) e1 e2
    concreteEval' (EqualBool e1 e2) = concreteBinOp (==) e1 e2
    concreteEval' (EqualString e1 e2) = concreteBinOp (==) e1 e2
    concreteEval' (GezInt e) = concreteUnaryOp (>= 0) e
    concreteEval' (Not e) = concreteUnaryOp not e
    concreteEval' (And es) = fmap and $ sequence (concreteEval' <$> Set.toList es)

instance ConcreteEval String where
    concreteEval' (Var v) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (At e1 e2) = concreteBinOp (\s n -> drop (fromInteger n) s) e1 e2
    concreteEval' (Concat es) = concat <$> (sequence $ concreteEval' <$> es)

concreteUnaryOp :: (ConcreteEval t1) => (t1 -> t2) -> ExprView t1 -> Maybe t2
concreteUnaryOp op e = do
    x <- concreteEval' e
    return $ op x

concreteBinOp :: (ConcreteEval t1, ConcreteEval t2) => (t1 -> t2 -> t3) -> ExprView t1 -> ExprView t2 -> Maybe t3
concreteBinOp binop e1 e2 = do
    x <- concreteEval' e1
    y <- concreteEval' e2
    return $ x `binop` y

concreteBinOpMaybe :: (ConcreteEval t1, ConcreteEval t2) => (t1 -> t2 -> Maybe t3) -> ExprView t1 -> ExprView t2 -> Maybe t3
concreteBinOpMaybe binop e1 e2 = do
    x <- concreteEval' e1
    y <- concreteEval' e2
    x `binop` y

concreteIfThenElse :: (ConcreteEval t) => ExprView Bool -> ExprView t -> ExprView t -> Maybe t
concreteIfThenElse i t e = do
    cond <- concreteEval' i
    if cond
        then concreteEval' t
        else concreteEval' e

valExprTests :: [Test]
valExprTests = [testEmptyProduct, test1Gez, testGET]

testEmptyProduct :: Test
testEmptyProduct = TestCase $ assertEqual "empty product should be 1" (symbolicEval $ sConst 1) (symbolicEval $ sProduct [])

test1Gez :: Test
test1Gez = TestCase $ assertEqual "1 should be greater or equal to zero" (Just True) (symbolicEval $ sIsNonNegative $ sConst 1)

testGET :: Test
testGET =
    let pvar = Variable "p" IntType
        p = sVar pvar
    in TestCase $ assertEqual ">= should be expressed in terms of >" (p .> 1) (sNot $ 1 .- p .>= 0)
