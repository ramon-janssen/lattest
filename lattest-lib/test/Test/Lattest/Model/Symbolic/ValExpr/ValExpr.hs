{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Test.Lattest.Model.Symbolic.ValExpr.ValExpr (

)
where

import Test.QuickCheck
import Lattest.Model.Symbolic.ValExpr.FreeMonoidX as FM
import Lattest.Model.Symbolic.ValExpr.ValExpr
import Lattest.Model.Symbolic.ValExpr.ValExprDefs(Expr(Expr))
import qualified GHC.Exts as GE
import qualified Data.Set as Set
import qualified Control.Monad as CM

instance Arbitrary (Expr a) where
    arbitrary = Expr <$> arbitrary
    shrink (view -> e) = Expr <$> shrink e

instance Arbitrary (ExprView a) where
    arbitrary = sized genExpr
    shrink (Var _) = []
    shrink (Const c) = Const <$> shrink c
    shrink (Ite i t e) = [Ite i' t' e' | (i', t', e') <- shrink (i, t, e)] ++ shrink t ++ shrink e
    shrink (EqualInt e1 e2) = [EqualInt e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ [Const True, Const False]
    shrink (EqualBool e1 e2) = [EqualBool e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ [Const True, Const False]
    shrink (EqualString e1 e2) = [EqualString e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ [Const True, Const False]
    shrink (Divide e1 e2) = [Divide e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ shrink e1
    shrink (Modulo e1 e2) = [Modulo e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ shrink e1 ++ shrink e2
    shrink (Sum es) = shrinkListExpr (Sum . GE.fromList) (GE.toList es)
    shrink (Product es) = shrinkListExpr (Product . GE.fromList) (GE.toList es)
    shrink (Length e) = Length <$> shrink e
    shrink (GezInt e) = GezInt <$> shrink e
    shrink (Not e) = [e]
    shrink (And es) = shrinkListExpr (And . Set.fromList) (Set.toList es)
    shrink (At e1 e2) = [At e1' e2' | (e1', e2') <- shrink (e1, e2) ] ++ shrink e1

shrinkListExpr :: (t1 -> t2) -> t1 -> [t2]
shrinkListExpr op es = fmap op (shrink es)

class ConcreteGenExpr t where
    genExpr :: Int -> Gen (ExprView t)

instance ConcreteGenExpr Integer where
    genExpr 0 = oneof [
        CM.liftM Var arbitrary,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        CM.liftM Var arbitrary,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr2 subexpr2 subexpr2,
        CM.liftM2 Divide subexpr2 subexpr2,
        CM.liftM2 Modulo subexpr2 subexpr2,
        CM.liftM Sum (FM.fromListT <$> listOf subexpr2),
        CM.liftM Product (FM.fromListT <$> listOf subexpr2),
        CM.liftM Length subexpr
        ]
        where
        subexpr :: Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: Gen (ExprView t)
        subexpr2 = genExpr (n `div` 2)

instance ConcreteGenExpr Bool where
    genExpr 0 = oneof [
        CM.liftM Var arbitrary,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        CM.liftM Var arbitrary,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr2 subexpr2 subexpr2,
        CM.liftM2 EqualInt subexpr2 subexpr2,
        CM.liftM2 EqualBool subexpr2 subexpr2,
        CM.liftM2 EqualString subexpr2 subexpr2,
        CM.liftM GezInt subexpr,
        CM.liftM Not subexpr,
        CM.liftM And (Set.fromList <$> listOf subexpr2)
        ]
        where
        subexpr :: Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: Gen (ExprView t)
        subexpr2 = genExpr (n `div` 2)

instance ConcreteGenExpr String where
    genExpr 0 = oneof [
        CM.liftM Var arbitrary,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        CM.liftM Var arbitrary,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr2 subexpr2 subexpr2,
        CM.liftM2 At subexpr2 subexpr2,
        CM.liftM Concat (listOf subexpr2)
        ]
        where
        subexpr :: Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: Gen (ExprView t)
        subexpr2 = genExpr (n `div` 2)

prop_symbolicEval :: Expr Integer -> Bool
prop_symbolicEval e = rightToMaybe (eval e) == concreteEval e
    where
    rightToMaybe (Left _) = Nothing
    rightToMaybe (Right x) = Just x
    concreteEval = concreteEval' . view

class ConcreteEval t where
    concreteEval' :: ExprView t -> Maybe t

instance ConcreteEval Integer where
    concreteEval' (Var v) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Divide e1 e2) = concreteBinOp div e1 e2
    concreteEval' (Modulo e1 e2) = concreteBinOp mod e1 e2
    concreteEval' (Length e) = concreteUnaryOp (Prelude.toInteger . length) e
    concreteEval' (Sum es) = concreteBinOp (+) e1 e2
    concreteEval' (Product es) = concreteBinOp (*) e1 e2

instance ConcreteEval Bool where
    concreteEval' (Var v) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (EqualInt e1 e2) = concreteBinOp (==) e1 e2
    concreteEval' (EqualBool e1 e2) = concreteBinOp (==) e1 e2
    concreteEval' (EqualString e1 e2) = concreteBinOp (==) e1 e2
    concreteEval' (GezInt e) = concreteUnaryOp (>= 0) e
    concreteEval' (Not e) = concreteUnaryOp not e
    concreteEval' (And e1 e2) = concreteBinOp (&&) e1 e2

instance ConcreteEval String where
    concreteEval' (Var v) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (At e1 e2) = concreteBinOp (flip drop) e1 e2

concreteUnaryOp :: (ConcreteEval t1) => (t1 -> t2) -> ExprView t1 -> Maybe t2
concreteUnaryOp op e = do
    x <- concreteEval' e
    return $ op x

concreteBinOp :: (ConcreteEval t1, ConcreteEval t2) => (t1 -> t2 -> t3) -> ExprView t1 -> ExprView t2 -> Maybe t3
concreteBinOp binop e1 e2 = do
    x <- concreteEval' e1
    y <- concreteEval' e2
    return $ x `binop` y

concreteIfThenElse :: (ConcreteEval t) => ExprView Bool -> ExprView t -> ExprView t -> Maybe t
concreteIfThenElse i t e = do
    cond <- concreteEval' i
    if cond
        then concreteEval' t
        else concreteEval' e

