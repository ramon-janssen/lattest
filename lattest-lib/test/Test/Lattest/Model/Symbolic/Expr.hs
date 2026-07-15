{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Test.Lattest.Model.Symbolic.Expr (
prop_evalSymbolic,
PropEvalSymbolic,
prop_solveSymbolic,
evalTests,
solveTests
)
where

import Lattest.Model.Symbolic.Internal.FreeMonoidX as FM
import Lattest.Model.Symbolic.Expr
import Lattest.Model.Symbolic.Internal.ExprDefs(List (..))
import Lattest.Model.Symbolic.SolveSymPrim
import qualified Lattest.SMT as SMT

import qualified Data.Set as Set
import qualified Debug.Trace as Trace
import qualified Control.Monad as CM
import Test.HUnit
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Data.Constraint.Extras (Has(..))



class ConcreteGenExpr t where
    genExpr :: Int -> Gen (ExprView t)
    shrinkConst :: t -> [t]

instance ConcreteGenExpr Integer where
    genExpr n | n <= 0 = oneof [
        arbitraryVar IntType,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        arbitraryVar IntType,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 Divide subexpr2 subexpr2,
        CM.liftM2 Modulo subexpr2 subexpr2,
        CM.liftM Sum (FM.fromListT <$> genList subexpr2),
        CM.liftM Product (FM.fromListT <$> genList subexprSqrt),
        CM.liftM Length subexpr
        ]
        where
        subexpr :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr2 = genExpr $ (n `div` 2) - 1
        subexpr3 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr3 = genExpr $ (n `div` 3) - 1
        subexprSqrt :: ConcreteGenExpr t => Gen (ExprView t)
        subexprSqrt = genExpr (intSqrt n - 1)
    shrinkConst = shrink

instance ConcreteGenExpr Bool where
    genExpr n | n <= 0 = oneof [
        arbitraryVar BoolType,
        CM.liftM Const arbitrary
        ]
    genExpr n | n > 0 = oneof [
        arbitraryVar BoolType,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 (Equal IntType) subexpr2 subexpr2,
        CM.liftM2 (Equal BoolType) subexpr2 subexpr2,
        CM.liftM2 (Equal StringType) subexpr2 subexpr2,
        CM.liftM GezInt subexpr,
        CM.liftM Not subexpr,
        CM.liftM And (Set.fromList <$> genList subexprSqrt)
        ]
        where
        subexpr :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr = genExpr (n - 1)
        subexpr2 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr2 = genExpr $ (n `div` 2) - 1
        subexpr3 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr3 = genExpr $ (n `div` 3) - 1
        subexprSqrt :: ConcreteGenExpr t => Gen (ExprView t)
        subexprSqrt = genExpr (intSqrt n - 1)
    shrinkConst = shrink

instance ConcreteGenExpr String where
    genExpr n | n <= 0 = oneof [
        arbitraryVar StringType,
        CM.liftM Const stringExpr
        ]
    genExpr n | n > 0 = oneof [
        arbitraryVar StringType,
        CM.liftM Const stringExpr,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM Concat (genList subexprSqrt)
        ]
        where
        subexpr2 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr2 = genExpr $ (n `div` 2) - 1
        subexpr3 :: ConcreteGenExpr t => Gen (ExprView t)
        subexpr3 = genExpr $ (n `div` 3) - 1
        subexprSqrt :: ConcreteGenExpr t => Gen (ExprView t)
        subexprSqrt = genExpr (intSqrt n - 1)
    shrinkConst _ = []
    {--- very crude and fast string shrinking. Should suffice while we don't do anything interesting with strings yet
    shrinkConst "" = []
    shrinkConst [c] = [[]]
    shrinkConst xs = [take (length xs `div` 2) xs, drop (length xs `div` 2) xs]
    -}
charExpr :: Gen Char
charExpr = elements $ ['A'..'Z'] ++ ['a'..'z']
stringExpr :: Gen String
stringExpr = CM.liftM2 (++) (return <$> charExpr) (genList charExpr)

-- generate lists, more conservatively than with listOf, in order to avoid exponential blowup
genList :: Gen a -> Gen [a]
genList g = sized $ \n -> do
    _ <- choose (0, intSqrt n - 1)
    CM.replicateM (intSqrt n) g

intSqrt :: Int -> Int
intSqrt = floor . (sqrt :: Double -> Double) . fromIntegral


arbitraryVar :: Type t -> Gen (ExprView t)
arbitraryVar t =
    let prefix :: Type a -> String
        prefix tp = case tp of
                    IntType -> "i"
                    FloatType -> "f"
                    BoolType -> "b"
                    StringType -> "s"
                    ListType x -> "[" ++ prefix x ++ "]"
                    TupleType x y -> "(" ++ prefix x ++ "," ++ prefix y ++ ")"
    in CM.liftM (\n -> Var $ Variable (prefix t++n) t) (return <$> charExpr)

type PropEvalSymbolic t = Expr t -> Bool

prop_evalSymbolic :: (Eq t, ConcreteEval t) => Expr t -> Bool
prop_evalSymbolic e =
    let l = concreteEval e
        r = symbolicEval e
    --in if l == r then True else Trace.trace ("concrete eval: " ++ show l ++ "\nsymbolic eval: " ++ show r ++ "\n") False
    in l == r

symbolicEval :: Expr t -> Maybe t
symbolicEval = rightToMaybe . eval
    where
    rightToMaybe :: Either a b -> Maybe b
    rightToMaybe (Left _) = Nothing
    rightToMaybe (Right b) = Just b

prop_solveSymbolic :: Expr Bool -> Property
prop_solveSymbolic guard = monadicIO $ do
    mValuation <- run $ SMT.runSMT $ solveGuard (Set.toList $ freeVars guard) guard
    case mValuation of
        Nothing -> return ()
        Just valuation ->
            let val = substConst valuation guard
            in case concreteEval val of
                Nothing -> return () -- we may generate an expression which can have an undefined value, e.g. division by zero, for which the SMT solver may pick an arbitrary valuation
                Just sat -> Trace.trace ("[" ++ show valuation ++ "]" ++ show guard) $ assertWith sat ("Substituting solved value doesn't yield True for [" ++ show valuation ++ "] " ++ show guard)

concreteEval :: ConcreteEval t => Expr t -> Maybe t
concreteEval = concreteEval' . view

class ConcreteEval t where
    concreteEval' :: ExprView t -> Maybe t

instance ConcreteEval Integer where
    concreteEval' (Var _) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Divide e1 e2) = concreteBinOpMaybe (safeZero div) e1 e2
    concreteEval' (Modulo e1 e2) = concreteBinOpMaybe (safeZero mod) e1 e2
    concreteEval' (Length e) = concreteUnaryOp (Prelude.toInteger . length) e
    concreteEval' (Sum es)     = foldOccur (\(concreteEval' . unwrap -> x) i y -> (+) <$> y <*> ((* i) <$> x)) (Just 0) es
    concreteEval' (Product es) = foldOccur (\(concreteEval' . unwrap -> x) i y -> (*) <$> y <*> ((^ i) <$> x)) (Just 0) es

instance ConcreteEval Double where
    concreteEval' (Var _) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (SumFloat es)     = foldOccur (\(concreteEval' . unwrap -> x) i y -> (+) <$> y <*> ((* fromInteger i) <$> x)) (Just 0.0) es
    concreteEval' (ProductFloat es) = foldOccur (\(concreteEval' . unwrap -> x) i y -> (*) <$> y <*> ((^ i) <$> x)) (Just 0.0) es
    concreteEval' (DivideFloat e1 e2) = concreteBinOpMaybe (safeZero (/)) e1 e2

safeZero :: (Num a, Eq a) => (a -> a -> a) -> (a -> a -> Maybe a)
safeZero _ _ 0 = Nothing
safeZero op n m = Just $ n `op` m


instance ConcreteEval Bool where
    concreteEval' (Var _) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Equal t e1 e2) = has @ConcreteEval t $ concreteBinOp (==) e1 e2
    concreteEval' (GezInt e) = concreteUnaryOp (>= 0) e
    concreteEval' (GezFloat e) = concreteUnaryOp (>= 0) e
    concreteEval' (Not e) = concreteUnaryOp not e
    concreteEval' (And es) = and <$> mapM concreteEval' (Set.toList es)
    concreteEval' (LElem t x xs) = has @ConcreteEval t $ (\y (List ys) -> has @Eq t $ y `elem` ys) <$> concreteEval' x <*> concreteEval' xs

instance ConcreteEval String where
    concreteEval' (Var _) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Concat es) = concat <$> mapM concreteEval' es

instance ConcreteEval a => ConcreteEval (List a) where
  concreteEval' = \case
    Var _ -> Nothing
    Const c -> Just c
    Take i xs -> (\j (List ys) -> List $ take (fromInteger j) ys) <$> concreteEval' i <*> concreteEval' xs
    Drop i xs -> (\j (List ys) -> List $ drop (fromInteger j) ys) <$> concreteEval' i <*> concreteEval' xs
    Ite i t e -> concreteIfThenElse i t e
    Cons x xs -> (\y (List ys) -> List $ y:ys) <$> concreteEval' x <*> concreteEval' xs
    Append x y -> (\(List xs) (List ys) -> List $ xs ++ ys) <$> concreteEval' x <*> concreteEval' y

instance (ConcreteEval a, ConcreteEval b) => ConcreteEval (a,b) where
  concreteEval' = \case
    Var _ -> Nothing
    Const c -> Just c
    Ite i t e -> concreteIfThenElse i t e

instance Has ConcreteEval Type where
  has tp k = case tp of
    IntType -> k
    FloatType -> k
    StringType -> k
    BoolType -> k
    ListType t -> has @ConcreteEval t k
    TupleType a b -> has @ConcreteEval a $ has @ConcreteEval b k

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

evalTests :: [Test]
evalTests = [testEvalEmptyProduct, testEvalNegativeModulo]

solveTests :: [Test]
solveTests = [testSolveNegativeModulo]

testEvalExpression :: (Eq a, Show a, ConcreteEval a) => Expr a -> String -> Test
testEvalExpression e msg = TestCase $ assertEqual msg (concreteEval e) (symbolicEval e)

testEvalEmptyProduct :: Test
testEvalEmptyProduct = testEvalExpression (sProduct @Integer []) "empty product evaluation incorrect"

testSolveExpression :: Expr Bool -> Test
testSolveExpression guard = TestCase $ do
    mValuation <- SMT.runSMT $ solveGuard (Set.toList $ freeVars guard) guard
    case mValuation of
        Nothing -> return ()
        Just valuation ->
            let val = substConst valuation guard
            in CM.forM_ (concreteEval val)
                $ \sat -> assertBool ("Substituting solved value doesn't yield True for [" ++ show valuation ++ "] " ++ show guard) sat

testEvalNegativeModulo :: Test
testEvalNegativeModulo = testEvalExpression ((-2) .% (-2)) "negative mod evaluates incorrectly"

testSolveNegativeModulo :: Test
testSolveNegativeModulo = testSolveExpression ((-2) .% (-2) .== sVar (Variable "ix" IntType))

