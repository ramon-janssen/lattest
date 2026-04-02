{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedLists #-}

module Test.Lattest.Model.Symbolic.ValExpr.ValExpr (
prop_evalSymbolic,
PropEvalSymbolic,
prop_solveSymbolic,
evalTests,
solveTests
)
where

import Lattest.Model.Symbolic.ValExpr.FreeMonoidX as FM
import Lattest.Model.Symbolic.ValExpr.ValExpr
import Lattest.Model.Symbolic.ValExpr.ValExprDefs(Expr(Expr), allTypes)
import Lattest.Model.Symbolic.SolveSymPrim
import qualified Lattest.SMT.SMTData as SMT
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Debug.Trace as Trace
import qualified Control.Monad as CM
import Test.HUnit
import Test.QuickCheck
import Test.QuickCheck.Monadic

instance (Arbitrary a, ConcreteGenExpr a, Show a) => Arbitrary (Expr a) where
    arbitrary = Expr <$> arbitrary -- max to avoid large expressions, which will choke the SMT solver
    -- for debugging exponential blowups in Arbitrary generation
    -- arbitrary = ((\e -> Trace.trace ("size " ++ (show $ sizeOf e) ++ " | ") e). Expr) <$> arbitrary
    -- arbitrary = ((\e -> Trace.trace ("expr " ++ show e ++ " | ") e). Expr) <$> arbitrary
    shrink (view -> e) = Expr <$> shrink e

sizeOf :: SizeOf a => Expr a -> Int
sizeOf = sizeOf' . view

sizeOf' :: SizeOf a => ExprView a -> Int
sizeOf' (Var _) = 1
sizeOf' (Const c) = sizeOfTyped c
sizeOf' (Ite i t e) = sizeOf' i + sizeOf' t + sizeOf' t + 1
sizeOf' (EqualInt e1 e2) = sizeOf' e1 + sizeOf' e2 + 1
sizeOf' (EqualBool e1 e2) = sizeOf' e1 + sizeOf' e2 + 1
sizeOf' (EqualString e1 e2) = sizeOf' e1 + sizeOf' e2 + 1
sizeOf' (Divide e1 e2) = sizeOf' e1 + sizeOf' e2 + 1
sizeOf' (Modulo e1 e2) = sizeOf' e1 + sizeOf' e2 + 1
sizeOf' (Sum es) = foldrTerms (\a b -> sizeOf' a + b) 0 es + 1
sizeOf' (Product es) = foldrTerms (\a b -> sizeOf' a + b) 0 es + 1
sizeOf' (Length e) = sizeOf' e + 1
sizeOf' (GezInt e) = sizeOf' e + 1
sizeOf' (Not e) = sizeOf' e + 1
sizeOf' (And es) = (sum $ sizeOf' <$> Set.toList es) + 1
sizeOf' (At e1 e2) = sizeOf' e1 + sizeOf' e2 + 1
sizeOf' (Concat es) = (sum $ sizeOf' <$> es) + 1

class SizeOf t
    where
    sizeOfTyped :: t -> Int

instance SizeOf Integer
    where
    sizeOfTyped _ = 1

instance SizeOf Bool
    where
    sizeOfTyped _ = 1

instance SizeOf String
    where
    sizeOfTyped s = length s

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
    shrink (Concat es) = Concat <$> shrinkList (const []) es

shrinkListExpr :: Arbitrary t1 => (t1 -> t2) -> t1 -> [t2]
shrinkListExpr op es = fmap op (shrink es)

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
        CM.liftM2 EqualInt subexpr2 subexpr2,
        CM.liftM2 EqualBool subexpr2 subexpr2,
        CM.liftM2 EqualString subexpr2 subexpr2,
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
        CM.liftM2 At subexpr2 subexpr2,
        CM.liftM Concat (genList subexprSqrt)
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
    shrinkConst _ = []
    {--- very crude and fast string shrinking. Should suffice while we don't do anything interesting with strings yet
    shrinkConst "" = []
    shrinkConst [c] = [[]]
    shrinkConst xs = [take (length xs `div` 2) xs, drop (length xs `div` 2) xs]
    -}
charExpr = elements $ ['A'..'Z'] ++ ['a'..'z']
stringExpr = CM.liftM2 (++) (return <$> charExpr) (genList charExpr)

-- generate lists, more conservatively than with listOf, in order to avoid exponential blowup
genList :: Gen a -> Gen [a]
genList g = sized $ \n -> do
    n' <- choose (0, intSqrt n - 1)
    CM.replicateM (intSqrt n) g

intSqrt :: Int -> Int
intSqrt = floor . sqrt . fromIntegral

prop_symbolicEval :: Expr Integer -> Bool
prop_symbolicEval e = rightToMaybe (eval e) == concreteEval e
    where
    rightToMaybe (Left _) = Nothing
    rightToMaybe (Right x) = Just x
    concreteEval = concreteEval' . view

arbitraryVar t = 
    let prefix = case t of
                    IntType -> 'i'
                    BoolType -> 'b'
                    StringType -> 's'
                    _ -> '?'
    in CM.liftM (\n -> Var $ Variable (prefix:n) t) (return <$> charExpr)

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

prop_solveSymbolic :: SMT.SMTRef -> Expr Bool -> Property
prop_solveSymbolic smt guard = monadicIO $ do
    mValuation <- run $ SMT.runSMT smt $ solveGuard (Set.toList $ freeVars guard) guard
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
    concreteEval' (At e1 e2) = concreteBinOp mCharAt e1 e2
        where
        mCharAt s n = case s List.!? fromInteger n of
                        Nothing -> ""
                        Just c -> [c]
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

evalTests :: [Test]
evalTests = [testEvalEmptyProduct, testEvalNegativeModulo, testEvalNegativeAt]

solveTests :: [SMT.SMTRef -> Test]
solveTests = [testSolveNegativeModulo, testSolveNegativeAt]

testEvalExpression :: (Eq a, Show a, ConcreteEval a) => Expr a -> String -> Test
testEvalExpression e msg = TestCase $ assertEqual msg (concreteEval e) (symbolicEval e)

testEvalEmptyProduct :: Test
testEvalEmptyProduct = testEvalExpression (sProduct []) "empty product evaluation incorrect"

testSolveExpression :: Expr Bool -> SMT.SMTRef -> Test
testSolveExpression guard smt = TestCase $ do
    mValuation <- SMT.runSMT smt $ solveGuard (Set.toList $ freeVars guard) guard
    case mValuation of
        Nothing -> return ()
        Just valuation ->
            let val = substConst valuation guard
            in case concreteEval val of
                Nothing -> return () -- we may generate an expression which can have an undefined value, e.g. division by zero, for which the SMT solver may pick an arbitrary valuation
                Just sat -> Trace.trace (show valuation) $ assertBool ("Substituting solved value doesn't yield True for [" ++ show valuation ++ "] " ++ show guard) sat

testEvalNegativeModulo :: Test
testEvalNegativeModulo = testEvalExpression ((-2) .% (-2)) "negative mod evaluates incorrectly"

testSolveNegativeModulo :: SMT.SMTRef -> Test
testSolveNegativeModulo = testSolveExpression ((-2) .% (-2) .== sVar (Variable "ix" IntType))

testEvalNegativeAt :: Test
testEvalNegativeAt = testEvalExpression (sConst "abc" .@ -1) "negative At evaluates incorrectly"

testSolveNegativeAt :: SMT.SMTRef -> Test
testSolveNegativeAt = testSolveExpression (sConst "abc" .@ -1 .== sVar (Variable "sx" StringType))
