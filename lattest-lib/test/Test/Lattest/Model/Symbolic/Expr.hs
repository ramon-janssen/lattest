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
import Lattest.Model.Symbolic.SolveSymPrim
import qualified Lattest.SMT as SMT

import qualified Data.Set as Set
import qualified Debug.Trace as Trace
import qualified Control.Monad as CM
import Test.HUnit
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Data.Constraint.Extras (Has(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (Expr (..))
import qualified Data.Dependent.Map as DMap
import Data.SBV (RCSet(..))



class ConcreteGenExpr t where
    genExpr :: Int -> Gen (ExprView t)
    shrinkConst :: t -> [t]

instance ConcreteGenExpr Integer where
    genExpr n | n <= 0 = oneof [
        arbitraryVar IntType,
        CM.liftM Const arbitrary
        ]
    genExpr n = oneof [
        arbitraryVar IntType,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 Divide subexpr2 subexpr2,
        CM.liftM2 Modulo subexpr2 subexpr2,
        CM.liftM Sum (FM.fromListT <$> genList subexpr2),
        CM.liftM Product (FM.fromListT <$> genList subexprSqrt)
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
    genExpr n = oneof [
        arbitraryVar BoolType,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3,
        CM.liftM2 (Equal IntType) subexpr2 subexpr2,
        CM.liftM2 (Equal BoolType) subexpr2 subexpr2,
        CM.liftM2 (Equal CharType) subexpr2 subexpr2,
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

instance ConcreteGenExpr Char where
    genExpr n | n <= 0 = oneof [
        arbitraryVar CharType,
        CM.liftM Const arbitrary
        ]
    genExpr n = oneof [
        arbitraryVar CharType,
        CM.liftM Const arbitrary,
        CM.liftM3 Ite subexpr3 subexpr3 subexpr3
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
                    CharType -> "c"
                    ListType x -> "[" ++ prefix x ++ "]"
                    SetType x -> "{" ++ prefix x ++ "}"
                    TupleType x y -> "(" ++ prefix x ++ "," ++ prefix y ++ ")"
                    SumType x y -> "<" ++ prefix x ++ "," ++ prefix y ++ ">"
    in CM.liftM (\n -> Var $ Variable (prefix t++n) t) (return <$> charExpr)

type PropEvalSymbolic t = Expr t -> Bool

-- If you squint a bit, this is really just two interpreters (`concreteEval'` defined below, and `reduce` defined in lattest-lib),
-- that are defined almost identically, and then a check whether they give the same result.
-- Does it really give us anything? Is it worth maintaining two interpreters?
--  - A person who did not feel like updating this interpreter after a large update to Expr
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
    concreteEval' (First _ x) = fst <$> concreteEval' x
    concreteEval' (Second _ x) = snd <$> concreteEval' x
    concreteEval' (Head xs) = head <$> concreteEval' xs
    concreteEval' (Either a b c d e) = concreteEither a b c d e
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Divide e1 e2) = concreteBinOpMaybe (safeZero div) e1 e2
    concreteEval' (Modulo e1 e2) = concreteBinOpMaybe (safeZero mod) e1 e2
    concreteEval' (Length _ e) = concreteUnaryOp (Prelude.toInteger . length) e
    concreteEval' (Sum es)     = foldOccur (\(concreteEval' . unwrap -> x) i y -> (+) <$> y <*> ((* i) <$> x)) (Just 0) es
    concreteEval' (Product es) = foldOccur (\(concreteEval' . unwrap -> x) i y -> (*) <$> y <*> ((^ i) <$> x)) (Just 0) es

instance ConcreteEval Double where
    concreteEval' (Var _) = Nothing
    concreteEval' (Const c) = Just c
    concreteEval' (First _ x) = fst <$> concreteEval' x
    concreteEval' (Second _ x) = snd <$> concreteEval' x
    concreteEval' (Head xs) = head <$> concreteEval' xs
    concreteEval' (Either a b c d e) = concreteEither a b c d e
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
    concreteEval' (First _ x) = fst <$> concreteEval' x
    concreteEval' (Second _ x) = snd <$> concreteEval' x
    concreteEval' (Head xs) = head <$> concreteEval' xs
    concreteEval' (Either a b c d e) = concreteEither a b c d e
    concreteEval' (Ite i t e) = concreteIfThenElse i t e
    concreteEval' (Equal t e1 e2) = has @ConcreteEval t $ concreteBinOp (==) e1 e2
    concreteEval' (GezInt e) = concreteUnaryOp (>= 0) e
    concreteEval' (GezFloat e) = concreteUnaryOp (>= 0) e
    concreteEval' (Not e) = concreteUnaryOp not e
    concreteEval' (And es) = and <$> mapM concreteEval' (Set.toList es)
    concreteEval' (LElem t x xs) = has @ConcreteEval t $ (\y ys -> has @Eq t $ y `elem` ys) <$> concreteEval' x <*> concreteEval' xs
    concreteEval' (SElem t x xs) = withExprConstraints t $ has @ConcreteEval t $ (\y ys -> has @Eq t $ case ys of
      RegularSet ys' -> y `Set.member` ys'
      ComplementSet ys' -> not $ y `Set.member` ys') <$> concreteEval' x <*> concreteEval' xs

instance ConcreteEval Char where
  concreteEval' (Var _) = Nothing
  concreteEval' (Const c) = Just c
  concreteEval' (First _ x) = fst <$> concreteEval' x
  concreteEval' (Second _ x) = snd <$> concreteEval' x
  concreteEval' (Head xs) = head <$> concreteEval' xs
  concreteEval' (Either a b c d e) = concreteEither a b c d e
  concreteEval' (Ite i t e) = concreteIfThenElse i t e

instance ConcreteEval [a] where
  concreteEval' = \case
    Var _ -> Nothing
    Const c -> Just c
    First _ x -> fst <$> concreteEval' x
    Second _ x -> snd <$> concreteEval' x
    Either a b c d e -> concreteEither a b c d e
    Head xs -> head <$> concreteEval' xs
    Concat xs -> concat <$> concreteEval' xs
    Tail xs -> tail <$> concreteEval' xs
    Take i xs -> take . fromInteger <$> concreteEval' i <*> concreteEval' xs
    Drop i xs -> drop . fromInteger <$> concreteEval' i <*> concreteEval' xs
    Ite i t e -> concreteIfThenElse i t e
    Cons x xs -> has @ExprType x $ has @ConcreteEval (typeOf' x) $ (:) <$> concreteEval' x <*> concreteEval' xs
    Append x y -> (++) <$> concreteEval' x <*> concreteEval' y
    Map v f xs -> has @ExprType f $ has @ConcreteEval (typeOf' f) $ do
      ys <- concreteEval' xs
      traverse (\y -> concreteEval' $ view $ subst (VarModel $ DMap.singleton v $ Expr $ Const y) $ Expr f) ys

instance ConcreteEval (a,b) where
  concreteEval' = \case
    Var _ -> Nothing
    Const c -> Just c
    First _ x -> fst <$> concreteEval' x
    Second _ x -> snd <$> concreteEval' x
    Head xs -> head <$> concreteEval' xs
    Either a b c d e -> concreteEither a b c d e
    Ite i t e -> concreteIfThenElse i t e
    Pair a b -> has @ExprType a $ has @ExprType b $ has @ConcreteEval (typeOf' a) $ has @ConcreteEval (typeOf' b) $ (,) <$> concreteEval' a <*> concreteEval' b
instance ConcreteEval (Either a b) where
  concreteEval' = \case
    Var _ -> Nothing
    Const c -> Just c
    First _ x -> fst <$> concreteEval' x
    Head xs -> head <$> concreteEval' xs
    Second _ x -> snd <$> concreteEval' x
    Either a b c d e -> concreteEither a b c d e
    Ite i t e -> concreteIfThenElse i t e
    ELeft x -> has @ExprType x $ has @ConcreteEval (typeOf' x) $ Left <$> concreteEval' x
    ERight x -> has @ExprType x $ has @ConcreteEval (typeOf' x) $ Right <$> concreteEval' x

instance ConcreteEval (SMT.RCSet a) where
  concreteEval' = \case
    Var _ -> Nothing
    Const c -> Just c
    First _ x -> fst <$> concreteEval' x
    Head xs -> head <$> concreteEval' xs
    Second _ x -> snd <$> concreteEval' x
    Either a b c d e -> concreteEither a b c d e
    Ite i t e -> concreteIfThenElse i t e
    SInsert x xs -> has @ConcreteEval (has @ExprType x $ typeOf' x) $ case concreteEval' xs of
      Nothing -> Nothing
      Just (RegularSet ys)    -> RegularSet    . flip Set.insert ys <$> concreteEval' x
      Just (ComplementSet ys) -> ComplementSet . flip Set.delete ys <$> concreteEval' x


instance Has ConcreteEval Type where
  has tp k = case tp of
    IntType -> k
    FloatType -> k
    CharType -> k
    BoolType -> k
    ListType _ -> k
    SetType _ -> k
    TupleType _ _ -> k
    SumType _ _ -> k

concreteUnaryOp :: (t1 -> t2) -> ExprView t1 -> Maybe t2
concreteUnaryOp op e = has @ExprType e $ has @ConcreteEval (typeOf' e) $ do
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

concreteEither :: (ConcreteEval t) => Variable a -> Variable b -> ExprView t -> ExprView t -> ExprView (Either a b) -> Maybe t
concreteEither vl vr l r x = has @ExprType x $ case typeOf' x of
  SumType ta tb -> case concreteEval' x of
    Nothing -> Nothing
    Just (Left y) -> concreteEval' $ view $ subst (VarModel $ DMap.singleton vl $ Expr $ withExprConstraints ta Const y) $ Expr l
    Just (Right y) -> concreteEval' $ view $ subst (VarModel $ DMap.singleton vr $ Expr $ withExprConstraints tb Const y) $ Expr r

evalTests :: [Test]
evalTests = [testEvalEmptyProduct, testEvalNegativeModulo]

solveTests :: [Test]
solveTests = [testSolveNegativeModulo, testSolveTwiceInSession]

-- | Solving two satisfiable guards within a single SMT run session
testSolveTwiceInSession :: Test
testSolveTwiceInSession = TestCase $ do
    let v = Variable "j" IntType
        guard = sVar v .== sConst (41 :: Integer)
    (firstSolve, secondSolve) <- SMT.runSMT $ do
        a <- solveGuard [SMT.Some v] guard
        b <- solveGuard [SMT.Some v] guard
        return (a, b)
    let valueOf mVal = (DMap.lookup v . runValuation) =<< mVal
    assertEqual "first solve of j == 41 in a session"  (Just (Val 41)) (valueOf firstSolve)
    assertEqual "second solve of j == 41 in the same session" (Just (Val 41)) (valueOf secondSolve)

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

