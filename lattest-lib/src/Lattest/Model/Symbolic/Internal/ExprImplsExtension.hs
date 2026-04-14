{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent Symbolic folder.
-}

{-# LANGUAGE FlexibleInstances #-}

module Lattest.Model.Symbolic.Internal.ExprImplsExtension
( -- * Derived Boolean operators
  -- ** Or (\/)
  sOr
, (.&&)
, (.||)
  -- ** Exclusive or (\|/)
, sXor
  -- ** Implies (=>)
, (.=>)
  -- * Derived Integer operators:
  -- ** Unary Minus = negate single argument
, sNeg
  -- ** Plus = Sum of two terms
, (.+)
  -- ** Minus
, (.-)
  -- ** Times = Product of two terms
, (.*)
  -- ** Absolute value
, sAbs
  -- * Derived Integer comparisons
  -- ** Less than (<)
, (.<)
  -- ** Less Equal (<=)
, (.<=)
  -- ** Greater Equal (>=)
, (.>=)
  -- ** Greater Than (>)
, (.>)
)
where

import qualified Data.Set     as Set

import           Lattest.Model.Symbolic.Internal.FreeMonoidX
import           Lattest.Model.Symbolic.Internal.ExprDefs
import           Lattest.Model.Symbolic.Internal.ExprImpls


-- | Apply operator Or (\\\/) on the provided set of value expressions.
-- Preconditions are /not/ checked.
sOr :: Set.Set (Expr Bool) -> Expr Bool
-- a \/ b == not (not a /\ not b)
sOr = sNot . sAnd . Set.map sNot

(.&&) :: Expr Bool -> Expr Bool -> Expr Bool
(.&&) a b = sAnd $ Set.fromList [a,b]

infixr 3 .&&

(.||) :: Expr Bool -> Expr Bool -> Expr Bool
(.||) a b = sOr $ Set.fromList [a,b]

infixr 2 .||

-- | Apply operator Xor (\\\|/) on the provided set of value expressions.
-- Preconditions are /not/ checked.
sXor :: Expr Bool -> Expr Bool -> Expr Bool
sXor a b = sOr (Set.fromList [ sAnd (Set.fromList [a, sNot b])
                                   , sAnd (Set.fromList [sNot a, b])
                                   ])

-- | Apply operator Implies (=>) on the provided value expressions.
-- Preconditions are /not/ checked.
(.=>) :: Expr Bool -> Expr Bool -> Expr Bool
-- a => b == not a \/ b == not (a /\ not b)
(.=>) a b = (sNot . sAnd) (Set.insert a (Set.singleton (sNot b)))

infixr 1 .=>

instance Num (Expr Integer) where
    fromInteger = sConst
    (-) = (.-)
    (+) = (.+)
    (*) = (.*)
    negate = sNeg
    abs = sAbs
    signum x = sIfThenElse (x .< 0) (-1) (sIfThenElse (x .> 0) 1 0)

-- | Apply unary operator Minus on the provided value expression.
-- Preconditions are /not/ checked.
sNeg :: Expr Integer -> Expr Integer
sNeg v = sSum (fromOccurListT [(v,-1)])

-- | Apply operator Add on the provided value expressions.
-- Preconditions are /not/ checked.
(.+) :: Expr Integer -> Expr Integer -> Expr Integer
(.+) a b = sSum (fromListT [a,b])

infixl 6 .+

-- | Apply operator Minus on the provided value expressions.
-- Preconditions are /not/ checked.
(.-) :: Expr Integer -> Expr Integer -> Expr Integer
(.-) a b = sSum (fromOccurListT [(a,1),(b,-1)])

infixl 6 .-

-- | Apply operator Times on the provided value expressions.
-- Preconditions are /not/ checked.
(.*) :: Expr Integer -> Expr Integer -> Expr Integer
(.*) a b = sProduct (fromListT [a,b])

infixl 7 .*

-- | Apply operator Absolute value (abs) on the provided value expression.
-- Preconditions are /not/ checked.
sAbs :: Expr Integer -> Expr Integer
sAbs a = sIfThenElse (sIsNonNegative a) a (sNeg a)

-- | Apply operator LT (<) on the provided value expression.
-- Preconditions are /not/ checked.
(.<) :: Expr Integer -> Expr Integer -> Expr Bool
-- a < b <==> a - b < 0 <==> Not ( a - b >= 0 )
ve1 .< ve2 = sNot $ sIsNonNegative $ sSum $ fromOccurListT [(ve1,1),(ve2,-1)]

infix 4 .<

-- | Apply operator GT (>) on the provided value expression.
-- Preconditions are /not/ checked.
(.>) :: Expr Integer -> Expr Integer -> Expr Bool
-- a > b <==> 0 > b - a <==> Not ( 0 <= b - a )
ve1 .> ve2 = sNot $ sIsNonNegative $ sSum $ fromOccurListT [(ve1,-1),(ve2,1)]

infix 4 .>

-- | Apply operator LE (<=) on the provided value expression.
-- Preconditions are /not/ checked.
(.<=) :: Expr Integer -> Expr Integer -> Expr Bool
-- a <= b <==> 0 <= b - a
ve1 .<= ve2 = sIsNonNegative $ sSum $ fromOccurListT [(ve1,-1),(ve2,1)]

infix 4 .<=

-- | Apply operator GE (>=) on the provided value expression.
-- Preconditions are /not/ checked.
(.>=) :: Expr Integer -> Expr Integer -> Expr Bool
-- a >= b <==> a - b >= 0
ve1 .>= ve2 = sIsNonNegative $ sSum $ fromOccurListT [(ve1,1),(ve2,-1)]

infix 4 .>=
