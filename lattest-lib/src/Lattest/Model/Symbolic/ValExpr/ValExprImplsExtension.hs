{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ValExprImplsExtension
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (See LICENSE at root directory of this repository)
--
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- This module Lattest.Model.Symbolic.ValExpr.defines extension of functions on and constructors of value expressions.
--
-----------------------------------------------------------------------------
module Lattest.Model.Symbolic.ValExpr.ValExprImplsExtension
( -- * Derived Boolean operators
  -- ** Or (\/)
  (.||)
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
, cstrLE
  -- ** Greater Equal (>=)
, cstrGE
  -- ** Greater Than (>)
, cstrGT
)
where

import qualified Data.Set     as Set

import           Lattest.Model.Symbolic.ValExpr.FreeMonoidX
import           Lattest.Model.Symbolic.ValExpr.ValExprDefs
import           Lattest.Model.Symbolic.ValExpr.ValExprImpls


-- | Apply operator Or (\\\/) on the provided set of value expressions.
-- Preconditions are /not/ checked.
(.||) :: Set.Set (Expr Bool) -> Expr Bool
-- a \/ b == not (not a /\ not b)
(.||) = sNot . (.&&) . Set.map sNot

-- | Apply operator Xor (\\\|/) on the provided set of value expressions.
-- Preconditions are /not/ checked.
sXor :: Expr Bool -> Expr Bool -> Expr Bool
sXor a b = (.||) (Set.fromList [ (.&&) (Set.fromList [a, sNot b])
                                   , (.&&) (Set.fromList [sNot a, b])
                                   ])

-- | Apply operator Implies (=>) on the provided value expressions.
-- Preconditions are /not/ checked.
(.=>) :: Expr Bool -> Expr Bool -> Expr Bool
-- a => b == not a \/ b == not (a /\ not b)
(.=>) a b = (sNot . (.&&)) (Set.insert a (Set.singleton (sNot b)))

-- | Apply unary operator Minus on the provided value expression.
-- Preconditions are /not/ checked.
sNeg :: Expr Integer -> Expr Integer
sNeg v = sSum (fromOccurListT [(v,-1)])

-- | Apply operator Add on the provided value expressions.
-- Preconditions are /not/ checked.
(.+) :: Expr Integer -> Expr Integer -> Expr Integer
(.+) a b = sSum (fromListT [a,b])

-- | Apply operator Minus on the provided value expressions.
-- Preconditions are /not/ checked.
(.-) :: Expr Integer -> Expr Integer -> Expr Integer
(.-) a b = sSum (fromOccurListT [(a,1),(b,-1)])

-- | Apply operator Times on the provided value expressions.
-- Preconditions are /not/ checked.
(.*) :: Expr Integer -> Expr Integer -> Expr Integer
(.*) a b = sProduct (fromListT [a,b])

-- | Apply operator Absolute value (abs) on the provided value expression.
-- Preconditions are /not/ checked.
sAbs :: Expr Integer -> Expr Integer
sAbs a = sIfThenElse (sIsNonNegative a) a (sNeg a)

-- | Apply operator LT (<) on the provided value expression.
-- Preconditions are /not/ checked.
(.<) :: Expr Integer -> Expr Integer -> Expr Bool
-- a < b <==> a - b < 0 <==> Not ( a - b >= 0 )
(.<) ve1 ve2 = sNot (sIsNonNegative (sSum (fromOccurListT [(ve1,1),(ve2,-1)])))

-- | Apply operator GT (>) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGT :: Expr Integer -> Expr Integer -> Expr Bool
-- a > b <==> 0 > b - a <==> Not ( 0 <= b - a )
cstrGT ve1 ve2 = sNot (sIsNonNegative (sSum (fromOccurListT [(ve1,-1),(ve2,1)])))

-- | Apply operator LE (<=) on the provided value expression.
-- Preconditions are /not/ checked.
cstrLE :: Expr Integer -> Expr Integer -> Expr Bool
-- a <= b <==> 0 <= b - a
cstrLE ve1 ve2 = sIsNonNegative (sSum (fromOccurListT [(ve1,-1),(ve2,1)]))

-- | Apply operator GE (>=) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGE :: Expr Integer -> Expr Integer -> Expr Bool
-- a >= b <==> a - b >= 0
cstrGE ve1 ve2 = sIsNonNegative (sSum (fromOccurListT [(ve1,1),(ve2,-1)]))
