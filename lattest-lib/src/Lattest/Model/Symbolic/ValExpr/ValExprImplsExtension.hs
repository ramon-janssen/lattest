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
  cstrOr
  -- ** Exclusive or (\|/)
, cstrXor
  -- ** Implies (=>)
, cstrImplies
  -- * Derived Integer operators:
  -- ** Unary Plus
, cstrUnaryPlus
  -- ** Unary Minus = negate single argument
, cstrUnaryMinus
  -- ** Plus = Sum of two terms
, cstrPlus
  -- ** Minus
, cstrMinus
  -- ** Times = Product of two terms
, cstrTimes
  -- ** Absolute value
, cstrAbs
  -- * Derived Integer comparisons
  -- ** Less than (<)
, cstrLT
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
cstrOr :: Set.Set ValExpr -> ValExpr
-- a \/ b == not (not a /\ not b)
cstrOr = cstrNot . cstrAnd . Set.map cstrNot

-- | Apply operator Xor (\\\|/) on the provided set of value expressions.
-- Preconditions are /not/ checked.
cstrXor :: ValExpr -> ValExpr -> ValExpr
cstrXor a b = cstrOr (Set.fromList [ cstrAnd (Set.fromList [a, cstrNot b])
                                   , cstrAnd (Set.fromList [cstrNot a, b])
                                   ])

-- | Apply operator Implies (=>) on the provided value expressions.
-- Preconditions are /not/ checked.
cstrImplies :: ValExpr -> ValExpr -> ValExpr
-- a => b == not a \/ b == not (a /\ not b)
cstrImplies a b = (cstrNot . cstrAnd) (Set.insert a (Set.singleton (cstrNot b)))

-- | Apply unary operator Plus on the provided value expression.
-- Preconditions are /not/ checked.
cstrUnaryPlus :: ValExpr -> ValExpr
cstrUnaryPlus = id

-- | Apply unary operator Minus on the provided value expression.
-- Preconditions are /not/ checked.
cstrUnaryMinus :: ValExpr -> ValExpr
cstrUnaryMinus v = cstrSum (fromOccurListT [(v,-1)])

-- | Apply operator Add on the provided value expressions.
-- Preconditions are /not/ checked.
cstrPlus :: ValExpr -> ValExpr -> ValExpr
cstrPlus a b = cstrSum (fromListT [a,b])

-- | Apply operator Minus on the provided value expressions.
-- Preconditions are /not/ checked.
cstrMinus :: ValExpr -> ValExpr -> ValExpr
cstrMinus a b = cstrSum (fromOccurListT [(a,1),(b,-1)])

-- | Apply operator Times on the provided value expressions.
-- Preconditions are /not/ checked.
cstrTimes :: ValExpr -> ValExpr -> ValExpr
cstrTimes a b = cstrProduct (fromListT [a,b])

-- | Apply operator Absolute value (abs) on the provided value expression.
-- Preconditions are /not/ checked.
cstrAbs :: ValExpr -> ValExpr
cstrAbs a = cstrITE (cstrGEZ a) a (cstrUnaryMinus a)

-- | Apply operator LT (<) on the provided value expression.
-- Preconditions are /not/ checked.
cstrLT :: ValExpr -> ValExpr -> ValExpr
-- a < b <==> a - b < 0 <==> Not ( a - b >= 0 )
cstrLT ve1 ve2 = cstrNot (cstrGEZ (cstrSum (fromOccurListT [(ve1,1),(ve2,-1)])))

-- | Apply operator GT (>) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGT :: ValExpr -> ValExpr -> ValExpr
-- a > b <==> 0 > b - a <==> Not ( 0 <= b - a )
cstrGT ve1 ve2 = cstrNot (cstrGEZ (cstrSum (fromOccurListT [(ve1,-1),(ve2,1)])))

-- | Apply operator LE (<=) on the provided value expression.
-- Preconditions are /not/ checked.
cstrLE :: ValExpr -> ValExpr -> ValExpr
-- a <= b <==> 0 <= b - a
cstrLE ve1 ve2 = cstrGEZ (cstrSum (fromOccurListT [(ve1,-1),(ve2,1)]))

-- | Apply operator GE (>=) on the provided value expression.
-- Preconditions are /not/ checked.
cstrGE :: ValExpr -> ValExpr -> ValExpr
-- a >= b <==> a - b >= 0
cstrGE ve1 ve2 = cstrGEZ (cstrSum (fromOccurListT [(ve1,1),(ve2,-1)]))
