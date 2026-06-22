{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
module Reference.FreeLatticeSlow (
FreeLatticeSlow,
)

where

import qualified Lattest.Model.Symbolic.Expr as E


import Algebra.Lattice.Free (Free(..), lowerFree)
import Algebra.Lattice.Levitated(Levitated(..))
import Algebra.Lattice(Lattice)
import qualified Algebra.Lattice as L ((/\), (\/))
import Control.Monad(ap)
import Lattest.Model.BoundedMonad (BoundedConfiguration (..), JoinSemiLattice (..), MeetSemiLattice (..), BooleanConfiguration (..))


{-|
    Free distributive lattice, or a positive boolean formula, i.e., a boolean formula with conjunctions and disjunctions over atomic propositions. The two elements 'top' and 'bot' can be interpreted as true and false.
    Behaviourally, this is equivalent to `FreeLatticeCNF`, but the size is not bounded by the normal form.
    This makes it less efficient when repeatedly applying operators, especially 'fmap' and monadic bind '>>='.
-}
newtype FreeLatticeSlow a = FreeLatticeSlow (Levitated (Free a)) deriving (Eq, Functor, Foldable, Lattice)

deriving instance Ord a => Ord (FreeLatticeSlow a)
deriving instance Ord a => Ord (Free a)

{-
-- Conjunction and disjunction on free distributive lattices.
-- note: this is already imlpemented by the JoinSemiLattice instance
(\/) :: FreeLatticeSlow a -> FreeLatticeSlow a -> FreeLatticeSlow a
(\/) = (L.\/)

-- | Conjunction on free distributive lattices.
(/\) :: FreeLatticeSlow a -> FreeLatticeSlow a -> FreeLatticeSlow a
(/\) = (L./\)
-}

{-|
    An FreeLatticeSlow as a state configuration means an automaton is in a state configuration of disjunctions (non-determinism) and conjunctions over states,
    where state configurations top and bottom, or true and false, indicate underspecified and forbidden configurations, respectively.
-}
instance BoundedConfiguration FreeLatticeSlow where
    isForbidden (FreeLatticeSlow Bottom) = True
    isForbidden _ = False
    isUnderspecified (FreeLatticeSlow Top) = True
    isUnderspecified _ = False
    forbidden = FreeLatticeSlow Bottom
    underspecified = FreeLatticeSlow Top

instance Applicative FreeLatticeSlow where
    pure = FreeLatticeSlow . Levitate . Var
    (<*>) = ap

instance Monad FreeLatticeSlow where
    (FreeLatticeSlow Bottom) >>= _ = FreeLatticeSlow Bottom
    (FreeLatticeSlow Top) >>= _ = FreeLatticeSlow Top
    (FreeLatticeSlow (Levitate x)) >>= f = lowerFree f x

instance Show a => Show (FreeLatticeSlow a) where
    show (FreeLatticeSlow Top) = "⊤"
    show (FreeLatticeSlow Bottom) = "⊥"
    show (FreeLatticeSlow (Levitate a)) = show' a
        where
        show' (Var a') = show a'
        show' (x :\/: y) = "(" ++ show' x ++ " ∨ " ++ show' y ++ ")"
        show' (x :/\: y) = "(" ++ show' x ++ " ∧ " ++ show' y ++ ")"

instance JoinSemiLattice (FreeLatticeSlow a) where
    (\/) = (L.\/) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself

instance MeetSemiLattice (FreeLatticeSlow a) where
    (/\) = (L./\) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself

instance BooleanConfiguration FreeLatticeSlow where
    asExpr (FreeLatticeSlow Top) = E.sTrue
    asExpr (FreeLatticeSlow Bottom) = E.sFalse
    asExpr (FreeLatticeSlow (Levitate a)) = asExpr' a
        where
        asExpr' (Var a') = a'
        asExpr' (x :\/: y) = asExpr' x E..|| asExpr' y
        asExpr' (x :/\: y) = asExpr' x E..&& asExpr' y

