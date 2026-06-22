{-# LANGUAGE StandaloneDeriving #-}
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
newtype FreeLatticeSlow a = FreeLattice (Levitated (Free a)) deriving (Eq, Functor, Foldable, Lattice)

deriving instance Ord a => Ord (FreeLatticeSlow a)
deriving instance Ord a => Ord (Free a)

{-
-- Conjunction and disjunction on free distributive lattices.
-- note: this is already imlpemented by the JoinSemiLattice instance
(\/) :: FreeLattice a -> FreeLattice a -> FreeLattice a
(\/) = (L.\/)

-- | Conjunction on free distributive lattices.
(/\) :: FreeLattice a -> FreeLattice a -> FreeLattice a
(/\) = (L./\)
-}

{-|
    An FreeLattice as a state configuration means an automaton is in a state configuration of disjunctions (non-determinism) and conjunctions over states,
    where state configurations top and bottom, or true and false, indicate underspecified and forbidden configurations, respectively.
-}
instance BoundedConfiguration FreeLatticeSlow where
    isForbidden (FreeLattice Bottom) = True
    isForbidden _ = False
    isUnderspecified (FreeLattice Top) = True
    isUnderspecified _ = False
    forbidden = FreeLattice Bottom
    underspecified = FreeLattice Top

instance Applicative FreeLatticeSlow where
    pure = FreeLattice . Levitate . Var
    (<*>) = ap

instance Monad FreeLatticeSlow where
    (FreeLattice Bottom) >>= _ = FreeLattice Bottom
    (FreeLattice Top) >>= _ = FreeLattice Top
    (FreeLattice (Levitate x)) >>= f = lowerFree f x

instance Show a => Show (FreeLatticeSlow a) where
    show (FreeLattice Top) = "⊤"
    show (FreeLattice Bottom) = "⊥"
    show (FreeLattice (Levitate a)) = show' a
        where
        show' (Var a') = show a'
        show' (x :\/: y) = "(" ++ show' x ++ " ∨ " ++ show' y ++ ")"
        show' (x :/\: y) = "(" ++ show' x ++ " ∧ " ++ show' y ++ ")"

instance JoinSemiLattice (FreeLatticeSlow a) where
    (\/) = (L.\/) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself

instance MeetSemiLattice (FreeLatticeSlow a) where
    (/\) = (L./\) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself

instance BooleanConfiguration FreeLatticeSlow where
    asExpr (FreeLattice Top) = E.sTrue
    asExpr (FreeLattice Bottom) = E.sFalse
    asExpr (FreeLattice (Levitate a)) = asExpr' a
        where
        asExpr' (Var a') = a'
        asExpr' (x :\/: y) = asExpr' x E..|| asExpr' y
        asExpr' (x :/\: y) = asExpr' x E..&& asExpr' y

