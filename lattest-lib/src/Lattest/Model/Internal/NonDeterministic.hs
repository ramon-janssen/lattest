module Lattest.Model.Internal.NonDeterministic (
  NonDet(..),
  nonDet
) where
import qualified Data.Set as Set
import Lattest.Model.BoundedMonad (BoundedConfiguration (..), BooleanConfiguration (..), JoinSemiLattice (..), OrdFunctor (..), OrdMonad (..))
import Lattest.Model.Symbolic.Expr (sOr, sTrue)

-- | Non-deterministic state configuration. This means that an automaton non-deterministically in a number of states, where zero states indicates the forbidden configuration, or in an explicit underspecified configuration.
data NonDet q = NonDet (Set.Set q) | UnderspecNonDet

nonDet :: Ord q => [q] -> NonDet q
nonDet = NonDet . Set.fromList

instance BoundedConfiguration NonDet where
    isForbidden (NonDet s) = Set.null s
    isForbidden _ = False
    isUnderspecified UnderspecNonDet = True
    isUnderspecified _ = False
    forbidden = NonDet Set.empty
    underspecified = UnderspecNonDet

instance OrdFunctor NonDet where
    ordMap f (NonDet ss) = NonDet $ ordMap f ss
    ordMap _ UnderspecNonDet = UnderspecNonDet

instance OrdMonad NonDet where
    ordBind (NonDet ss) f = foldr (\/) (NonDet Set.empty) $ Set.map f ss
    ordBind UnderspecNonDet _ = UnderspecNonDet
    ordReturn s = NonDet $ Set.singleton s

instance Foldable NonDet where
    foldr f q (NonDet qs) = foldr f q qs
    foldr _ q _ = q

instance Show a => Show (NonDet a) where
    show (NonDet a)
        | Set.null a = "⊥"
        | otherwise = show $ Set.toList a
    show UnderspecNonDet = "⊤"

instance Ord a => Eq (NonDet a) where
    UnderspecNonDet == UnderspecNonDet = True
    (NonDet q1) == (NonDet q2) = q1 == q2
    _ == _ = False

instance Ord a => Ord (NonDet a) where
    _ <= UnderspecNonDet = True
    UnderspecNonDet <= _ = False
    (NonDet q1) <= (NonDet q2) = q1 <= q2

instance (Ord a) => JoinSemiLattice (NonDet a) where
    (\/) (NonDet q1) (NonDet q2) = NonDet (Set.union q1 q2)
    (\/) _ _ = UnderspecNonDet -- underspecification acts as top, so is absorbing w.r.t. join

instance BooleanConfiguration NonDet where
    asExpr (NonDet qs) = sOr qs
    asExpr UnderspecNonDet = sTrue

