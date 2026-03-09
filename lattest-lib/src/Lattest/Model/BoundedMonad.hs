{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

{- |
    A /bounded monad/ is a type constructor which represents the observable perspective on the state of an automaton, also called a
    /state configuration/. A system will internally have a state, but this state can not always be observed or inferred for an external viewer. To
    model the difference between internal and observable state, we define automata as having a type of internal state, say q, and
    an observable state configuration over q.
    
    In this module, we define three such state configurations:
    
    * deterministic state configurations, where every behaviour leads to a single state,
    * non-deterministic state configurations, where given observable behaviour may lead to a set of states, and
    * distributive lattices, or positive boolean formulas, where the observable behaviour is expressed as a logical expression over states.
    
    Here, 'observed behaviour' is formally a trace or sequence of observable actions. Thus, after a trace, the system is
    in a state configuration over states. The state configuration is computed by taking transitions, following the monadic interpret 
    of the state configuration. If the automaton does not exhibit a given trace of actions, then the state configuration after
    that trace is either 'forbidden' or 'underspecified'. Here, 'forbidden' expresses that the automaton does not allow the
    given trace, whereas 'underspecified' expresses that the automaton does not specify the trace, hence the trace is allowed.
    
    The name 'bounded monad' is based on bounded lattices, which have a top and bottom element. For more details on the use of top and bottom in
    state configurations, see
    
    * [/Ramon Janssen/, Refinement and partiality for model-based testing (Doctoral dissertation), 2022, Chapter 4](https://repository.ubn.ru.nl/bitstream/handle/2066/285020/285020.pdf)
-}

module Lattest.Model.BoundedMonad (
(<#>),
OrdMonad,
OrdFunctor,
ordReturn,
ordBind,
ordMap,
ordJoin,
-- * State configurations
-- ** Deterministic
Det(..),
-- ** Non-deterministic
NonDet(..),
-- ** Distributive lattice
FreeLattice,
atom,
top,
bot,
-- ** Distributive lattice in CNF
FreeLatticeCNF(FreeLatticeCNF),
-- * Specifiednesss
Specifiedness(..),
BoundedConfiguration,
specifiedness,
forbidden,
underspecified,
isForbidden,
isUnderspecified,
-- ** Auxiliary Specifiedness functions
isAllowed,
isSpecified,
isIndefinite,
isConclusive,
-- ** Utility types
BoundedMonad,
BoundedFunctor,
-- ** General non-determinism
JoinSemiLattice,
MeetSemiLattice,
(\/),
(/\)
)
where

import Algebra.Lattice.Free (Free(..), lowerFree)
import Algebra.Lattice.Levitated(Levitated(..))
import Algebra.Lattice(Lattice)
import qualified Algebra.Lattice as L ((/\), (\/))
import qualified Data.Set as Set
import Control.Monad(ap)

class OrdFunctor f where
    ordMap :: (Ord b) => (a -> b) -> f a -> f b

instance {-# OVERLAPPABLE #-} Functor f => OrdFunctor f where
    ordMap = fmap

(<#>) :: (OrdFunctor f, Ord b) => (a -> b) -> f a -> f b
(<#>) = ordMap

instance OrdMonad Set.Set where
    ordBind s f = Set.unions $ Set.map f s
    ordReturn s = Set.singleton s

class (OrdFunctor m) => OrdMonad m where
    ordReturn :: a -> m a
    ordBind :: (Ord b) => m a -> (a -> m b) -> m b

instance {-# OVERLAPPABLE #-} Monad m => OrdMonad m where
    ordBind = (>>=)
    ordReturn = return

ordJoin :: (Ord a, OrdMonad m) => m (m a) -> m a
ordJoin mma = ordBind mma id

instance OrdFunctor Set.Set where
    ordMap = Set.map

-- | Deterministic state configuration. This means that an automaton is either in a single state, or in an explicit forbidden configuration, or in an explicit underspecified configuration.
data Det q = Det q | ForbiddenDet | UnderspecDet deriving (Ord, Eq)

instance BoundedConfiguration Det where
    isForbidden ForbiddenDet = True
    isForbidden _ = False
    isUnderspecified UnderspecDet = True
    isUnderspecified _ = False
    forbidden = ForbiddenDet
    underspecified = UnderspecDet

instance Functor Det where
    fmap f (Det s) = Det (f s)
    fmap _ UnderspecDet = UnderspecDet
    fmap _ ForbiddenDet = ForbiddenDet
    
instance Applicative Det where
    pure q = Det q
    Det f <*> (Det s) = Det (f s)
    ForbiddenDet <*> _ = ForbiddenDet
    UnderspecDet <*> _ = UnderspecDet
    _ <*> ForbiddenDet = ForbiddenDet
    _ <*> UnderspecDet = UnderspecDet
    
instance Monad Det where
    Det s >>= f = f s
    ForbiddenDet >>= _ = ForbiddenDet
    UnderspecDet >>= _ = UnderspecDet

instance Foldable Det where
    foldr f q (Det q') = f q' q
    foldr _ q _ = q

instance Show a => Show (Det a) where
    show (Det a) = show a
    show ForbiddenDet = "-forbidden-"
    show UnderspecDet = "-underspecified-"


-- | Non-deterministic state configuration. This means that an automaton non-deterministically in a number of states, where zero states indicates the forbidden configuration, or in an explicit underspecified configuration.
data NonDet q = NonDet (Set.Set q) | UnderspecNonDet

instance BoundedConfiguration NonDet where
    isForbidden (NonDet s) = if Set.null s then True else False
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
    show (NonDet a) = show $ Set.toList a
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

{-|
    Free distributive lattice, or a positive boolean formula, i.e., a boolean formula with conjunctions and disjunctions over atomic propositions. The two elements 'top' and 'bot' can be interpreted as true and false.
-}
newtype FreeLattice a = FreeLattice (Levitated (Free a)) deriving (Eq, Functor, Foldable, Lattice)

deriving instance Ord a => Ord (FreeLattice a)
deriving instance Ord a => Ord (Free a)

-- | A single state embedded in a free distributive lattice.
atom :: a -> FreeLattice a
atom = FreeLattice . Levitate . Var

-- | The free distributive lattice element ⊥, or false.
bot :: FreeLattice a
bot = FreeLattice Bottom

-- | The free distributive lattice element ⊤, or true.
top :: FreeLattice a
top = FreeLattice Top

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
instance BoundedConfiguration FreeLattice where
    isForbidden (FreeLattice Bottom) = True
    isForbidden _ = False
    isUnderspecified (FreeLattice Top) = True
    isUnderspecified _ = False
    forbidden = FreeLattice Bottom
    underspecified = FreeLattice Top

instance Applicative FreeLattice where
    pure = atom
    (<*>) = ap

instance Monad FreeLattice where
    (FreeLattice Bottom) >>= _ = FreeLattice Bottom
    (FreeLattice Top) >>= _ = FreeLattice Top
    (FreeLattice (Levitate x)) >>= f = lowerFree f x

instance Show a => Show (FreeLattice a) where
    show (FreeLattice Top) = "⊤"
    show (FreeLattice Bottom) = "⊥"
    show (FreeLattice (Levitate a)) = show' a
        where
        show' (Var a) = show a
        show' (x :\/: y) = "(" ++ show' x ++ " ∨ " ++ show' y ++ ")"
        show' (x :/\: y) = "(" ++ show' x ++ " ∧ " ++ show' y ++ ")"

instance JoinSemiLattice (FreeLattice a) where
    (\/) = (L.\/) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself

instance MeetSemiLattice (FreeLattice a) where
    (/\) = (L./\) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself

{-|
    Free distributive lattice, or a positive boolean formula, in CNF-format. Behaviourally, this is equivalent to the standard `FreeLattice`, but the size is bounded by the normal form.
-}

newtype FreeLatticeCNF a = FreeLatticeCNF (Set.Set (Set.Set a)) deriving  (Eq, Ord, Show)

isCnfBot :: FreeLatticeCNF a -> Bool
isCnfBot (FreeLatticeCNF x) = any Set.null x

isCnfTop :: FreeLatticeCNF a -> Bool
isCnfTop (FreeLatticeCNF x) = Set.null x

instance BoundedConfiguration FreeLatticeCNF where
    isForbidden = isCnfBot
    isUnderspecified = isCnfTop
    forbidden = FreeLatticeCNF $ Set.singleton Set.empty
    underspecified = FreeLatticeCNF $ Set.empty

instance OrdMonad FreeLatticeCNF where
    ordBind (FreeLatticeCNF x) f = FreeLatticeCNF $ cnfJoin $ Set.map (Set.map f1) x
        where
            f1 y = let FreeLatticeCNF z = f y in z
    ordReturn x = FreeLatticeCNF  $ Set.singleton $ Set.singleton x

cnfJoin :: (Ord a) => Set.Set (Set.Set (Set.Set (Set.Set a))) -> Set.Set (Set.Set a)
cnfJoin = reduceAll . Set.map Set.unions . Set.unions . Set.map nAryCartesianProduct
    where
    -- some possible optimizations: 1) don't compare every element to and 2) use the ordering on sets to avoid half of the comparisons, 3) ensure that this ordering is such that absorbing/neutral elements are compared first and avoid more work in that case
    reduceAll sets = Set.filter (not . isProperSupersetOfAny sets) sets

nAryCartesianProduct :: (Ord a) => Set.Set (Set.Set a) -> Set.Set (Set.Set a)
nAryCartesianProduct j = Set.map Set.fromList $ Set.fromList $ sequence $ Set.toList $ Set.map Set.toList j

isProperSupersetOfAny :: Ord a => Set.Set (Set.Set a) -> Set.Set a -> Bool
isProperSupersetOfAny sets a = any (isProperSupersetOf a) (Set.toList sets)
    where
    isProperSupersetOf :: Ord a => Set.Set a -> Set.Set a -> Bool
    isProperSupersetOf set potentialSubset = (potentialSubset `Set.isSubsetOf` set) && not (set `Set.isSubsetOf` potentialSubset)

instance OrdFunctor FreeLatticeCNF where
    ordMap f (FreeLatticeCNF x) = FreeLatticeCNF $ Set.map (Set.map f) x

instance Ord a => JoinSemiLattice (FreeLatticeCNF a) where
    (FreeLatticeCNF x) \/ (FreeLatticeCNF y) = FreeLatticeCNF $ Set.map Set.unions $ nAryCartesianProduct $ Set.fromList [x,y]

instance Ord a => MeetSemiLattice (FreeLatticeCNF a) where
    (FreeLatticeCNF x) /\ (FreeLatticeCNF y) =
        let x' = Set.filter (not . isProperSupersetOfAny y) x
            y' = Set.filter (not . isProperSupersetOfAny x) y
        in FreeLatticeCNF (x' `Set.union` y')

{-|
    Specifiednesss describe wether behaviour (a sequence of actions) is allowed a stateful specification model. 'Forbidden' describes that
    behaviour is not allowed, not is any subsequent behaviour. 'Underspecified' describes that behaviour is allowed and any subsequent
    behaviour is also allowed. 'Indefinite' means that the behaviour is allowed, and subsequent behaviour may be forbidden, underspecified,
    or may again be 'Indefinite'. 
-}
data Specifiedness = Underspecified | Forbidden | Indefinite deriving (Eq, Ord, Show, Read)

{-|
    Specifiedness configurations are state configurations which have a representation for forbidden and underspecified configurations.
-}
class BoundedConfiguration m where
    forbidden :: m t -- ^ The forbidden state configuration. 
    underspecified :: m t -- ^ The underspecified state configuration.
    isForbidden :: m t -> Bool -- ^ Is this state configuration forbidden?
    isUnderspecified :: m t -> Bool -- ^ Is this state configuration underspecified?

-- | Extract the current 'Specifiedness' from a bounded monad.
specifiedness c
    | isForbidden c = Forbidden
    | isUnderspecified c = Underspecified
    | otherwise = Indefinite

-- | Is the configuration a representation of the 'Indefinite' specifiedness?
isIndefinite :: (BoundedConfiguration m) => m t -> Bool
isIndefinite p = specifiedness p == Indefinite

-- | Is the configuration a representation of "definitive", i.e., 'Forbidden' or 'Underspecified'?
isConclusive :: (BoundedConfiguration m) => m t -> Bool
isConclusive p = specifiedness p /= Indefinite

-- | Is the configuration a representation of "allowed", i.e., 'Indefinite' or 'Underspecified'?
isAllowed :: (BoundedConfiguration m) => m t -> Bool
isAllowed = not . isForbidden

-- | Is the configuration a representation of "specified", i.e., 'Indefinite' or 'Forbidden'?
isSpecified :: (BoundedConfiguration m) => m t -> Bool
isSpecified = not . isUnderspecified

-- | Abbreviation for types which are both bounded configurations and Monads.
type BoundedMonad m = (BoundedConfiguration m, OrdMonad m)

-- | Abbreviation for types which are both bounded configurations and Functors.
type BoundedFunctor m = (BoundedConfiguration m, OrdFunctor m)

-- | Semi-lattices with a binary join ('or') operation
class JoinSemiLattice a where
    (\/) :: a -> a -> a

--this would be very sensible but it confuses the compiler greatly. Maybe the UndecidableInstances and Overlapping language extensions don't like each other?
--instance Lattice a => JoinSemiLattice a where
--    join = (L.\/)

-- | Semi-lattices with a binary meet ('and') operation
class MeetSemiLattice a where
    (/\) :: a -> a -> a


