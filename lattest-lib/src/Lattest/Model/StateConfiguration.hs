{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
    A /state configuration/ is a type constructor which represents the observable perspective on the state of an automaton. A
    system will internally have a state, but this state can not always be observed or inferred for an external viewer. To model
    the difference between internal and observable state, we define automata as having a type of internal state, say q, and
    an observable state configuration over q.
    
    In this module, we define three such state configurations:
    
    * deterministic state configurations, where every behaviour leads to a single state,
    * non-deterministic state configurations, where given observable behaviour may lead to a set of states, and
    * distributive lattices, or positive boolean formulas, where the observable behaviour is expressed as a logical expression over states.
    
    Here, 'observed behaviour' is formally a trace or sequence of observable actions. Thus, after a trace, the system is
    in a state configuration over states. The state configuration is computed by taking transitions, following the monadic semantics 
    of the state configuration. If the automaton does not exhibit a given trace of actions, then the state configuration after
    that trace is either 'forbidden' or 'underspecified'. Here, 'forbidden' expresses that the automaton does not allow the
    given trace, whereas 'underspecified' expresses that the automaton does not specify the trace, hence the trace is allowed.
    
    For more details see
    
    * [/Ramon Janssen/, Refinement and partiality for model-based testing (Doctoral dissertation), 2022, Chapter 4](https://repository.ubn.ru.nl/bitstream/handle/2066/285020/285020.pdf)
-}

module Lattest.Model.StateConfiguration (
-- * State configurations
-- ** Deterministic
DetState(..),
-- ** Non-deterministic
NonDetState(..),
-- ** Distributive lattice
FDL,
atom,
top,
bot,
(\/),
(/\),
-- * Permissions
Permission(..),
PermissionConfiguration,
permission,
forbidden,
underspecified,
isForbidden,
isUnderspecified,
-- ** Auxiliary Permission functions
isAllowed,
isSpecified,
isIndefinite,
isConclusive,
-- ** Utility types
StateConfiguration,
PermissionApplicative,
PermissionFunctor,
-- ** General non-determinism
JoinSemiLattice,
join
)
where

import Algebra.Lattice.Free (Free(..), lowerFree)
import Algebra.Lattice.Levitated(Levitated(..))
import Algebra.Lattice(Lattice)
import qualified Algebra.Lattice as L ((/\), (\/))
import qualified Data.Set as Set
import Control.Monad(ap)

-- | Deterministic state configuration. This means that an automaton is either in a single state, or in an explicit forbidden configuration, or in an explicit underspecified configuration.
data DetState q = Det q | ForbiddenDet | UnderspecDet

instance PermissionConfiguration DetState where
    isForbidden ForbiddenDet = True
    isForbidden _ = False
    isUnderspecified UnderspecDet = True
    isUnderspecified _ = False
    forbidden = ForbiddenDet
    underspecified = UnderspecDet

instance Functor DetState where
    fmap f (Det s) = Det (f s)
    fmap _ UnderspecDet = UnderspecDet
    fmap _ ForbiddenDet = ForbiddenDet
    
instance Applicative DetState where
    pure q = Det q
    Det f <*> (Det s) = Det (f s)
    ForbiddenDet <*> _ = ForbiddenDet
    UnderspecDet <*> _ = UnderspecDet
    _ <*> ForbiddenDet = ForbiddenDet
    _ <*> UnderspecDet = UnderspecDet
    
instance Monad DetState where
    Det s >>= f = f s
    ForbiddenDet >>= _ = ForbiddenDet
    UnderspecDet >>= _ = UnderspecDet

instance Foldable DetState where
    foldr f q (Det q') = f q' q
    foldr _ q _ = q

instance Show a => Show (DetState a) where
    show (Det a) = show a
    show ForbiddenDet = "-forbidden-"
    show UnderspecDet = "-underspecified-"


-- | Non-deterministic state configuration. This means that an automaton non-deterministically in a number of states, where zero states indicates the forbidden configuration, or in an explicit underspecified configuration.
data NonDetState q = NonDet [q] | UnderspecNonDet

instance PermissionConfiguration NonDetState where
    isForbidden (NonDet []) = True
    isForbidden _ = False
    isUnderspecified UnderspecNonDet = True
    isUnderspecified _ = False
    forbidden = NonDet []
    underspecified = UnderspecNonDet

instance Functor NonDetState where
    fmap f (NonDet ss) = NonDet $ fmap f ss
    fmap _ UnderspecNonDet = UnderspecNonDet
    
instance Applicative NonDetState where
    pure s = NonDet [s]
    NonDet fs <*> NonDet ss = NonDet (fs <*> ss)
    UnderspecNonDet <*> _ = UnderspecNonDet
    _ <*> UnderspecNonDet = UnderspecNonDet
    
instance Monad NonDetState where
    NonDet ss >>= f = foldr join (NonDet []) $ fmap f ss  
    UnderspecNonDet >>= _ = UnderspecNonDet

instance Foldable NonDetState where
    foldr f q (NonDet qs) = foldr f q qs
    foldr _ q _ = q

instance Show a => Show (NonDetState a) where
    show (NonDet a) = show a
    show UnderspecNonDet = "⊤"

instance Ord a => Eq (NonDetState a) where
    UnderspecNonDet == UnderspecNonDet = True
    (NonDet q1) == (NonDet q2) = Set.fromList q1 == Set.fromList q2
    _ == _ = False

instance Ord a => Ord (NonDetState a) where
    _ <= UnderspecNonDet = True
    UnderspecNonDet <= _ = False
    (NonDet q1) <= (NonDet q2) = Set.fromList q1 <= Set.fromList q2

instance JoinSemiLattice (NonDetState a) where
    join (NonDet q1) (NonDet q2) = NonDet (q1 ++ q2)
    join _ _ = UnderspecNonDet -- underspecification acts as top, so is absorbing w.r.t. join

{-|
    Free distributive lattice, or a positive boolean formula, i.e., a boolean formula with conjunctions and disjunctions over atomic propositions. The two elements 'top' and 'bot' can be interpreted as true and false.
-}
newtype FDL a = FDL (Levitated (Free a)) deriving (Eq, Functor, Foldable, Lattice)

-- | A single state embedded in a free distributive lattice.
atom :: a -> FDL a
atom = FDL . Levitate . Var

-- | The free distributive lattice element ⊥, or false.
bot :: FDL a
bot = FDL Bottom

-- | The free distributive lattice element ⊤, or true.
top :: FDL a
top = FDL Top

-- | Disjunction on free distributive lattices.
(\/) :: FDL a -> FDL a -> FDL a
(\/) = (L.\/)

-- | Conjunction on free distributive lattices.
(/\) :: FDL a -> FDL a -> FDL a
(/\) = (L./\)

{-|
    An FDL as a state configuration means an automaton is in a state configuration of disjunctions (non-determinism) and conjunctions over states,
    where state configurations top and bottom, or true and false, indicate underspecified and forbidden configurations, respectively.
-}
instance PermissionConfiguration FDL where
    isForbidden (FDL Bottom) = True
    isForbidden _ = False
    isUnderspecified (FDL Top) = True
    isUnderspecified _ = False
    forbidden = FDL Bottom
    underspecified = FDL Top

instance Applicative FDL where
    pure = atom
    (<*>) = ap

instance Monad FDL where
    (FDL Bottom) >>= _ = FDL Bottom
    (FDL Top) >>= _ = FDL Top
    (FDL (Levitate x)) >>= f = lowerFree f x

instance Show a => Show (FDL a) where
    show (FDL Top) = "⊤"
    show (FDL Bottom) = "⊥"
    show (FDL (Levitate a)) = show' a
        where
        show' (Var a) = show a
        show' (x :\/: y) = "(" ++ show' x ++ " ∨ " ++ show' y ++ ")"
        show' (x :/\: y) = "(" ++ show' x ++ " ∧ " ++ show' y ++ ")"

instance JoinSemiLattice (FDL a) where
    join = (L.\/) -- it should be possible to generalize this to arbitrary instances, see remark below the JoinSemiLattice class itself 

{-|
    Permissions describe wether behaviour (a sequence of actions) is allowed a stateful specification model. 'Forbidden' describes that
    behaviour is not allowed, not is any subsequent behaviour. 'Underspecified' describes that behaviour is allowed and any subsequent
    behaviour is also allowed. 'Indefinite' means that the behaviour is allowed, and subsequent behaviour may be forbidden, underspecified,
    or may again be 'Indefinite'. 
-}
data Permission = Underspecified | Forbidden | Indefinite deriving (Eq, Ord, Show, Read)

{-|
    Permission configurations are state configurations which have a representation for forbidden and underspecified configurations.
-}
class PermissionConfiguration m where
    forbidden :: m t -- ^ The forbidden state configuration. 
    underspecified :: m t -- ^ The underspecified state configuration.
    isForbidden :: m t -> Bool -- ^ Is this state configuration forbidden?
    isUnderspecified :: m t -> Bool -- ^ Is this state configuration underspecified?

-- | Extract the current 'Permission' from a permission configuration.
permission c
    | isForbidden c = Forbidden
    | isUnderspecified c = Underspecified
    | otherwise = Indefinite

-- | Is the configuration a representation of the 'Indefinite' permission?
isIndefinite :: (PermissionConfiguration m) => m t -> Bool
isIndefinite p = permission p == Indefinite

-- | Is the configuration a representation of a "definitive" permission, i.e., 'Forbidden' or 'Underspecified'?
isConclusive :: (PermissionConfiguration m) => m t -> Bool
isConclusive p = permission p /= Indefinite

-- | Is the configuration a representation of an "allowed" permission, i.e., 'Indefinite' or 'Underspecified'?
isAllowed :: (PermissionConfiguration m) => m t -> Bool
isAllowed = not . isForbidden

-- | Is the configuration a representation of a "specified" permission, i.e., 'Indefinite' or 'Forbidden'?
isSpecified :: (PermissionConfiguration m) => m t -> Bool
isSpecified = not . isUnderspecified

-- | Abbreviation for types which are both permission configurations and Monads.
type StateConfiguration m = (PermissionConfiguration m, Monad m)

-- | Abbreviation for types which are both permission configurations and Applicatives.
type PermissionApplicative m = (PermissionConfiguration m, Applicative m)

-- | Abbreviation for types which are both permission configurations and Functors.
type PermissionFunctor m = (PermissionConfiguration m, Functor m)

-- | Because the lattices-library doesn't support this
class JoinSemiLattice a where
    join :: a -> a -> a

--this would be very sensible but it confuses the compiler greatly. Maybe the UndecidableInstances and Overlapping language extensions don't like each other?
--instance Lattice a => JoinSemiLattice a where
--    join = (L.\/)

