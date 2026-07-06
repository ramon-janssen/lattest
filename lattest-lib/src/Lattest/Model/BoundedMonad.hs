{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ConstraintKinds #-}


{- |
    A /bounded monad/ is a type constructor which represents the observable perspective on the state of an automaton, also called a
    /state configuration/. A system will internally have a state, but this state can not always be observed or inferred for an external viewer. To
    model the difference between internal and observable state, we define automata as having a type of internal state, say q, and
    an observable state configuration over q.
    
    In this module, we define two such state configurations:
    
    * deterministic state configurations, where every behaviour leads to a single state,
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
-- * State configurations
-- ** Deterministic
Det(..),
-- ** Distributive lattice in CNF
FreeLattice(FreeLattice),
atom,
top,
bot,
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
(/\),
-- ** Mapping between lattices and boolean expressions
BooleanConfiguration,
asExpr,
asDualExpr,
-- ** 'Data.OrdMonad' re-export, for convenience.
module OM,
joins,
meets,
disjunction,
(\$/),
conjunction,
(/$\)
)
where

import qualified Lattest.Model.Symbolic.Expr as E

import qualified Data.List as List
import qualified Data.Set as Set
import Data.OrdMonad as OM


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
    Det f <*> (Det s) = Det (f s)
    ForbiddenDet <*> _ = ForbiddenDet
    UnderspecDet <*> _ = UnderspecDet
    _ <*> ForbiddenDet = ForbiddenDet
    _ <*> UnderspecDet = UnderspecDet
    pure = Det

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

{-|
    Free distributive lattice, or a positive boolean formula, in CNF-format. 
-}
newtype FreeLattice a = FreeLattice (Set.Set (Set.Set a)) deriving  (Eq, Ord, Foldable)

-- | A single state embedded in a free distributive lattice.
atom :: a -> FreeLattice a
atom = ordReturn

-- | The free distributive lattice element ⊥, or false.
bot :: FreeLattice a
bot = forbidden

-- | The free distributive lattice element ⊤, or true.
top :: FreeLattice a
top = underspecified

-- | Combine a collection of FreeLattices using '(/\)'
meets :: (Foldable f, Ord a) => f (FreeLattice a) -> FreeLattice a
meets = foldr (/\) top

-- | Combine a collection of FreeLattices using '(\/)'
joins :: (Foldable f, Ord a) => f (FreeLattice a) -> FreeLattice a
joins = foldr (\/) bot

-- | Combine a collection of states using '(/\)'
conjunction :: (Functor f, Foldable f, Ord a) => f a -> FreeLattice a
conjunction = meets . fmap atom

-- | Synonym for 'conjunction'
(/$\) :: (Functor f, Foldable f, Ord a) => f a -> FreeLattice a
(/$\) = conjunction

-- | Combine a collection of states using '(\/)'
disjunction :: (Functor f, Foldable f, Ord a) => f a -> FreeLattice a
disjunction = joins . fmap atom

-- | Synonym for 'disjunction'
(\$/) :: (Functor f, Foldable f, Ord a) => f a -> FreeLattice a
(\$/) = disjunction

instance BoundedConfiguration FreeLattice where
    isForbidden (FreeLattice x) = any Set.null x
    isUnderspecified (FreeLattice x) = Set.null x
    forbidden = FreeLattice $ Set.singleton Set.empty
    underspecified = FreeLattice Set.empty

instance OM.OrdMonad FreeLattice where
    ordBind (FreeLattice x) f = FreeLattice $ cnfJoin $ Set.map (Set.map f1) x
        where
            f1 y = let FreeLattice z = f y in z
    ordReturn x = FreeLattice  $ Set.singleton $ Set.singleton x

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

instance OM.OrdFunctor FreeLattice where
    ordMap f (FreeLattice x) = FreeLattice $ Set.map (Set.map f) x

instance Ord a => JoinSemiLattice (FreeLattice a) where
    (FreeLattice x) \/ (FreeLattice y) = FreeLattice $ Set.map Set.unions $ nAryCartesianProduct $ Set.fromList [x,y]

instance Ord a => MeetSemiLattice (FreeLattice a) where
    (FreeLattice x) /\ (FreeLattice y) =
        let x' = Set.filter (not . isProperSupersetOfAny y) x
            y' = Set.filter (not . isProperSupersetOfAny x) y
        in FreeLattice (x' `Set.union` y')

instance Show a => Show (FreeLattice a) where
    show l
        | isForbidden l = "⊥"
        | isUnderspecified l = "⊤"
    show (FreeLattice x) = case Set.toList x of
            [conjunct] -> List.intercalate " ∨ " $ show <$> Set.toList conjunct
            conjuncts -> List.intercalate " ∧ " $ showDisjunct <$> conjuncts
        where
        showDisjunct :: Show a => Set.Set a -> String
        showDisjunct y = case Set.toList y of
            [e] -> show e
            disjuncts -> "(" ++ List.intercalate " ∨ " (show <$> disjuncts) ++ ")"

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
specifiedness :: BoundedConfiguration m => m t -> Specifiedness
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
type BoundedMonad m = (BoundedConfiguration m, OM.OrdMonad m)

-- | Abbreviation for types which are both bounded configurations and Functors.
type BoundedFunctor m = (BoundedConfiguration m, OM.OrdFunctor m)

-- | Semi-lattices with a binary join ('or') operation
class JoinSemiLattice a where
    (\/) :: a -> a -> a

-- | Semi-lattices with a binary meet ('and') operation
class MeetSemiLattice a where
    (/\) :: a -> a -> a

--this would be very sensible but it confuses the compiler greatly. Maybe the UndecidableInstances and Overlapping language extensions don't like each other?
--instance Lattice a => JoinSemiLattice a where
--    join = (L.\/)

class BooleanConfiguration m where -- TODO: possibly this class can be less ad-hoc, e.g. via some lattice-theoretic concept
    asExpr :: m (E.Expr Bool) -> E.Expr Bool

instance BooleanConfiguration Det where
    asExpr (Det q) = q
    asExpr ForbiddenDet = E.sFalse
    asExpr UnderspecDet = E.sTrue

instance BooleanConfiguration FreeLattice where
    asExpr (FreeLattice x) = Set.foldr (E..&&) E.sTrue $ Set.map (Set.foldr (E..||) E.sFalse) x

asDualExpr :: (OrdFunctor m, BooleanConfiguration m) => m (E.Expr Bool) -> E.Expr Bool
asDualExpr m = E.sNot $ asExpr $ E.sNot OM.<#> m

instance Traversable Det where
  sequenceA (Det a) = Det <$> a
  sequenceA ForbiddenDet = pure ForbiddenDet
  sequenceA UnderspecDet = pure UnderspecDet

