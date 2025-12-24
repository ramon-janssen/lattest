{-# LANGUAGE TupleSections #-}

{- |
    This module contains some simple automata types, and auxiliary functions for constructing them in a convenient manner.
    Note that the types are no more than type aliases, so if the automata type with your favorite combination of type parameters
    is not listed, don't hesitate to construct an automaton type ('AutSyntax' or 'AutIntrpr') yourself instead of using the StandardAutomata.
    The base function `automaton` for constructing automata is re-exported here for convenience.
-}

module Lattest.Model.StandardAutomata (
-- * Automaton construction
automaton,
-- * Alphabets
-- | Auxiliary functions useful for constructing alphabets, intended for creating automata via `automaton`.
ioAlphabet,
-- * Transition relations
-- | Auxiliary functions useful for constructing transition relations, intended for creating automata via `automaton`.

-- ** Deterministic Transition Relations
detConcTransFromRel,
detConcTransFromMRel,
detConcTransFromMaybeRel,
-- ** Non-Deterministic Transition Relations
nonDetConcTransFromRel,
nonDetConcTransFromMRel,
nonDetConcTransFromListRel,
-- *** Alternating state configurations
-- | Re-exports, so that test scripts don't need to import BoundedMonad separately
FreeLattice,
atom,
top,
bot,
(\/),
(/\),
-- ** Transition Functions
transFromFunc,
concTransFromFunc,

-- * Automaton Semantics
-- | Auxiliary functions for creating semantical automata `AutIntrpr`. Note that most of these functions are no more than calls to `interpret`, instantiating
-- the type of the semantical interpretation.
ConcreteAutIntrpr,
interpretConcrete,
ConcreteSuspAutIntrpr,
interpretQuiescentConcrete,
ConcreteSuspInputAttemptAutIntrpr,
interpretInputAttemptConcrete,
interpretQuiescentInputAttemptConcrete,
STS,
IOSTS,
interpretSTS,
STSIntrp,
IOSTSIntrp
)
where

import Lattest.Model.Alphabet (IOAct(..), IOSuspAct, Suspended, isInput, IFAct, SuspendedIF, SymInteract, SymGuard,GateValue)
import Lattest.Model.Automaton (AutSyntax, automaton, AutIntrpr, interpret, Completable, implicitDestination,IntrpState(..),STStdest,stsTLoc)
import Lattest.Model.BoundedMonad (Det(..), NonDet(..), FreeLattice, BoundedConfiguration, BoundedMonad, BoundedFunctor, BoundedApplicative, forbidden, underspecified, FreeLattice, atom, top, bot, (\/), (/\), JoinSemiLattice)
import Data.Foldable (toList)
import Data.Tuple.Extra (third3)
import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Lazy (mapWithKey)
import qualified Data.Map.Lazy as LMap
import  Data.Maybe as Maybe
import qualified Data.Set as Set

-- | construct an alphabet of input-output-actions (`IOAct`) from separate alphabets of inputs and outputs
ioAlphabet :: (Traversable t, Ord i, Ord o) => t i -> t o -> Set.Set (IOAct i o)
ioAlphabet ti to = Set.fromList $ (In <$> toList ti) ++ (Out <$> toList to)

-- | To a transition relation without tdest, add vacuous tdests ().
concreteTrans :: (Functor m, Completable t) => (loc -> Map t (m loc)) -> (loc -> Map t (m ((), loc)))
concreteTrans trans q = Map.map (fmap (\loc -> ((), loc))) (trans q)

{- |
    Create a deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as explicit states.
    Having multiple occurrences of a transition label is forbidden, i.e., leads to a Nothing result.
-}
detConcTransFromRel :: (Completable t, Ord loc, Ord t) => [(loc, t, loc)] -> Maybe (loc -> Map t (Det ((), loc)))
detConcTransFromRel = transFromRelWith combineDet vacuousTrans (\l () _ -> Det $ vacuousLoc l)

{- |
    Create a deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as deterministic state
    configuration. Having multiple occurrences of a transition label is forbidden, i.e., leads to a Nothing result.
-}
detConcTransFromMRel :: (Completable t, Ord loc, Ord t) => [(loc, t, Det loc)] -> Maybe (loc -> Map t (Det ((), loc)))
detConcTransFromMRel = transFromRelWith combineDet vacuousTrans (\dl () _ -> fmap vacuousLoc dl)

{- |
    Create a deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as Just deterministic
    states, where `Nothing` is mapped to either `forbidden` or `underspecified`, depending on the transition label. Having multiple occurrences of a transition label is forbidden,
    i.e., leads to a Nothing result.
-}
detConcTransFromMaybeRel :: (Completable t, Ord loc, Ord t) => [(loc, t, Maybe loc)] -> Maybe (loc -> Map t (Det ((), loc)))
detConcTransFromMaybeRel = transFromRelWith combineDet vacuousTrans $ \mLoc () t -> case mLoc of
    Just loc -> vacuousLoc <$> Det loc
    Nothing -> implicitDestination t

{- |
    Create a non-deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as explicit states.
    The state configuration must support non-determinism, and having multiple occurrences of a transition label is interpreted as non-deterministic choice
    between the destinations.
-}
nonDetConcTransFromRel :: (Completable t, Ord loc, Ord t, Applicative m, JoinSemiLattice (m ((), loc))) => [(loc, t, loc)] -> (loc -> Map t (m ((), loc)))
nonDetConcTransFromRel = fromJust <$> transFromRelWith combineNonDet vacuousTrans (\l () _ -> pure $ vacuousLoc l)

{- |
    Create a non-deterministic symbolic transition relation from an explicit list of tuples, with the destination of transitions expressed as explicit states.
    The state configuration must support non-determinism, and having multiple occurrences of a transition label is interpreted as non-deterministic choice
    between the destinations.
-}
--nonDetSymbTransFromRel :: (Completable t, Ord loc, Ord t, Applicative m, JoinSemiLattice (m ((), loc))) => [(loc, t, tdest, loc)] -> (loc -> Map t (m (tdest, loc)))
--nonDetSymbTransFromRel = fromJust <$> transFromRelWith combineNonDet id (\l () _ -> pure $ vacuousLoc l)

{- |
    Create a concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as non-deterministic state
    configuration. The state configuration must support non-determinism, and having multiple occurrences of a transition label is interpreted
    as non-deterministic choice between the destinations.
-}
nonDetConcTransFromMRel :: (Completable t, Ord loc, Ord t, Applicative m, JoinSemiLattice (m ((), loc))) => [(loc, t, m loc)] -> (loc -> Map t (m ((), loc)))
nonDetConcTransFromMRel = fromJust <$> transFromRelWith combineNonDet vacuousTrans (\ndl () _ -> fmap vacuousLoc ndl)

{- |
    Create a non-deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as lists of locations,
    where the empty list is mapped to either `forbidden` or `underspecified`, depending on the transition label.
    Having multiple occurrences of a transition label is interpreted as non-deterministic choice between the destinations.
-}
nonDetConcTransFromListRel :: (Completable t, Ord loc, Ord t) => [(loc, t, [loc])] -> (loc -> Map t (NonDet ((), loc)))
nonDetConcTransFromListRel = fromJust <$> transFromRelWith combineNonDet vacuousTrans listToNonDet
    where
    listToNonDet (list@(_:_)) () t = vacuousLoc <$> NonDet list
    listToNonDet [] () t = implicitDestination t

combineNonDet x y = Just $ x \/ y

combineDet _ _ = Nothing

vacuousTrans (a,b,c) = (a,b,(),c)

vacuousLoc l = ((), l)

transFromRelWith :: (Completable t, Ord loc, Ord t) =>
    (m (tdest, loc) -> m (tdest, loc) -> Maybe (m (tdest, loc))) -- the way of combining the monadic transitions resulting from two list elements, or Nothing if they cannot be combined
    -> (te -> (loc, t, tdest, loc')) -- the way of creating a 4-tuple with all the transition info from a list element
    -> (loc' -> tdest -> t -> m (tdest, loc)) -- the way of creating a monadic transition result from the transition info of a list element
    -> [te] -- the transition relation in a list representation
    -> Maybe (loc -> Map t (m (tdest, loc))) -- a transition function, or Nothing if combining two monadic transitions failed
transFromRelWith c' fe' f' trans = do
    tMapMap <- foldr (addToMap c' fe' f') (Just Map.empty) trans -- map from locations to a map from transitions to Dets
    Just $ \loc -> case loc `Map.lookup` tMapMap of
        Just tMap -> tMap
        Nothing -> Map.empty
    where
    addToMap :: (Completable t, Ord loc, Ord t) => (m (tdest, loc) -> m (tdest, loc) -> Maybe (m (tdest, loc))) -> (te -> (loc, t, tdest, loc')) -> (loc' -> tdest -> t -> m (tdest, loc)) -> te -> Maybe (Map loc (Map t (m (tdest, loc)))) -> Maybe (Map loc (Map t (m (tdest, loc))))
    addToMap c fe f te maybeTMapMap = do
        tMapMap <- maybeTMapMap
        let (loc, t, tdest, loc') = fe te
        case loc `Map.lookup` tMapMap of
            Just tMap -> case t `Map.lookup` tMap of
                Nothing -> Just $ Map.insert loc (Map.insert t (f loc' tdest t) tMap) tMapMap
                Just prevLoc -> do
                    combinedLoc <- c prevLoc $ f loc' tdest t
                    Just $ Map.insert loc (Map.insert t combinedLoc tMap) tMapMap
            Nothing -> Just $ Map.insert loc (Map.singleton t (f loc' tdest t)) tMapMap

{- |
    Create a transition relation from a transition function. Warning: to use the resulting transition relation in an automaton, the function must be defined
    for all reachable states, and for all transition labels in the alphabet of the automaton.
-}
transFromFunc :: (Foldable fld, Ord t) => (loc -> t -> m (tdest, loc)) -> fld t -> (loc -> Map t (m (tdest, loc)))
transFromFunc fTrans alph loc = Map.fromSet (fTrans loc) (foldableAsSet alph)

{- |
    Create a concrete transition relation from a transition function. Warning: to use the resulting transition relation in an automaton, the function must be defined
    for all reachable states, and for all transition labels in the alphabet of the automaton.
-}
concTransFromFunc :: (Foldable fld, Functor m, Ord t) => (loc -> t -> m loc) -> fld t -> (loc -> Map t (m ((), loc)))
concTransFromFunc fTrans alph loc = Map.fromSet (fTransConc) (foldableAsSet alph)
    where
    fTransConc t = (\x -> ((), x)) <$> fTrans loc t

foldableAsSet :: (Foldable fld, Ord a) => fld a -> Set.Set a
foldableAsSet fld = Set.fromList $ Foldable.toList fld

---------------------------------
-- instantiations of interpret --
---------------------------------

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions.
type ConcreteAutIntrpr m q act = AutIntrpr m q q act () act

-- | Interpret syntactical states and actions directly as literal, semantical states and actions.
interpretConcrete :: (BoundedMonad m, Ord t, Show t, Show loc) => AutSyntax m loc t () -> ConcreteAutIntrpr m loc t
interpretConcrete = flip interpret id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with timeouts as possible output observations.
type ConcreteSuspAutIntrpr m q i o = AutIntrpr m q q (IOAct i o) () (IOSuspAct i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with timeouts as possible output observations.
interpretQuiescentConcrete :: (BoundedMonad m, Ord i, Ord o, Show i, Show o, Show loc) => AutSyntax m loc (IOAct i o) () -> ConcreteSuspAutIntrpr m loc i o
interpretQuiescentConcrete = flip interpret id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with input failures as possible input observations.
type ConcreteInputAttemptAutIntrpr m q i o = AutIntrpr m q q (IOAct i o) () (IFAct i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with input failures as possible input observations.
interpretInputAttemptConcrete :: (BoundedMonad m, Ord i, Ord o, Show i, Show o, Show loc) => AutSyntax m loc (IOAct i o) () -> ConcreteInputAttemptAutIntrpr m loc i o
interpretInputAttemptConcrete = flip interpret id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with timeouts and input failures as possible observations.
type ConcreteSuspInputAttemptAutIntrpr m q i o = AutIntrpr m q q (IOAct i o) () (SuspendedIF i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with timeouts and input failures as possible observations.
interpretQuiescentInputAttemptConcrete :: (BoundedMonad m, Ord i, Ord o, Show i, Show o, Show loc) => AutSyntax m loc (IOAct i o) () -> ConcreteSuspInputAttemptAutIntrpr m loc i o
interpretQuiescentInputAttemptConcrete = flip interpret id

type STS m loc g = AutSyntax m loc (SymInteract g) STStdest
type IOSTS m loc i o = STS m loc (IOAct i o)

type STSIntrp m loc g = AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g)
type IOSTSIntrp m loc i o = STSIntrp m loc (IOAct i o)

interpretSTS :: (Ord g, Ord loc, Show loc, Show g, Show (m (IntrpState loc)), BoundedMonad m,Show (m (STStdest, loc))) => STS m loc g -> (loc -> IntrpState loc) -> AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g)
interpretSTS = interpret
