{-# LANGUAGE TupleSections #-}

{- |
    This module contains some simple automata types, and auxiliary functions for constructing them in a convenient manner.
    Note that the types are no more than type aliases, so if the automata type with your favorite combination of type parameters
    is not listed, don't hesitate to construct an automaton type ('AutSyn' or 'AutSem') yourself instead of using the StandardAutomata.
-}

module Lattest.Model.StandardAutomata (
-- * Syntactical automata
-- ** Auxiliary Functions for Transitions
-- *** Inputs/Outputs
ioAlphabet,
-- *** Deterministic Transition Relations
detConcTransFromRel,
detConcTransFromMRel,
detConcTransFromMRel,
-- *** Non-Deterministic Transition Relations
nonDetConcTransFromRel,
nonDetConcTransFromRel,
nonDetConcTransFromListRel,
-- **** Alternating state configurations
-- Re-exports, so that test scripts don't need to import StateConfiguration separately
FDL,
atom,
top,
bot,
(\/),
(/\),

-- * Automaton Semantics
ConcreteAutSem,
semanticsConcrete,
ConcreteTimeoutAutSem,
semanticsQuiescentConcrete,
ConcreteTimeoutInputAttemptAutSem,
semanticsQuiescentInputAttemptConcrete
)
where

import Lattest.Model.Alphabet (IOAct(..), TimeoutIO, Timeout, isInput, IFAct, TimeoutIF)
import Lattest.Model.Automaton (AutSyn, automaton, AutSem, semantics, Observable, implicitDestination)
import Lattest.Model.StateConfiguration (DetState(..), NonDetState(..), FDL, PermissionConfiguration, StateConfiguration, PermissionFunctor, PermissionApplicative, forbidden, underspecified, FDL, atom, top, bot, (\/), (/\), join)

import Data.Foldable (toList)
import Data.Tuple.Extra (third3)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Lazy (mapWithKey)
import qualified Data.Map.Lazy as LMap
import qualified Data.Set as Set

ioAlphabet :: (Traversable t, Ord i, Ord o) => t i -> t o -> Set.Set (IOAct i o)
ioAlphabet ti to = Set.fromList $ (In <$> toList ti) ++ (Out <$> toList to)

-- | To a transition relation without tloc, add vacuous tlocs ().
concreteTrans :: (Functor m, Observable t) => (loc -> Map t (m loc)) -> (loc -> Map t (m ((), loc)))
concreteTrans trans q = Map.map (fmap (\loc -> ((), loc))) (trans q)

detConcTransFromRel :: (Observable t, Ord loc, Ord t) => [(loc, t, loc)] -> Maybe (loc -> Map t (DetState ((), loc)))
detConcTransFromRel = detTransFromRelWith combineDet vacuousTrans (\l () _ -> Det $ vacuousLoc l)

detConcTransFromMRel :: (Observable t, Ord loc, Ord t) => [(loc, t, DetState loc)] -> Maybe (loc -> Map t (DetState ((), loc)))
detConcTransFromMRel = detTransFromRelWith combineDet vacuousTrans (\dl () _ -> fmap vacuousLoc dl)

detConcTransFromMaybeRel :: (Observable t, Ord loc, Ord t) => [(loc, t, Maybe loc)] -> Maybe (loc -> Map t (DetState ((), loc)))
detConcTransFromMaybeRel = detTransFromRelWith combineDet vacuousTrans $ \mLoc () t -> case mLoc of
    Just loc -> vacuousLoc <$> Det loc
    Nothing -> implicitDestination t

nonDetConcTransFromRel :: (Observable t, Ord loc, Ord t) => [(loc, t, loc)] -> Maybe (loc -> Map t (NonDetState ((), loc)))
nonDetConcTransFromRel = detTransFromRelWith combineNonDet vacuousTrans (\l () _ -> NonDet [vacuousLoc l])

nonDetConcTransFromMRel :: (Observable t, Ord loc, Ord t) => [(loc, t, NonDetState loc)] -> Maybe (loc -> Map t (NonDetState ((), loc)))
nonDetConcTransFromMRel = detTransFromRelWith combineNonDet vacuousTrans (\ndl () _ -> fmap vacuousLoc ndl)

nonDetConcTransFromListRel :: (Observable t, Ord loc, Ord t) => [(loc, t, [loc])] -> Maybe (loc -> Map t (NonDetState ((), loc)))
nonDetConcTransFromListRel = detTransFromRelWith combineNonDet vacuousTrans $ \mLoc () t -> case mLoc of
    list@(_:_) -> vacuousLoc <$> NonDet list
    [] -> implicitDestination t

combineNonDet x y = Just $ join x y

combineDet _ _ = Nothing

vacuousTrans (a,b,c) = (a,b,(),c)

vacuousLoc l = ((), l)

detTransFromRelWith :: (Observable t, Ord loc, Ord t) =>
    (m (tloc, loc) -> m (tloc, loc) -> Maybe (m (tloc, loc))) -- the way of combining the monadic transitions resulting from two list elements, or Nothing if they cannot be combined
    -> (te -> (loc, t, tloc, loc')) -- the way of creating a 4-tuple with all the transition info from a list element
    -> (loc' -> tloc -> t -> m (tloc, loc)) -- the way of creating a monadic transition result from the transition info of a list element
    -> [te] -- the transition relation in a list representation
    -> Maybe (loc -> Map t (m (tloc, loc))) -- a transition function, or Nothing if combining two monadic transitions failed
detTransFromRelWith c' fe' f' trans = do
    tMapMap <- foldr (addToMap c' fe' f') (Just Map.empty) trans -- map from locations to a map from transitions to DetStates
    Just $ \loc -> case loc `Map.lookup` tMapMap of
        Just tMap -> tMap
        Nothing -> Map.empty
    where
    addToMap :: (Observable t, Ord loc, Ord t) => (m (tloc, loc) -> m (tloc, loc) -> Maybe (m (tloc, loc))) -> (te -> (loc, t, tloc, loc')) -> (loc' -> tloc -> t -> m (tloc, loc)) -> te -> Maybe (Map loc (Map t (m (tloc, loc)))) -> Maybe (Map loc (Map t (m (tloc, loc))))
    addToMap c fe f te maybeTMapMap = do
        tMapMap <- maybeTMapMap
        let (loc, t, tloc, loc') = fe te
        case loc `Map.lookup` tMapMap of
            Just tMap -> case t `Map.lookup` tMap of
                Nothing -> Just $ Map.insert loc (Map.insert t (f loc' tloc t) tMap) tMapMap
                Just prevLoc -> do
                    combinedLoc <- c prevLoc $ f loc' tloc t
                    Just $ Map.insert loc (Map.insert t combinedLoc tMap) tMapMap
            Nothing -> Just $ Map.insert loc (Map.singleton t (f loc' tloc t)) tMapMap

---------------------------------
-- instantiations of locations --
---------------------------------

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions.
type ConcreteAutSem m q act = AutSem m q q act () act

-- | Interpret syntactical states and actions directly as literal, semantical states and actions.
semanticsConcrete :: (StateConfiguration m, Ord t) => AutSyn m loc t () -> ConcreteAutSem m loc t
semanticsConcrete = flip semantics id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with timeouts as possible output observations.
type ConcreteTimeoutAutSem m q i o = AutSem m q q (IOAct i o) () (TimeoutIO i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with timeouts as possible output observations.
semanticsQuiescentConcrete :: (StateConfiguration m, Ord i, Ord o) => AutSyn m loc (IOAct i o) () -> ConcreteTimeoutAutSem m loc i o
semanticsQuiescentConcrete = flip semantics id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with input failures as possible input observations.
type ConcreteInputAttemptAutSem m q i o = AutSem m q q (IOAct i o) () (IFAct i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with input failures as possible input observations.
semanticsInputAttemptConcrete :: (StateConfiguration m, Ord i, Ord o) => AutSyn m loc (IOAct i o) () -> ConcreteInputAttemptAutSem m loc i o
semanticsInputAttemptConcrete = flip semantics id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with timeouts and input failures as possible observations.
type ConcreteTimeoutInputAttemptAutSem m q i o = AutSem m q q (IOAct i o) () (TimeoutIF i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with timeouts and input failures as possible observations.
semanticsQuiescentInputAttemptConcrete :: (StateConfiguration m, Ord i, Ord o) => AutSyn m loc (IOAct i o) () -> ConcreteTimeoutInputAttemptAutSem m loc i o
semanticsQuiescentInputAttemptConcrete = flip semantics id
