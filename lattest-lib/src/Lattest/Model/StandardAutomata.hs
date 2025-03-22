{-# LANGUAGE TupleSections #-}

{- |
    This module contains some simple automata types, and auxiliary functions for constructing them in a convenient manner.
    Note that the types are no more than type aliases, so if the automata type with your favorite combination of type parameters
    is not listed, don't hesitate to construct an automaton type ('AutSyn' or 'AutSem') yourself instead of using the StandardAutomata.
-}

module Lattest.Model.StandardAutomata (
-- * Syntactical automata
-- ** Standard automata types
IA,
DIA,
NDIA,
AIA,
-- ** Auxiliary Functions for Constructing Automata
-- *** Interface Automata
-- | Functions for constructing Interface Automata, with arbitrary state configurations.
ia,
iaWithMenu,
iaWithAlphabet,
-- *** Deterministic Interface Automata
dia,
diaWithMenu,
diaWithAlphabet,
dia',
diaWithMenu',
diaWithAlphabet',
-- *** Non-Deterministic Interface Automata
ndia,
ndiaWithMenu,
ndiaWithAlphabet,
-- *** Alternating Interface Automata
aia,
aiaWithMenu,
aiaWithMenu',
aiaWithAlphabet,
aiaWithAlphabet',
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
semanticsQuiescentInputAttemptConcrete,
)
where

import Lattest.Model.Alphabet (IOAct, TimeoutIO, Timeout, isInput, IFAct, TimeoutIF, SymInteract, SymGuard, SymAssign)
import Lattest.Model.Automaton (AutSyn, automaton, AutSem, semantics, implicitDestination)
import Lattest.Model.StateConfiguration (DetState(..), NonDetState(..), FDL, PermissionConfiguration, StateConfiguration, PermissionFunctor, PermissionApplicative, forbidden, underspecified, FDL, atom, top, bot, (\/), (/\))

import Data.Foldable (toList)
import Data.Tuple.Extra (third3)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Map.Lazy (mapWithKey)
import qualified Data.Map.Lazy as LMap

-- TODO IA should have internal transitions
-- | Interface Automaton (for now, without internal transitions)
type IA m loc i o = AutSyn m loc (IOAct i o) ()
-- | deterministic IA
type DIA loc i o = IA DetState loc i o
-- | non-deterministic IA
type NDIA loc i o = IA NonDetState loc i o
-- | alternating IA
type AIA loc i o = IA FDL loc i o

type STS m loc i o = AutSyn m loc (SymInteract i o) (SymGuard,SymAssign)

---------------------------------
-- instantiations of alphabets --
---------------------------------

-- | From a (literal) list, create a transition relation without tloc (destination location specific parts of a location).
createTrans :: (Ord loc, Ord t, Applicative m) => [(loc, t, loc)] -> (loc -> Map t (m loc))
createTrans = createTrans' . fmap (third3 pure)

createTrans' :: (Ord loc, Ord t, Applicative m) => [(loc, t, m loc)] -> (loc -> Map t (m loc))
createTrans' list =
    let mapOfLists = foldr (\(loc, t, mloc') -> LMap.insertWith (++) loc [(t, mloc')]) LMap.empty list
        mapOfMaps = LMap.map LMap.fromList mapOfLists
    in \loc -> mapOfMaps LMap.! loc

-- | Construct an IA from transitions expressed as maps from actions to state configurations.
ia :: Functor m => m loc -> (loc -> Map (IOAct i o) (m loc)) -> IA m loc i o
ia loc t = automaton loc $ (Map.map (fmap ((),)) <$> t)

-- | Construct a deterministic IA from a list of transitions
dia' :: (Ord loc, Ord i, Ord o) => loc -> [(loc, IOAct i o, loc)] -> DIA loc i o
dia' loc trans = ia (Det loc) (createTrans trans)

-- | Construct a deterministic IA from transitions expressed as maps from actions to Just states, or Nothing for actions that are not enabled.
dia :: loc -> (loc -> Map (IOAct i o) (Maybe loc)) -> DIA loc i o
dia loc t = ia (Det loc) (\loc' -> mapWithKey maybeToDetState $ t loc')
    where
    maybeToDetState _ (Just q) = Det q
    maybeToDetState act Nothing = implicitDestination act

-- | Construct an non-deterministic IA from transitions expressed as maps from actions to lists of states, or the empty list for actions that are not enabled.
ndia :: [loc] -> (loc -> Map (IOAct i o) [loc]) -> NDIA loc i o
ndia loc t = ia (NonDet loc) (\loc' -> mapWithKey maybeToNonDetState $ t loc')
    where
    maybeToNonDetState act qs = if null qs then implicitDestination act else NonDet qs

-- | Construct an alternating IA from transitions expressed as maps from actions to logical expressions over states, or top or bottom for actions that are not enabled.
aia :: FDL loc -> (loc -> Map (IOAct i o) (FDL loc)) -> AIA loc i o
aia = ia

{- |
    Construct an IA from transitions expressed as maps from actions to state configurations. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
iaWithMenu :: (PermissionFunctor m, Foldable fld, Ord i, Ord o) => m loc -> (loc -> fld (IOAct i o)) -> (loc -> Map (IOAct i o) (m loc)) -> IA m loc i o
iaWithMenu loc menu t = 
    let t' = \loc' -> LMap.fromList $ fmap (\act -> (act,implicitDestination act)) $ toList $ menu loc' 
    in ia loc $ \loc' -> t loc' `Map.union` t' loc'

{- |
    Construct an IA from transitions expressed as maps from actions to state configurations. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
iaWithMenu' :: (PermissionApplicative m, Foldable fld, Ord i, Ord o, Ord loc) => m loc -> (loc -> fld (IOAct i o)) -> [(loc, IOAct i o, m loc)] -> IA m loc i o
iaWithMenu' loc menu t = iaWithMenu loc menu (createTrans' t)

{- |
    Construct a deterministic IA from a list of transitions. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit list of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
diaWithMenu' :: (Ord loc, Ord i, Ord o, Foldable fld) => loc -> (loc -> fld (IOAct i o)) -> [(loc, IOAct i o, loc)] -> DIA loc i o
diaWithMenu' loc menu trans = iaWithMenu (Det loc) menu (createTrans trans)

{- |
    Construct a deterministic IA from transitions expressed as maps from actions to Just states. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
diaWithMenu :: (Ord i, Ord o, Foldable fld) => loc -> (loc -> fld (IOAct i o)) -> (loc -> Map (IOAct i o) (Maybe loc)) -> DIA loc i o
diaWithMenu loc menu t = iaWithMenu (Det loc) menu (\loc' -> mapWithKey maybeToDetState $ t loc')
    where
    maybeToDetState _ (Just q) = Det q
    maybeToDetState act Nothing = implicitDestination act

{- |
    Construct an non-deterministic IA from transitions expressed as maps from actions to lists of states. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
ndiaWithMenu :: (Ord i, Ord o, Foldable fld) => [loc] -> (loc -> fld (IOAct i o)) -> (loc -> Map (IOAct i o) [loc]) -> NDIA loc i o
ndiaWithMenu loc menu t = iaWithMenu (NonDet loc) menu (\loc' -> mapWithKey maybeToNonDetState $ t loc')
    where
    maybeToNonDetState act qs = if null qs then implicitDestination act else NonDet qs

{- |
    Construct an alternating IA from transitions expressed as maps from actions to logical expressions over states. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
aiaWithMenu :: (Foldable fld, Ord i, Ord o) => FDL loc -> (loc -> fld (IOAct i o)) -> (loc -> Map (IOAct i o) (FDL loc)) -> AIA loc i o
aiaWithMenu = iaWithMenu

{- |
    Construct an alternating IA from a list of transitions to logical expressions over states. Also accepts a /menu/ of actions that defines, per state,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
aiaWithMenu' :: (Foldable fld, Ord i, Ord o, Ord loc) => FDL loc -> (loc -> fld (IOAct i o)) -> [(loc, IOAct i o, FDL loc)] -> IA FDL loc i o
aiaWithMenu' = iaWithMenu'

{- |
    Construct an IA from transitions expressed as maps from actions to state configurations. Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
iaWithAlphabet :: (PermissionFunctor m, Foldable fld, Ord i, Ord o) => m loc -> fld (IOAct i o) -> (loc -> Map (IOAct i o) (m loc)) -> IA m loc i o
iaWithAlphabet mloc alphabet t = iaWithMenu mloc (const alphabet) t

{- |
    Construct an IA from transitions expressed as maps from actions to state configurations. Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
iaWithAlphabet' :: (PermissionApplicative m, Foldable fld, Ord i, Ord o, Ord loc) => m loc -> fld (IOAct i o) -> [(loc, IOAct i o, m loc)] -> IA m loc i o
iaWithAlphabet' mloc alphabet t = iaWithAlphabet mloc alphabet (createTrans' t)

{- |
    Construct a deterministic IA from a list of transitions. Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit list of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
diaWithAlphabet' :: (Ord loc, Ord i, Ord o, Foldable fld) => loc -> fld (IOAct i o) -> [(loc, IOAct i o, loc)] -> DIA loc i o
diaWithAlphabet' mloc alphabet t = diaWithMenu' mloc (const alphabet) t

{- |
    Construct a deterministic IA from transitions expressed as maps from actions to Just states. Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
diaWithAlphabet :: (Ord i, Ord o, Foldable fld) => loc -> fld (IOAct i o) -> (loc -> Map (IOAct i o) (Maybe loc)) -> DIA loc i o
diaWithAlphabet mloc alphabet t = diaWithMenu mloc (const alphabet) t

{- |
    Construct an non-deterministic IA from transitions expressed as maps from actions to lists of states. Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
ndiaWithAlphabet :: (Ord i, Ord o, Foldable fld) => [loc] -> fld (IOAct i o) -> (loc -> Map (IOAct i o) [loc]) -> NDIA loc i o
ndiaWithAlphabet mloc alphabet t = ndiaWithMenu mloc (const alphabet) t

{- |
    Construct an alternating IA from transitions expressed as maps from actions to logical expressions over states.
    Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
aiaWithAlphabet :: (Foldable fld, Ord i, Ord o) => FDL loc -> fld (IOAct i o) -> (loc -> Map (IOAct i o) (FDL loc)) -> AIA loc i o
aiaWithAlphabet = iaWithAlphabet

{- |
    Construct an alternating IA from a list of transitions to logical expressions over states.
    Also accepts an /alphabet/ of actions that defines, globally for the entire automaton,
    which actions are (at least) implicitly defined. Actions that are in the menu but not in the explicit map of transitions are mapped to 'underspecified'
    (for inputs) or 'forbidden' (for outputs).
-}
aiaWithAlphabet' :: (Foldable fld, Ord i, Ord o, Ord loc) => FDL loc -> fld (IOAct i o) -> [(loc, IOAct i o, FDL loc)] -> AIA loc i o
aiaWithAlphabet' = iaWithAlphabet'

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
