{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
    This module contains the definitions and semantics of automata models.
-}

module Lattest.Model.Automaton (
-- * Syntactical Automaton Model
-- ** Definition
AutSyn,
locConf,
alphabet,
transRel,
-- ** Constructing Syntactical Automata
automaton,
automaton',
-- * Semantical Automaton Model
-- ** Definition
AutSem,
stateConf,
syntacticAutomaton,
-- ** Constructing Syntactical Automata
semantics,
-- ** Type Classes for Semantics
Observable,
implicitDestination,
TransitionSemantics,
StateSemantics,
AutomatonSemantics,
after,
afters,
-- ** Finite Transition Labels
FiniteMenu,
specifiedMenu,
-- ** STS State data types
IntrpState(..),
Valuation,
-- * Auxiliary Automaton Functions
reachable,
reachableFrom,
)
where

import Prelude hiding (lookup)

import Lattest.Model.StateConfiguration(PermissionApplicative, StateConfiguration, PermissionConfiguration, isForbidden, forbidden, underspecified, isSpecified)
import Lattest.Model.Alphabet(IOAct(In,Out),isOutput,TimeoutIO,Timeout(Timeout),IFAct(..),Attempt(..),fromTimeout,asTimeout,fromInputAttempt,asInputAttempt,TimeoutIF,asTimeoutInputAttempt,fromTimeoutInputAttempt,
    SymInteract(..),GateValue(..),Value(..), SymGuard, SymAssign,Variable,addTypedVar,Variable(..),Type(..),SymExpr(..),Gate(..),equalTyped)
import Lattest.Util.Utils((&&&), takeArbitrary)
import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tuple.Extra(first)
import GHC.OldList(find)
import Grisette.Core as Grisette
import Grisette.SymPrim as GSymPrim

------------
-- syntax --
------------

{- |
    Syntactical automaton model, with locations and transitions. This is analogous to an automaton drawn on paper
    with points and arrows. Transitions are mapped to /state configurations/, see "Lattest.Model.StateConfiguration".
    Furthermore, transitions contain transition labels, both on the 'outside' and in the 'inside' of the state configuration.
    
    These labels are abstract and may be interpreted in various ways, e.g. a simple automaton model may directly have
    observable actions as labels, whereas a more complex automaton model may have symbolic data variables with guards,
    assignments, clocks for timing, etc.
-}
data AutSyn m loc t tloc = Automaton {
    locConf :: m loc,
    alphabet :: Set t,
    transRel :: loc -> Map t (m (tloc, loc))
    }

-- | Construct an automaton from an initial state configuration and a transition mapping
automaton :: (PermissionConfiguration m, Observable t, Ord t, Foldable fld) => m loc -> fld t -> (loc -> Map t (m (tloc, loc))) -> AutSyn m loc t tloc
automaton mqi alphFld trans = Automaton mqi alph trans'
    where -- FIXME t is now Observable, in other functions we expect actions instead of transitions to be Observable.
          -- some alternatives: instead of forbidden, just throw an error (not nice), or add a separate class for transitions
    alph = Set.fromList $ Foldable.toList alphFld
    trans' q = Map.restrictKeys (trans q) alph `Map.union` setToList alph implicitDestination -- left-biased union 
    setToList s f = Set.foldr (\k -> Map.insert k (f k)) Map.empty s

-- | Construct an automaton from an initial state and a transition mapping
automaton' :: (PermissionApplicative m, Observable t, Ord t) => loc -> Set t -> (loc -> Map t (m (tloc, loc))) -> AutSyn m loc t tloc
automaton' = automaton . pure

---------------
-- semantics --
---------------

{- |
    Semantical automaton model. This model contains a reference to the syntactical automaton on which it is based,
    but it also contains a state configuration with semantical states.

    The difference between the locations from the syntactical model and the states from the semantical model depends
    on the automaton semantics. E.g. for a simple automaton model, states and locations may be the same, whereas a more
    complex automaton model may have states consisting of syntactical locations combined with valuations for data
    variables, clocks for timing, etc.
-}
data AutSem m loc q t tloc act = AutomatonRun {
    stateConf :: m q,
    syntacticAutomaton :: AutSyn m loc t tloc
    }

{- |
    Infer a semantical model from a syntactical model, based on the appropriate instance of the 'AutomatonSemantics' typeclass.
    Note that an automaton may be interpreted in multiple ways, so the type checker may need a hint on which semantical
    automaton is requested. This can be avoided by calling more specific, pre-typed variants of 'semantics' in
    "Lattest.Adapter.StandardAdapters".
-}
semantics :: (AutomatonSemantics m loc q t tloc act) => AutSyn m loc t tloc -> (loc -> q) -> AutSem m loc q t tloc act
semantics aut initState = AutomatonRun { stateConf = initState <$> locConf aut, syntacticAutomaton = aut }

-- | The Observable typeclass defines which types can be used as labels on transitions.
class Observable act where
    {- |
        Defines the implicit state configuration reached by a given transition label if that label is omitted from 
        a syntactical automaton. E.g. if a state contains no outgoing transition for an output label, that label
        is often considered to map to the 'forbidden' state configuration.
    -}
    implicitDestination :: PermissionConfiguration m => act -> m any

{- |
    TransitionSemantics expresses that the semantics of a syntactic transition can be expressed in terms of actions. E.g. symbolic transitions with
    interaction variables that can be expressed in terms of concrete observed values.
-}
class (Ord t, Observable act) => TransitionSemantics t act where
    {- |
        Map an action to a matching transition. E.g. a concrete value on some channel that matches with the symbolic representation of that channel.
        'Nothing' indicates an action that occurs within a location, without explicit transition.
    -}
    asTransition :: loc -> Set t -> act -> Maybe t
    -- | Find the syntactic transition that applies for the given semantic action value, or alternatively a move within the location.
    takeTransition :: (PermissionApplicative m, Ord t) => loc -> Set t -> act -> Map t (m (tloc, loc)) -> Maybe (Move m t tloc loc)
    takeTransition loc alph act tmap = case asTransition loc alph act of
        Nothing -> Just $ LocationMove $ pure loc
        Just t -> TransitionMove . (t,) <$> Map.lookup t tmap

{- |
    Data structure needed to express that an automaton may transition from one location to another, but it may also 'transition'
    within a single state, e.g. the passing of time in a timed automaton.
-}
data Move m t tloc loc = TransitionMove (t, m (tloc, loc)) | LocationMove (m loc)

{- |
    StateSemantics expresses that the semantics of a syntactic location can be expressed in terms of state q. E.g. a location symbolic variables can be 
    given in terms of valuations of these variables.
-}
class StateSemantics loc q where
    -- | from a state, extract the corresponding location
    asLoc :: q -> loc

{- |
    Automaton semantics expresses that we can take steps, to move from one state configuration to another. 
-}
class StateConfiguration m => AutomatonSemantics m loc q t tloc act where
    -- | Take a transition for the given action.
    after :: AutSem m loc q t tloc act -> act -> AutSem m loc q t tloc act

{- |
    Standard monadic implementation of the 'after' function: take a monadic step. The first argument describes how to take a step, i.e., how to
    produce a new state configuration from the transition relation, the action taken, and the previous state.
-}
monadicAfter :: (StateConfiguration m) => (Set t -> (loc -> Map t (m (tloc, loc))) -> act -> q -> m q) -> AutSem m loc q t tloc act -> act -> AutSem m loc q t tloc act
monadicAfter step autRun act' =
    let aut = syntacticAutomaton autRun 
    in autRun { stateConf = stateConf autRun >>= step (alphabet aut) (transRel aut) act' }

{- |
    Default stepping function for the 'monadicAfter' function: find the transition in the transition mapping corresponding to the given action, and
    take a monadic step from the current state configuration.
    
    If no transition is found for the given action, then the state configuration is implicit, as described by 'Observable'.
-}
withStep :: (TransitionSemantics t act, StateSemantics loc q, StateConfiguration m) => (q -> act -> Maybe (t, tloc) -> loc -> m q) -> Set t -> (loc -> Map t (m (tloc, loc))) -> act -> q -> m q
withStep move alph transMap act q = case takeTransition (asLoc q) alph act (transMap $ asLoc q) of
    Nothing -> implicitDestination act
    Just (LocationMove mloc) -> mloc >>= moveWithinLocation q act Nothing
        where
        moveWithinLocation q act nottloc loc = move q act nottloc loc
    Just (TransitionMove (t, mloc)) -> mloc >>= moveAlongTransition q act t
        where
        moveAlongTransition q act t (tloc, loc) = move q act (Just (t, tloc)) loc

-- | Take a sequence of transitions for the given actions.
afters :: (AutomatonSemantics m loc q t tloc act) => AutSem m loc q t tloc act -> [act] -> AutSem m loc q t tloc act
afters aut [] = aut
afters aut (act:acts) = aut `after` act `afters` acts

------------------------------------------------------------------
-- utility function to obtain the menu of outgoing transitions --
------------------------------------------------------------------
-- note: this only shows the transitions that are syntactically present in the automaton, so e.g. not quiescence, including underspecified/forbidden transitions
transMenu :: (Foldable m, Functor m, Ord t) => AutSyn m mloc t tloc -> Set t
transMenu aut = let
    stateToMenu = Set.fromList . Map.keys . transRel aut
    in Set.unions $ stateToMenu <$> locConf aut

{-|
    The class of automata with a finite list of transition labels on outgoing transitions for every state.
    This property is useful for e.g. test selection.
-}
class TransitionSemantics t act => FiniteMenu t act where
    -- menu of actions that are semantically present in the automaton, including underspecified/forbidden transitions
    asActions :: t -> [act]
    locationActions :: AutSyn m mloc t tloc -> [act]

actionMenu :: (Foldable m, Functor m, Ord t) => FiniteMenu t act => PermissionApplicative m => AutSyn m mloc t tloc -> [act]
actionMenu aut = (locationActions aut ++) $ concat $ fmap asActions $ Set.toList $ transMenu aut

-- | Menu of specified actions that are semantically present in the automaton.
specifiedMenu :: (AutomatonSemantics m loc q t tloc act, Foldable m, Ord t) => FiniteMenu t act => AutSem m loc q t tloc act -> [act]
specifiedMenu aut = [act | act <- actionMenu $ syntacticAutomaton aut, isSpecified $ stateConf $ aut `after` act]

-----------------------------------------------------------------------------------------------
-- special case where the semantic states and actions are directly represented syntactically --
-----------------------------------------------------------------------------------------------

instance (Observable act) where
    implicitDestination _ = forbidden

instance (Ord act) => TransitionSemantics act act where
    asTransition _ _ = Just

instance (Ord act) => FiniteMenu act act where
    asActions t = [t] 
    locationActions _ = []

instance StateSemantics q q where
    asLoc = id

instance (TransitionSemantics t act, StateConfiguration m) => AutomatonSemantics m q q t () act
    where
    after = monadicAfter $ withStep (\_ _ _ q -> pure q)

----------------
-- quiescence --
----------------
instance (Observable (IOAct i o)) where
    implicitDestination (Out _) = forbidden
    implicitDestination _ = underspecified

instance (Ord i, Ord o) => TransitionSemantics (IOAct i o) (TimeoutIO i o) where
    asTransition loc _ (Out Timeout) = Nothing
    asTransition _ _ other = Just $ fromTimeout other
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc _ (Out Timeout) m = Just . LocationMove $ if hasQuiescence m then forbidden else pure loc
    takeTransition _ _ act m = TransitionMove . (fromTimeout act,) <$> Map.lookup (fromTimeout act) m

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (TimeoutIO i o) where
    asActions t = [asTimeout t]
    locationActions _ = [Out Timeout]

hasQuiescence :: PermissionApplicative m => Map (IOAct i o) (m (tloc, loc)) -> Bool
hasQuiescence m = any (isOutput . fst &&& not . isForbidden . snd) (Map.toList m)

-------------------
-- input-failure --
-------------------

instance (Ord i, Ord o) => TransitionSemantics (IOAct i o) (IFAct i o) where
    asTransition loc _ (In (Attempt (i, False))) = Nothing
    asTransition _ _ other = Just $ fromInputAttempt other
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc _ (In (Attempt (i, False))) m = Just . LocationMove $ pure loc
    takeTransition _ _ act m = TransitionMove . (fromInputAttempt act,) <$> Map.lookup (fromInputAttempt act) m

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (IFAct i o) where
    asActions t = [asInputAttempt t]
    locationActions _ = []

--------------------------------
-- input-failure + quiescence --
--------------------------------
-- Ideally this would just be the above two semantics stacked to avoid the boilerplate below, but that is a hassle

instance (Ord i, Ord o) => TransitionSemantics (IOAct i o) (TimeoutIF i o) where
    asTransition loc _ (In (Attempt (i, False))) = Nothing
    asTransition loc _ (Out Timeout) = Nothing
    asTransition _ _ other = Just $ fromTimeoutInputAttempt other
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc _ (In (Attempt (i, False))) m = Just . LocationMove $ pure loc
    takeTransition loc _ (Out Timeout) m = Just . LocationMove $ if hasQuiescence m then forbidden else pure loc
    takeTransition _ _ act m = TransitionMove . (fromTimeoutInputAttempt act,) <$> Map.lookup (fromTimeoutInputAttempt act) m

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (TimeoutIF i o) where
    asActions t = [asTimeoutInputAttempt t]
    locationActions _ = [Out Timeout]

--------------------------------
-- STS interpretation --
--------------------------------

data IntrpState a = IntrpState a Valuation deriving (Eq, Ord, Show)

type Valuation = (Map Variable Value)

evaluate :: SymExpr -> GSymPrim.Model -> Value
evaluate (BoolExpr expr) valuation = BoolVal (Grisette.evalSymToCon valuation expr :: Bool)
evaluate (IntExpr expr) valuation = IntVal (Grisette.evalSymToCon valuation expr :: Integer)

instance (Observable (GateValue i o)) where
    implicitDestination (GateValue (OutputGate _) _) = forbidden
    implicitDestination _ = underspecified

instance StateSemantics a (IntrpState a) where
    asLoc (IntrpState l _) = l

instance (Ord i, Ord o) => TransitionSemantics (SymInteract i o) (GateValue i o) where
    asTransition _ alf (GateValue gate values) =
        case List.find (\(SymInteract g vars) -> g == gate) (Set.toList alf) of
            Nothing -> errorWithoutStackTrace $ "gate not in STS alphabet"
            Just i@(SymInteract g vars) ->
                if List.length values /= List.length vars
                    then errorWithoutStackTrace $ "nr of values unequal to nr of parameters"
                    else if List.all (\(var,val) -> equalTyped var val) (zip vars values)
                            then Just i
                            else errorWithoutStackTrace "type of variable and value do not match"


instance (Ord i, Ord o, Ord loc, StateConfiguration m) => AutomatonSemantics m loc (IntrpState loc) (SymInteract i o) (SymGuard,SymAssign) (GateValue i o) where
    after = monadicAfter $ withStep (\(IntrpState l1 varMap) gv@(GateValue g ws) (Just (SymInteract g2 ps, (guard,assign))) l2 ->
        let pValuation = List.foldr (\(v,w) m -> addTypedVar v w m) Grisette.emptyModel (zip ps ws)
            valuation = Map.foldrWithKey (\x xval m -> addTypedVar x xval m) pValuation varMap
        in if not $ Grisette.evalSymToCon valuation guard -- guard is false
            then implicitDestination gv
            else let varMap2 = Map.mapWithKey (\v@(Variable x t) xval -> case Map.lookup v assign of
                                                    Nothing -> xval
                                                    Just assignExpr -> evaluate assignExpr valuation) varMap
                 in return $ IntrpState l2 varMap2)

-------------------------
-- Auxiliary functions --
-------------------------

{- |
    Compute the set of locations that is syntactically reachable from the initial location configuration. See `reachableFrom`.
-}
reachable :: (Ord loc, Foldable m) => AutSyn m loc t tloc -> Set loc
reachable aut = reachableFrom aut $ locConf aut

{- |
    Compute the set of locations that is syntactically reachable from the given locations.
    
    Note that this not involve any interpretation of the automaton, e.g. if a location of symbolic automaton is only reachable via a transition with
    a guard that is always `False`, then that location is still considered to be reachable, even if a symbolic interpretation of that automaton
    can never reach that location for any trace of concrete values.
-}
reachableFrom :: (Ord loc, Foldable m, Foldable f) => AutSyn m loc t tloc -> f loc -> Set loc
reachableFrom aut locations = reachableFrom' Set.empty $ Set.fromList $ Foldable.toList locations
    where
    reachableFrom' acc boundary = case takeArbitrary boundary of
        Nothing -> acc -- done, no more new states to explore
        Just (q, boundaryRem) -> -- explore the states reached by transitions from q
            let ts = transRel aut q
                qs = Set.fromList $ concat $ fmap snd . Foldable.toList <$> Map.elems ts
                new = qs `Set.difference` acc
                acc' = acc `Set.union` new
                boundary' = boundaryRem `Set.union` new
            in reachableFrom' acc' boundary'




