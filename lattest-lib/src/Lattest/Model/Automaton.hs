{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-|
    This module contains the definitions and interpretations of automata models.
-}

module Lattest.Model.Automaton (
-- * Syntactical Automaton Model
-- ** Definition
AutSyntax,
initConf,
alphabet,
trans,
transRel,
-- ** Constructing Syntactical Automata
automaton,
automaton',
-- * Semantical Automaton Model
-- ** Definition
AutIntrpr,
stateConf,
syntacticAutomaton,
-- ** Constructing Syntactical Automata
interpret,
-- ** Type Classes for Semantics
Completable,
implicitDestination,
TransitionSemantics,
StateSemantics,
StepSemantics,
after,
afters,
-- ** Exceptions
AutomatonException(..),
-- ** Finite Transition Labels
FiniteMenu,
specifiedMenu,
-- ** STS State data types
IntrpState(..),
Valuation,
STStdest,
stsTLoc,
-- * Auxiliary Automaton Functions
reachable,
reachableFrom,
prettyPrint,
prettyPrintFrom,
prettyPrintIntrp,
determinize
)
where

import Prelude hiding (lookup)

import Lattest.Model.BoundedMonad(BoundedApplicative, BoundedMonad, BoundedConfiguration, isForbidden, forbidden, underspecified, isSpecified)
import qualified Lattest.Model.BoundedMonad as BM (determinize, undeterminize,Det)
import Lattest.Model.Alphabet(IOAct(In,Out),isOutput,IOSuspAct,Suspended(Quiescence),IFAct(..),InputAttempt(..),fromSuspended,asSuspended,fromInputAttempt,asInputAttempt,SuspendedIF,asSuspendedInputAttempt,fromSuspendedInputAttempt,
    SymInteract(..),GateValue(..),Value(..), SymGuard, SymAssign,Variable,addTypedVar,Variable(..),Type(..),SymExpr(..),Gate(..),equalTyped,assignedExpr)
import Lattest.Util.Utils((&&&), takeArbitrary)
import Control.Exception(throw,Exception)
import qualified Control.Monad as Monad(join)
import qualified Data.Foldable as Foldable
import Data.Map (Map, (!))
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tuple.Extra(first)
import GHC.OldList(find)
import GHC.Stack(CallStack,callStack)
import Grisette.Core as Grisette
import Grisette.SymPrim as GSymPrim

------------
-- syntax --
------------

{- |
    Syntactical automaton model, with locations and transitions. This is analogous to an automaton drawn on paper
    with points and arrows. Transitions are mapped to /state configurations/, see "Lattest.Model.BoundedMonad".
    Furthermore, transitions contain transition labels, both on the 'outside' and in the 'inside' of the state configuration.
    
    These labels are abstract and may be interpreted in various ways, e.g. a simple automaton model may directly have
    observable actions as labels, whereas a more complex automaton model may have symbolic data variables with guards,
    assignments, clocks for timing, etc.
-}
data AutSyntax m loc t tdest = Automaton {
    initConf :: m loc,
    alphabet :: Set t,
    transRel :: loc -> Map t (m (tdest, loc))
    }

-- | Construct an automaton from an initial state configuration and a transition mapping
automaton :: (BoundedConfiguration m, Completable t, Ord t, Foldable fld) => m loc -> fld t -> (loc -> Map t (m (tdest, loc))) -> AutSyntax m loc t tdest
automaton mqi alphFld trans = Automaton mqi alph trans'
    where -- FIXME t is now Completable, in other functions we expect actions instead of transitions to be Completable.
          -- some alternatives: instead of forbidden, just throw an error (not nice), or add a separate class for transitions
    alph = Set.fromList $ Foldable.toList alphFld
    trans' q = Map.restrictKeys (trans q) alph `Map.union` setToList alph implicitDestination -- left-biased union 
    setToList s f = Set.foldr (\k -> Map.insert k (f k)) Map.empty s

-- | Construct an automaton from an initial state and a transition mapping
automaton' :: (BoundedApplicative m, Completable t, Ord t) => loc -> Set t -> (loc -> Map t (m (tdest, loc))) -> AutSyntax m loc t tdest
automaton' = automaton . pure

{- |
    The transition relation as a function. Note that this function is partial, and only defined for transition labels in the alphabet of the
    automaton.
-}
trans :: Ord t => AutSyntax m loc t tdest -> loc -> t -> m (tdest, loc)
trans aut loc t = case Map.lookup t (transRel aut loc) of
    Just x -> x
    Nothing -> error "transition function only defined for transition labels in the automaton alphabet"

---------------
-- interpret --
---------------

{- |
    Semantical automaton model. This model contains a reference to the syntactical automaton on which it is based,
    but it also contains a state configuration with semantical states.

    The difference between the locations from the syntactical model and the states from the semantical model depends
    on the automaton interpret. E.g. for a simple automaton model, states and locations may be the same, whereas a more
    complex automaton model may have states consisting of syntactical locations combined with valuations for data
    variables, clocks for timing, etc.
-}
data AutIntrpr m loc q t tdest act = AutInterpretation {
    stateConf :: m q,
    syntacticAutomaton :: AutSyntax m loc t tdest
    }

{- |
    Infer a semantical model from a syntactical model, based on the appropriate instance of the 'AutomatonSemantics' typeclass.
    Note that an automaton may be interpreted in multiple ways, so the type checker may need a hint on which semantical
    automaton is requested. This can be avoided by calling more specific, pre-typed variants of 'interpret' in
    "Lattest.Adapter.StandardAdapters".
-}
interpret :: (StepSemantics m loc q t tdest act) => AutSyntax m loc t tdest -> (loc -> q) -> AutIntrpr m loc q t tdest act
interpret aut initState = AutInterpretation { stateConf = initState <$> initConf aut, syntacticAutomaton = aut }

-- | The Completable typeclass defines which types can be used as labels on transitions.
class Completable act where
    {- |
        Defines the implicit state configuration reached by a given transition label if that label is omitted from 
        a syntactical automaton. E.g. if a state contains no outgoing transition for an output label, that label
        is often considered to map to the 'forbidden' state configuration.
    -}
    implicitDestination :: BoundedConfiguration m => act -> m any

{- |
    TransitionSemantics expresses that the interpret of a syntactic transition can be expressed in terms of actions. E.g. symbolic transitions with
    interaction variables that can be expressed in terms of concrete observed values.
-}
class (Ord t, Completable act) => TransitionSemantics t act where
    {- |
        Map an action to a matching transition. E.g. a concrete value on some channel that matches with the symbolic representation of that channel.
        'Nothing' indicates an action that occurs within a location, without explicit transition.
    -}
    asTransition :: loc -> Set t -> act -> Maybe t
    {- |
        Find the syntactic transition that applies for the given semantic action value, or alternatively a move within the location.
        The function may be partial, following the given alphabet.
    -}
    takeTransition :: (BoundedApplicative m) => loc -> Set t -> act -> (t -> m (tdest, loc)) -> Move m t tdest loc
    takeTransition loc alph act trans' = case asTransition loc alph act of
        Nothing -> LocationMove $ pure loc
        Just t -> TransitionMove (t, trans' t)

{- |
    Data structure needed to express that an automaton may transition from one location to another, but it may also 'transition'
    within a single state, e.g. the passing of time in a timed automaton.
-}
data Move m t tdest loc = TransitionMove (t, m (tdest, loc)) | LocationMove (m loc)

{- |
    StateSemantics expresses that the interpret of a syntactic location can be expressed in terms of state q. E.g. a location symbolic variables can be 
    given in terms of valuations of these variables.
-}
class StateSemantics loc q where
    -- | from a state, extract the corresponding location
    asLoc :: q -> loc

{- |
    StepSemantics expresses that we can move through an automaton run with state semantics by applying the transition semantics
    The transition consists of two parts: one global part outside the configuration monad (e.g. describing the action that applies to that transition),
    described by the transition semantics, and a local part inside the monad, bound to the destination state (e.g. to update symbolic variables for a state).
-}
class (StateSemantics loc q, TransitionSemantics t act, BoundedMonad m) => StepSemantics m loc q t tdest act where
    {- |
        Given the current state, an action and the transition matching that action, and a new location and local transition, produce the new state
        The case of no transition (i.e. no transition applies in the TransitionSemantics) can be used to move within a location.
    -}
    move :: q -> act -> Maybe (t, tdest) -> loc -> m q

{- |
    Take a step for the given action, according to the step semantics to move from one state configuration to another. May throw an AutomatonException.
-}
after :: StepSemantics m loc q t tdest act => AutIntrpr m loc q t tdest act -> act -> AutIntrpr m loc q t tdest act
after intrpr act' = 
    let aut = syntacticAutomaton intrpr
        stateConf' = stateConf intrpr >>= after' (alphabet aut) (transRel $ aut) act'
    in intrpr { stateConf = stateConf' }

after' :: (StepSemantics m loc q t tdest act) => Set t -> (loc -> Map t (m (tdest, loc))) -> act -> q -> m q
after' alph transMap act q = Monad.join $ case takeTransition (asLoc q) alph act (lookupAction $ transMap $ asLoc q) of
    LocationMove mloc -> move q act (nothingTTdest transMap) <$> mloc
        where
         -- ugly solution to get a Nothing of the type (Maybe (t, tdest)) without ScopedTypeVariables
        nothingTTdest :: (x1 -> Map t (x2 (tdest, x3))) -> Maybe (t, tdest)
        nothingTTdest _ = Nothing
    TransitionMove (t, mloc) -> moveAlongTransition q act t <$> mloc
        where
        moveAlongTransition q act t (tdest, loc) = move q act (Just (t, tdest)) loc
    where
    lookupAction :: Ord k => Map k a -> k -> a
    lookupAction m k = case Map.lookup k m of
        Just v -> v
        Nothing -> throw $ ActionOutsideAlphabet callStack

-- | Take a sequence of transitions for the given actions.
afters :: (StepSemantics m loc q t tdest act) => AutIntrpr m loc q t tdest act -> [act] -> AutIntrpr m loc q t tdest act
afters aut [] = aut
afters aut (act:acts) = aut `after` act `afters` acts

-- | Exceptions that can occur when working with automata.
data AutomatonException
    -- | Thrown during a computation of `after` for an action outside the automaton alphabet.
    = ActionOutsideAlphabet CallStack
    deriving (Show)
instance Eq AutomatonException where
    (==) (ActionOutsideAlphabet _) (ActionOutsideAlphabet _) = True
    (==) _ _ = False
instance Ord AutomatonException where
    (<=) (ActionOutsideAlphabet _) (ActionOutsideAlphabet _) = True
    (<=) _ _ = False

instance Exception AutomatonException

------------------------------------------------------------------
-- utility function to obtain the menu of outgoing transitions --
------------------------------------------------------------------
-- note: this only shows the transitions that are syntactically present in the automaton, so e.g. not quiescence, including underspecified/forbidden transitions
transMenu :: (Foldable m, Functor m, Ord t) => AutSyntax m mloc t tdest -> Set t
transMenu aut = let
    stateToMenu = Set.fromList . Map.keys . transRel aut
    in Set.unions $ stateToMenu <$> initConf aut

{-|
    The class of automata with a finite list of transition labels on outgoing transitions for every state.
    This property is useful for e.g. test selection.
-}
class TransitionSemantics t act => FiniteMenu t act where
    -- menu of actions that are semantically present in the automaton, including underspecified/forbidden transitions
    asActions :: t -> [act]
    locationActions :: AutSyntax m mloc t tdest -> [act]

actionMenu :: (Foldable m, Functor m, Ord t) => FiniteMenu t act => BoundedApplicative m => AutSyntax m mloc t tdest -> [act]
actionMenu aut = (locationActions aut ++) $ concat $ fmap asActions $ Set.toList $ transMenu aut

-- | Menu of specified actions that are semantically present in the automaton.
specifiedMenu :: (StepSemantics m loc q t tdest act, Foldable m, Ord t) => FiniteMenu t act => AutIntrpr m loc q t tdest act -> [act]
specifiedMenu aut = [act | act <- actionMenu $ syntacticAutomaton aut, isSpecified $ stateConf $ aut `after` act]

-----------------------------------------------------------------------------------------------
-- special case where the semantic states and actions are directly represented syntactically --
-----------------------------------------------------------------------------------------------

instance (Completable act) where
    implicitDestination _ = forbidden

instance (Ord act) => TransitionSemantics act act where
    asTransition _ _ = Just

instance (Ord act) => FiniteMenu act act where
    asActions t = [t] 
    locationActions _ = []

instance StateSemantics q q where
    asLoc = id

instance (TransitionSemantics t act, BoundedMonad m) => StepSemantics m q q t () act where
    move _ _ _ q = pure q

----------------
-- quiescence --
----------------
instance (Completable (IOAct i o)) where
    implicitDestination (Out _) = forbidden
    implicitDestination _ = underspecified

instance (Ord i, Ord o) => TransitionSemantics (IOAct i o) (IOSuspAct i o) where
    asTransition loc _ (Out Quiescence) = Nothing
    asTransition _ _ other = Just $ fromSuspended other
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc alph (Out Quiescence) m = LocationMove $ if hasQuiescence (Map.fromSet m alph) then forbidden else pure loc
    takeTransition _ _ act m = TransitionMove (fromSuspended act, m $ fromSuspended act)

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (IOSuspAct i o) where
    asActions t = [asSuspended t]
    locationActions _ = [Out Quiescence]

hasQuiescence :: BoundedApplicative m => Map (IOAct i o) (m (tdest, loc)) -> Bool
hasQuiescence m = any (isOutput . fst &&& not . isForbidden . snd) (Map.toList m)

-------------------
-- input-failure --
-------------------

instance (Ord i, Ord o) => TransitionSemantics (IOAct i o) (IFAct i o) where
    asTransition loc _ (In (InputAttempt(i, False))) = Nothing
    asTransition _ _ other = Just $ fromInputAttempt other
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc _ (In (InputAttempt(i, False))) m = LocationMove $ pure loc
    takeTransition _ _ act m = TransitionMove (fromInputAttempt act, m $ fromInputAttempt act)

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (IFAct i o) where
    asActions t = [asInputAttempt t]
    locationActions _ = []

--------------------------------
-- input-failure + quiescence --
--------------------------------
-- Ideally this would just be the above two interpret stacked to avoid the boilerplate below, but that is a hassle

instance (Ord i, Ord o) => TransitionSemantics (IOAct i o) (SuspendedIF i o) where
    asTransition loc _ (In (InputAttempt(i, False))) = Nothing
    asTransition loc _ (Out Quiescence) = Nothing
    asTransition _ _ other = Just $ fromSuspendedInputAttempt other
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc _ (In (InputAttempt(i, False))) m = LocationMove $ pure loc
    takeTransition loc alph (Out Quiescence) m = LocationMove $ if hasQuiescence (Map.fromSet m alph) then forbidden else pure loc
    takeTransition _ _ act m = TransitionMove (fromSuspendedInputAttempt act, m $ fromSuspendedInputAttempt act)

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (SuspendedIF i o) where
    asActions t = [asSuspendedInputAttempt t]
    locationActions _ = [Out Quiescence]

--------------------------------
-- STS interpretation --
--------------------------------

data IntrpState a = IntrpState a Valuation deriving (Eq, Ord, Show)

type Valuation = (Map Variable Value)

newtype STStdest = STSLoc (SymGuard,SymAssign)

stsTLoc :: SymGuard -> SymAssign -> STStdest
stsTLoc g a = STSLoc (g,a)

instance Show STStdest where
    show (STSLoc (g,a)) =  "[[" ++ show g ++ "]] " ++ show a

evaluate :: SymExpr -> GSymPrim.Model -> Value
evaluate (BoolExpr expr) valuation = BoolVal (Grisette.evalSymToCon valuation expr :: Bool)
evaluate (IntExpr expr) valuation = IntVal (Grisette.evalSymToCon valuation expr :: Integer)

instance (Completable (GateValue i o)) where
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

instance (Ord i, Ord o, Ord loc, BoundedMonad m) => StepSemantics m loc (IntrpState loc) (SymInteract i o) STStdest (GateValue i o) where
    move (IntrpState l1 varMap) gv@(GateValue g ws) (Just (SymInteract g2 ps, STSLoc (guard,assign))) l2 =
        let pValuation = List.foldr (\(v,w) m -> addTypedVar v w m) Grisette.emptyModel (zip ps ws)
            valuation = Map.foldrWithKey (\x xval m -> addTypedVar x xval m) pValuation varMap
        in if not $ Grisette.evalSymToCon valuation guard -- guard is false
            then implicitDestination gv
            else let varMap2 = Map.mapWithKey (\v@(Variable x t) xval -> case assignedExpr v assign of
                                                    Nothing -> xval
                                                    Just assignExpr -> evaluate assignExpr valuation) varMap
                 in return $ IntrpState l2 varMap2

-------------------------
-- Auxiliary functions --
-------------------------

{- |
    Compute the set of locations that is syntactically reachable from the initial location configuration. See `reachableFrom`.
-}
reachable :: (Ord loc, Foldable m) => AutSyntax m loc t tdest -> Set loc
reachable aut = reachableFrom aut $ initConf aut

{- |
    Compute the set of locations that is syntactically reachable from the given locations.
    
    Note that this not involve any interpretation of the automaton, e.g. if a location of symbolic automaton is only reachable via a transition with
    a guard that is always `False`, then that location is still considered to be reachable, even if a symbolic interpretation of that automaton
    can never reach that location for any trace of concrete values.
-}
reachableFrom :: (Ord loc, Foldable m, Foldable f) => AutSyntax m loc t tdest -> f loc -> Set loc
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

prettyPrint :: (Show (m (tdest, loc)), Show (m loc), Show loc, Show t, Ord loc, Foldable m) => AutSyntax m loc t tdest -> String
prettyPrint aut = prettyPrintFrom aut (initConf aut)

prettyPrintFrom :: (Show (m (tdest, loc)), Show (m loc), Show loc, Show t, Ord loc, Foldable m, Foldable f) => AutSyntax m loc t tdest -> f loc -> String
prettyPrintFrom aut fromLocs = "initial location configuration: " ++ printInitial ++ "\nlocations: " ++ printLocations ++ "\ntransitions:\n" ++ printTransitions
    where
    locations = Set.toList $ reachableFrom aut fromLocs
    printInitial = show $ initConf aut
    printLocations = List.intercalate ", " (show <$> locations)
    printTransitions = List.intercalate "\n" (printTransitionsFrom <$> locations)
    printTransitionsFrom q = List.intercalate "\n" (printTransition q <$> Map.toList (transRel aut q))
    printTransition q (t, mt) = show q ++ " ――" ++ show t ++ "⟶ " ++ show mt
    
prettyPrintIntrp :: (Show (m (tdest, loc)), Show (m loc), Show loc, Show (m q), Show t, Ord loc, Foldable m) => AutIntrpr m loc q t tdest act -> String
prettyPrintIntrp intrp = "current state configuration: " ++ printStateConf ++ "\n" ++ printAut
    where
    printStateConf = show $ stateConf intrp
    printAut = prettyPrint $ syntacticAutomaton intrp
{-
data AutSyntax m loc t tdest = Automaton {
    initConf :: m loc,
    alphabet :: Set t,
    transRel :: loc -> Map t (m (tdest, loc))
    }
-}
determinize :: BoundedConfiguration m => AutSyntax m loc t () -> AutSyntax BM.Det (m loc) t () -- TODO think about whether the () could also be polymorphic: does determinization make sense for e.g. STSes?
determinize aut = Automaton {
    initConf = BM.determinize $ initConf aut,
    alphabet = alphabet aut, 
    transRel = \mloc ->
        let ft = \t -> addTDest <$> BM.determinize $ takeMTransition t mloc
        in transitionsAsMap ft
    }
    where
    takeMTransition t mloc = BM.undeterminize $ fmap stripTDest $ Monad.join (takeTransition t <$> mloc)  -- t -> m loc -> m loc
    takeTransition t loc = (transRel aut loc Map.! t) -- t -> loc -> m loc
    transitionsAsMap ft = Map.fromSet ft $ alphabet aut -- :: (t -> a) -> Map t a
    addTDest loc = ((), loc)
    stripTDest ((), loc) = loc

-- transRel     :: m loc -> Map t (Det ((), m loc))
-- transRel aut :: loc ->   Map t (m (tdest, loc))
-- transRel aut <$> transRel :: m (Map t (m (tdest, loc)))
-- \mloc -> transitionsAsMap f -- f :: t -> Det ((), m loc)
--f = \t -> BM.determinize mloc

-- fromSet :: (k -> a) -> Set k -> Map k a
-- transitionsAsMap = swap fromSet (alphabet aut) :: (t -> a) -> Map t a

--BM.determinize :: BoundedConfiguration m => m loc -> Det (m loc)
--BM.undeterminize :: BoundedConfiguration m => Det (m q) -> m q -- TODO better name?





