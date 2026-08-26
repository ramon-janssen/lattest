{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}

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
inConfiguration,
-- ** Type Classes for Semantics
Completable,
implicitDestination,
TransitionSemantics,
StateSemantics,
StepSemantics,
after,
afters,
After,
IOAfter,
ioAfter,
-- ** Exceptions
AutomatonException(..),
-- ** Finite Transition Labels
FiniteMenu,
specifiedMenu,
-- ** STS State data types
IntrpState(..),
Valuation,
STStdest(STSLoc),
stsTLoc,
-- * Auxiliary Automaton Functions
reachable,
reachableFrom,
allLocations,
prettyPrint,
prettyPrintFrom,
prettyPrintIntrp,
-- * Sequential Composition
sequentiallyAt,
(|>),
selfSequentiallyAt,
(|>>),
-- * Conjunction and Disjunction Helpers
(//\\),
(\\//),
conjunctionAll,
disjunctionAll,
-- * Output-Check Completion
CheckLoc(..),
prependOutputChecks
)
where

import Prelude hiding (lookup)

import Lattest.Model.BoundedMonad(BoundedMonad, BoundedConfiguration, BooleanConfiguration, isForbidden, forbidden, underspecified, isSpecified, MeetSemiLattice, JoinSemiLattice, (/\), (\/))
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.Alphabet(IOAct(In,Out),isOutput,IOSuspAct,Suspended(Quiescence),IFAct,InputAttempt(..),fromSuspended,asSuspended,fromInputAttempt,asInputAttempt,SuspendedIF,asSuspendedInputAttempt,fromSuspendedInputAttempt,
    SymInteract(..),IOSymInteract,GateValue(..), IOGateValue, IOSuspGateValue, IFGateValue, SuspendedIFGateValue, SymGuard, isOutputInteract, interactionGate)
import Lattest.Model.Symbolic.SolveSymPrim(combineGuards, substituteInGuard, evaluateGuard, solveAnySequential)
import Lattest.SMT(runSMT)
import Lattest.Util.Utils((&&&), takeArbitrary)

import Control.Exception(throw,Exception)

import Control.Arrow(second)

import qualified Data.Foldable as Foldable
import Data.Functor.Identity(Identity(Identity), runIdentity)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import GHC.Stack(CallStack,callStack)
import Lattest.Model.Symbolic.Expr(Valuation, VarModel, Variable(..),Type(..),Expr(..), eval, constType, varType, substConst, assignedExpr, Constant(..), toBool, fromConstantsMap, toConstantsMap, assignValues, insertIntoValuation, toConst, ConstType, Assignable, noAssignment, sTrue)

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
automaton mqi alphFld transRel' = Automaton mqi alph trans'
    where -- FIXME t is now Completable, in other functions we expect actions instead of transitions to be Completable.
          -- some alternatives: instead of forbidden, just throw an error (not nice), or add a separate class for transitions
    alph = Set.fromList $ Foldable.toList alphFld
    trans' q = Map.restrictKeys (transRel' q) alph `Map.union` setToList alph implicitDestination -- left-biased union
    setToList s f = Set.foldr (\k -> Map.insert k (f k)) Map.empty s

-- | Construct an automaton from an initial state and a transition mapping
automaton' :: (BoundedMonad m, Completable t, Ord t) => loc -> Set t -> (loc -> Map t (m (tdest, loc))) -> AutSyntax m loc t tdest
automaton' = automaton . BM.ordReturn

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
interpret :: (StepSemantics m loc q t tdest act, Ord q) => AutSyntax m loc t tdest -> (loc -> q) -> AutIntrpr m loc q t tdest act
interpret aut initState = AutInterpretation { stateConf = initState BM.<#> initConf aut, syntacticAutomaton = aut }

-- | The given model, in the given configuration.
inConfiguration :: AutIntrpr m loc q t tdest act -> m q -> AutIntrpr m loc q t tdest act
inConfiguration aut conf = aut {stateConf = conf}

-- | The Completable typeclass defines which types can be used as labels on transitions.
class Completable act where
    {- |
        Defines the implicit state configuration reached by a given transition label if that label is omitted from 
        a syntactical automaton. E.g. if a state contains no outgoing transition for an output label, that label
        is often considered to map to the 'forbidden' state configuration.
    -}
    implicitDestination :: BoundedConfiguration m => act -> m any

class TransitionMapping t act where
    {- |
        Map an action to a matching transition. E.g. a concrete value on some channel that matches with the symbolic representation of that channel.
        'Nothing' indicates an action that occurs within a location, without explicit transition.
    -}
    asTransition :: Set t -> act -> Maybe t

{- |
    TransitionSemantics expresses that the interpret of a syntactic transition can be expressed in terms of actions. E.g. symbolic transitions with
    interaction variables that can be expressed in terms of concrete observed values.
-}
class (Ord t, Completable act, TransitionMapping t act, StateSemantics loc q) => TransitionSemantics loc q t tdest act | t act -> tdest where
    {- |
        Find the syntactic transition that applies for the given semantic action value, or alternatively a move within the location.
        The function may be partial, following the given alphabet.
    -}
    takeTransition :: (BoundedMonad m) => q -> Set t -> act -> (t -> m (tdest, loc)) -> Move m t tdest loc
    takeTransition q alph act trans' = case asTransition alph act of
        Nothing -> LocationMove $ BM.ordReturn $ asLoc q
        Just t -> TransitionMove (t, trans' t)

class (Ord t, Completable act, TransitionMapping t act, StateSemantics loc q) => IOTransitionSemantics loc q t tdest act | t act -> tdest where
    {- |
        Find the syntactic transition that applies for the given semantic action value, or alternatively a move within the location.
        The function may be partial, following the given alphabet.
    -}
    ioTakeTransition :: (BoundedMonad m, BooleanConfiguration m) => q -> Set t -> act -> (t -> m (tdest, loc)) -> IO (Move m t tdest loc)
    ioTakeTransition q alph act trans' = return $ case asTransition alph act of
        Nothing -> LocationMove $ BM.ordReturn (asLoc q)
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
class (StateSemantics loc q, BoundedMonad m) => StepSemantics m loc q t tdest act where
    {- |
        Given the current state, an action and the transition matching that action, and a new location and local transition, produce the new state
        The case of no transition (i.e. no transition applies in the TransitionSemantics) can be used to move within a location.
    -}
    move :: q -> act -> Maybe (t, tdest) -> loc -> m q

type After m loc q t tdest act = (StepSemantics m loc q t tdest act, TransitionSemantics loc q t tdest act, Ord t)

{- |
    Take a step for the given action, according to the step semantics to move from one state configuration to another. May throw an AutomatonException.
-}
after :: (After m loc q t tdest act, Ord (m q), Ord q) => AutIntrpr m loc q t tdest act -> act -> AutIntrpr m loc q t tdest act
after aut act = runIdentity $ afterInternal takeTransitionId fmapId aut act
    where
    takeTransitionId :: (BoundedMonad m, TransitionSemantics loc q t tdest act) => q -> Set t -> act -> (t -> m (tdest, loc)) -> Identity (Move m t tdest loc)
    takeTransitionId q alph act' trans' = Identity $ takeTransition q alph act' trans'
    fmapId :: (BM.OrdFunctor f, Ord y) => (x -> Identity y) -> f x -> Identity (f y)
    fmapId f = Identity . BM.ordMap (runIdentity . f)

class IOAfter m loc q t tdest act where
    ioAfter :: AutIntrpr m loc q t tdest act -> act -> IO (AutIntrpr m loc q t tdest act)

-- tdest ~ () <=> LTS
instance (After m loc q t () act, Ord (m q), Ord q) => IOAfter m loc q t () act where
    ioAfter aut act = return $ after aut act

-- tdest ~ STStdest <=> STS
instance (StepSemantics m loc q t STStdest act, IOTransitionSemantics loc q t STStdest act, BooleanConfiguration m, Ord q, Ord t, Ord (m q), BM.OrdTraversable m) => IOAfter m loc q t STStdest act where
    ioAfter = afterInternal ioTakeTransition BM.ordTraverse

--takeTransition :: (BoundedMonad m) => q -> Set t -> act -> (t -> m (tdest, loc)) -> Move m t tdest loc
--ioTakeTransition :: (BoundedMonad m) => q -> Set t -> act -> (t -> m (tdest, loc)) -> IO (Move m t tdest loc)

-- distributeMonadOverFoldable :: (Functor m, Foldable m, Monad execM, Ord x) => (x -> execM y) -> m x -> execM (m y)
-- fmapInternal?? :: (Functor m, Monad execM) => (x -> execM y) -> m x -> execM (m y)
afterInternal :: (StepSemantics m loc q t tdest act, Monad execM, Ord t, Ord q, Ord (m q)) =>
    (q -> Set t -> act -> (t -> m (tdest, loc)) -> execM (Move m t tdest loc)) ->
    ((q -> execM (m q)) -> m q -> execM (m (m q))) ->
    AutIntrpr m loc q t tdest act -> act -> execM (AutIntrpr m loc q t tdest act)
afterInternal internalTakeTransition fmapmq intrpr act' = do
    let aut = syntacticAutomaton intrpr
        toNewStateConfig = afterInternal' internalTakeTransition (alphabet aut) (transRel aut) act'
    stateConf' <- toNewStateConfig `fmapmq` stateConf intrpr
    return $ intrpr { stateConf = BM.ordJoin stateConf' }
{-
after :: (StepSemantics m loc q t tdest act, Ord q, Ord (m q)) => AutIntrpr m loc q t tdest act -> act -> AutIntrpr m loc q t tdest act
after intrpr act' = 
    let aut = syntacticAutomaton intrpr
        stateConf' = BM.ordBind (stateConf intrpr) (after' (alphabet aut) (transRel $ aut) act')
    in intrpr { stateConf = stateConf' }
    -}

afterInternal' :: (StepSemantics m loc q t tdest act, Ord t, Ord q, Ord (m q), Monad execM) =>
    (q -> Set t -> act -> (t -> m (tdest, loc)) -> execM (Move m t tdest loc)) ->
    Set t -> (loc -> Map t (m (tdest, loc))) -> act -> q -> execM (m q)
afterInternal' internalTakeTransition alph transMap act q = do
    t <- internalTakeTransition q alph act (lookupAction $ transMap $ asLoc q)
    --Monad.join <$> case t of
    return $ BM.ordJoin $ case t of
        LocationMove mloc -> move q act (nothingTTdest transMap) BM.<#> mloc
            where
            -- ugly solution to get a Nothing of the type (Maybe (t, tdest)) without ScopedTypeVariables
            nothingTTdest :: (x1 -> Map t (x2 (tdest, x3))) -> Maybe (t, tdest)
            nothingTTdest _ = Nothing
        TransitionMove (t', mtdestloc) -> moveAlongTransition q act t' BM.<#> mtdestloc
            where
            moveAlongTransition :: (StepSemantics m loc q t tdest act) => q -> act -> t -> (tdest, loc) -> m q
            moveAlongTransition q' act' t'' (tdest, loc) = move q' act' (Just (t'', tdest)) loc
        where
        lookupAction :: Ord k => Map k a -> k -> a
        lookupAction m k = case Map.lookup k m of
            Just v -> v
            Nothing -> throw $ ActionOutsideAlphabet callStack
{-
after' :: (StepSemantics m loc q t tdest act) => Set t -> (loc -> Map t (m (tdest, loc))) -> act -> q -> m q
after' alph transMap act q = BM.ordJoin $ case takeTransition (asLoc q) alph act (lookupAction $ transMap $ asLoc q) of
    LocationMove mloc -> move q act (nothingTTdest transMap) BM.<#> mloc
        where
         -- ugly solution to get a Nothing of the type (Maybe (t, tdest)) without ScopedTypeVariables
        nothingTTdest :: (x1 -> Map t (x2 (tdest, x3))) -> Maybe (t, tdest)
        nothingTTdest _ = Nothing
    TransitionMove (t, mloc) -> moveAlongTransition q act t BM.<#> mloc
        where
        moveAlongTransition q act t (tdest, loc) = move q act (Just (t, tdest)) loc
    where
    lookupAction :: Ord k => Map k a -> k -> a
    lookupAction m k = case Map.lookup k m of
        Just v -> v
        Nothing -> throw $ ActionOutsideAlphabet callStack
-}

-- | Take a sequence of transitions for the given actions.
afters :: (StepSemantics m loc q t tdest act, TransitionSemantics loc q t tdest act, Ord q, Ord (m q)) => AutIntrpr m loc q t tdest act -> [act] -> AutIntrpr m loc q t tdest act
afters aut [] = aut
afters aut (act:acts) = aut `after` act `afters` acts

-- | Exceptions that can occur when working with automata.
newtype AutomatonException
    -- | Thrown during a computation of `after` for an action outside the automaton alphabet.
    = ActionOutsideAlphabet CallStack
    deriving (Show)
instance Eq AutomatonException where
    (==) (ActionOutsideAlphabet _) (ActionOutsideAlphabet _) = True
instance Ord AutomatonException where
    (<=) (ActionOutsideAlphabet _) (ActionOutsideAlphabet _) = True

instance Exception AutomatonException

------------------------------------------------------------------
-- utility function to obtain the menu of outgoing transitions --
------------------------------------------------------------------
-- note: this only shows the transitions that are syntactically present in the automaton, so e.g. not quiescence, including underspecified/forbidden transitions
transMenu :: (Foldable m, BM.OrdFunctor m, Ord t) => AutSyntax m mloc t tdest -> Set t
transMenu aut = let
    stateToMenu = Set.fromList . Map.keys . transRel aut
    in Set.unions $ stateToMenu BM.<#> initConf aut

{-|
    The class of automata with a finite list of concrete actions matching to outgoing transitions for every state.
    This property is useful for e.g. test selection.
-}
class TransitionMapping t act => FiniteMenu t act where
    -- menu of actions that are semantically present in the automaton, including underspecified/forbidden transitions
    asActions :: t -> [act]
    locationActions :: AutSyntax m mloc t tdest -> [act]

actionMenu :: (Foldable m, Ord t, Ord act, FiniteMenu t act, BoundedMonad m) => AutSyntax m mloc t tdest -> [act]
actionMenu aut = (locationActions aut ++) $ concat $ BM.ordMap asActions $ Set.toList $ transMenu aut

-- | Menu of specified actions that are semantically present in the automaton.
specifiedMenu :: (StepSemantics m loc q t tdest act, TransitionSemantics loc q t tdest act, Foldable m, Ord act, Ord q, Ord (m q), FiniteMenu t act)
    => AutIntrpr m loc q t tdest act -> [act]
specifiedMenu aut = [act | act <- actionMenu $ syntacticAutomaton aut, isSpecified $ stateConf $ aut `after` act]

-----------------------------------------------------------------------------------------------
-- special case where the semantic states and actions are directly represented syntactically --
-----------------------------------------------------------------------------------------------

instance {-# OVERLAPPABLE #-} (Completable act) where
    implicitDestination _ = forbidden

instance TransitionMapping act act where
    asTransition _ = Just

instance (Ord act, Completable act) => TransitionSemantics q q act () act

instance FiniteMenu act act where
    asActions t = [t]
    locationActions _ = []

instance StateSemantics q q where
    asLoc = id

instance (TransitionSemantics q q t () act, BoundedMonad m) => StepSemantics m q q t () act where
    move _ _ _ = BM.ordReturn

----------------
-- quiescence --
----------------
instance (Completable (IOAct i o)) where
    implicitDestination (Out _) = forbidden
    implicitDestination _ = underspecified

instance TransitionMapping (IOAct i o) (IOSuspAct i o) where
    asTransition _ (Out Quiescence) = Nothing
    asTransition _ other = Just $ fromSuspended other

instance (Ord i, Ord o) => TransitionSemantics q q (IOAct i o) () (IOSuspAct i o) where
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc alph (Out Quiescence) m = LocationMove $ if hasQuiescence (Map.fromSet m alph) then BM.ordReturn loc else forbidden
    takeTransition _ _ act m = TransitionMove (fromSuspended act, m $ fromSuspended act)

instance FiniteMenu (IOAct i o) (IOSuspAct i o) where
    asActions t = [asSuspended t]
    locationActions _ = [Out Quiescence]

hasQuiescence :: BoundedMonad m => Map (IOAct i o) (m (tdest, loc)) -> Bool
hasQuiescence m = not $ any (isOutput . fst &&& not . isForbidden . snd) (Map.toList m)

-------------------
-- input-failure --
-------------------

instance TransitionMapping (IOAct i o) (IFAct i o) where
    asTransition _ (In (InputAttempt(_, False))) = Nothing
    asTransition _ other = Just $ fromInputAttempt other

instance (Ord i, Ord o) => TransitionSemantics  q q (IOAct i o) () (IFAct i o) where
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition _ _ (In (InputAttempt(i, False))) m =
        let mtdestloc = m $ In i
        in LocationMove $ if isSpecified mtdestloc
            then forbidden -- if ?i is specified, then the failure of ?i is forbidden
            else underspecified -- input failure is not repetitive: it is allowed, and nothing can be done afterwards, i.e., underspecified
    takeTransition _ _ act' m = TransitionMove (fromInputAttempt act', m $ fromInputAttempt act')

instance FiniteMenu (IOAct i o) (IFAct i o) where
    asActions t = [asInputAttempt t]
    locationActions _ = []

--------------------------------
-- input-failure + quiescence --
--------------------------------
-- Ideally this would automatically follow from the above two interpretations stacked to avoid the boilerplate below, but that is a hassle

instance TransitionMapping (IOAct i o) (SuspendedIF i o) where
    asTransition _ (In (InputAttempt(_, False))) = Nothing
    asTransition _ (Out Quiescence) = Nothing
    asTransition _ other = Just $ fromSuspendedInputAttempt other

instance (Ord i, Ord o) => TransitionSemantics q q (IOAct i o) () (SuspendedIF i o) where
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition _ _ (In (InputAttempt(i, False))) m =
        let mtdestloc = m $ In i
        in LocationMove $ if isSpecified mtdestloc
            then forbidden -- if ?i is specified, then the failure of ?i is forbidden
            else underspecified -- input failure is not repetitive: it is allowed, and nothing can be done afterwards, i.e., underspecified

    takeTransition loc alph (Out Quiescence) m = LocationMove $ if hasQuiescence (Map.fromSet m alph) then forbidden else BM.ordReturn loc
    takeTransition _ _ act m = TransitionMove (fromSuspendedInputAttempt act, m $ fromSuspendedInputAttempt act)

instance FiniteMenu (IOAct i o) (SuspendedIF i o) where
    asActions t = [asSuspendedInputAttempt t]
    locationActions _ = [Out Quiescence]

--------------------------------
-- STS interpretation --
--------------------------------

data IntrpState a = IntrpState a Valuation deriving (Eq, Ord)

instance Show a => Show (IntrpState a) where
    show (IntrpState a v) = show (a,v)

newtype STStdest = STSLoc (SymGuard,VarModel) deriving (Eq, Ord)

stsTLoc :: SymGuard -> VarModel -> STStdest
stsTLoc g a = STSLoc (g,a)

instance Show STStdest where
    show (STSLoc (g,a)) =  show g ++ ", " ++ show a

instance Completable (IOGateValue i o) where
    implicitDestination (GateValue g _) = implicitDestination g

instance Completable (IOSymInteract i o) where
    implicitDestination (SymInteract g _ ) = implicitDestination g

instance StateSemantics a (IntrpState a) where
    asLoc (IntrpState l _) = l

instance (Ord g, TransitionMapping g g') => TransitionMapping (SymInteract g) (GateValue g') where
    asTransition interactions (GateValue g vals) = do
        let ts = Set.map interactionGate interactions
        ig' <- asTransition ts g
        case List.find (\(SymInteract ig _) -> ig == ig') (Set.toList interactions) of
            Nothing -> errorWithoutStackTrace "gate not in STS alphabet"
            Just i@(SymInteract _ vars) ->
                if List.length vals /= List.length vars
                    then errorWithoutStackTrace $
                      "nr of values unequal to nr of parameters: " <> show (List.length vals) <> " values and " <> show (List.length vars) <> " variables"
                    else if List.all (\(var,val) -> varType var == constType val) (zip vars vals)
                            then Just i
                            else errorWithoutStackTrace $
                              "type of variable and value do not match. Variables: " <> show vars <> ", Values: " <> show vals

instance (Completable (GateValue g'), Ord g, TransitionMapping g g') => TransitionSemantics loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') where

instance (Completable (GateValue g'), BoundedMonad m) => StepSemantics m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') where
    move (IntrpState _l1 stateValuation) gv@(GateValue _ gateVals) (Just (SymInteract _ gateVars, STSLoc (guard,assign))) l2 =
        let gateValuation = buildGateValuation gateVars gateVals
            -- valuation = Map.foldrWithKey (\x xval m -> insertIntoValuation x xval m) gateValuation stateValuation
            valuation = fromConstantsMap $ toConstantsMap stateValuation `Map.union` toConstantsMap gateValuation
        in if not $ evalBool valuation guard
            then implicitDestination gv
            else let stateValuation2 = Map.mapWithKey (\var val -> assignNewValue var val valuation assign) $ toConstantsMap stateValuation
                 in BM.ordReturn $ IntrpState l2 $ fromConstantsMap stateValuation2
        where
        assignNewValue :: Variable -> Constant -> Valuation -> VarModel -> Constant
        -- the following case distinctino could be removed if constants were also typed
        assignNewValue var@(Variable _ IntType) oldVal val' assign' = maybe oldVal (evalVal val') (assignedExpr var assign' :: Maybe (Expr Integer))
        assignNewValue var@(Variable _ BoolType) oldVal val' assign' = maybe oldVal (evalVal val') (assignedExpr var assign' :: Maybe (Expr Bool))
        assignNewValue var@(Variable _ StringType) oldVal val' assign' = maybe oldVal (evalVal val') (assignedExpr var assign' :: Maybe (Expr String))
        assignNewValue var@(Variable _ FloatType) oldVal val' assign' = maybe oldVal (evalVal val') (assignedExpr var assign' :: Maybe (Expr Double))
    move (IntrpState _ stateValuation) _ Nothing l2 = BM.ordReturn (IntrpState l2 stateValuation) -- TODO check if this is correct
buildGateValuation :: [Variable] -> [Constant] -> Valuation
--buildGateValuation gateVars gateVals = List.foldr (\(gateVar,gateVal) m -> insertIntoValuation gateVar gateVal m) (Map.empty) (zip gateVars gateVals)
buildGateValuation gateVars gateVals = assignValues $ (\(gateVar,gateVal) m -> insertIntoValuation gateVar gateVal m) <$> zip gateVars gateVals
evalVal :: (ConstType t, Assignable t) => Valuation -> Expr t -> Constant
evalVal valuation e = case eval $ substConst valuation e of
    Right v -> toConst v
    Left m -> error $ "evalVal: " ++ m
evalBool :: Valuation -> Expr Bool -> Bool
evalBool valuation = toBool . evalVal valuation

--------------------
-- STS quiescence --
--------------------
instance (Ord i, Ord o) => IOTransitionSemantics loc (IntrpState loc) (IOSymInteract i o) STStdest (IOSuspGateValue i o) where
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    -- TODO do something with the values (now "_"), even if just throwin an exception if non-empty
    ioTakeTransition (IntrpState loc stateVal) alph (GateValue (Out Quiescence) _) m = do
        qui <- hasSymbolicQuiescence stateVal (Map.fromSet m alph)
        return $ LocationMove $ if qui then BM.ordReturn loc else forbidden
    ioTakeTransition q alph act m = return $ takeTransition q alph (fromSuspended <$> act) m

hasSymbolicQuiescence :: (BoundedMonad m, BooleanConfiguration m) => Valuation -> Map (IOSymInteract i o) (m (STStdest, loc)) -> IO Bool
hasSymbolicQuiescence stateVal m = do
    let syntacticallySpecifiedOutputs = filter (isOutputInteract . fst &&& not . isForbidden . snd) (Map.toList m)
        outputsAndCombinedGuards = second (combineGuards . BM.ordMap (substituteInGuard stateVal . tdestlocToGuard)) <$> syntacticallySpecifiedOutputs
    -- FIXME this should not solve sequentially, flattening the full list to a single guard is potentially more efficient (e.g. when the last guard in the list is trivially true)
    Maybe.isNothing <$> runSMT (solveAnySequential outputsAndCombinedGuards)
    where
    tdestlocToGuard (STSLoc (guard, _), _) = guard

-----------------------
-- STS input-failure --
-----------------------
instance (Ord i, Ord o) => IOTransitionSemantics loc (IntrpState loc) (IOSymInteract i o) STStdest (IFGateValue i o) where
    ioTakeTransition (IntrpState _ stateVal) alph (GateValue (In (InputAttempt(i, False))) gateVals) m =
        case asTransition alph (coerceIO (GateValue (In (InputAttempt (i, True))) gateVals) alph) of
            Nothing -> error "TransitionSemantics IFGateValue: error"
            Just interact'@(SymInteract _ gateVars) ->
                let gateVal = buildGateValuation gateVars gateVals
                    mtdestloc = m interact'
                    guard = combineGuards $ tdestlocToGuard BM.<#> mtdestloc
                    guardVal = evaluateGuard $ substituteInGuard gateVal $ substituteInGuard stateVal guard
                in return $ LocationMove $ if isSpecified mtdestloc && guardVal
                    then forbidden
                    else underspecified
        where
        tdestlocToGuard (STSLoc (guard, _), _) = guard
        coerceIO :: IFGateValue i o -> Set.Set (IOSymInteract i o) -> IFGateValue i o
        coerceIO = const
    ioTakeTransition q alph gateValue m = return $ takeTransition q alph (fromInputAttempt <$> gateValue) m

------------------------------------
-- STS input-failure + quiescence --
------------------------------------
-- Ideally this would automatically follow from the above two interpretations stacked to avoid the boilerplate below, but that is a hassle
instance (Ord i, Ord o) => IOTransitionSemantics loc (IntrpState loc) (IOSymInteract i o) STStdest (SuspendedIFGateValue i o) where
    ioTakeTransition (IntrpState loc stateVal) alph (GateValue (Out Quiescence) _) m = do
        qui <- hasSymbolicQuiescence stateVal (Map.fromSet m alph)
        return $ LocationMove $ if qui then BM.ordReturn loc else forbidden
    ioTakeTransition (IntrpState _ stateVal) alph (GateValue (In (InputAttempt(i, False))) gateVals) m =
        case asTransition alph (coerceIO (GateValue (In (InputAttempt (i, True))) gateVals) alph) of
            Nothing -> error "TransitionSemantics IFGateValue: error"
            Just interact'@(SymInteract _ gateVars) ->
                let gateVal = buildGateValuation gateVars gateVals
                    mtdestloc = m interact'
                    guard = combineGuards $ tdestlocToGuard BM.<#> mtdestloc
                    guardVal = evaluateGuard $ substituteInGuard gateVal $ substituteInGuard stateVal guard
                in return $ LocationMove $ if isSpecified mtdestloc && guardVal
                    then forbidden
                    else underspecified
        where
        tdestlocToGuard (STSLoc (guard, _), _) = guard
        coerceIO :: IFGateValue i o -> Set.Set (IOSymInteract i o) -> IFGateValue i o
        coerceIO = const
    ioTakeTransition q alph gateValue m = return $ takeTransition q alph (fromSuspendedInputAttempt <$> gateValue) m

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
                qs = Set.fromList $ concatMap (fmap snd . Foldable.toList) $ Map.elems ts
                new = qs `Set.difference` acc
                acc' = acc `Set.union` new
                boundary' = boundaryRem `Set.union` new
            in reachableFrom' acc' boundary'

------------------------------
-- sequential composition --
------------------------------

-- | A location is sink if none of its outgoing transitions are specified, i.e. every transition is either forbidden or underspecified.
isSinkLocation :: BoundedConfiguration m => AutSyntax m loc t tdest -> loc -> Bool
isSinkLocation aut loc = not (any BM.isIndefinite (Map.elems (transRel aut loc)))

{- |
    All locations of an automaton, i.e. its initial location together with everything reachable from them.
-}
allLocations :: (Ord loc, Foldable m) => AutSyntax m loc t tdest -> Set loc
allLocations aut = reachable aut `Set.union` Set.fromList (Foldable.toList (initConf aut))

{- |
    Returns 'allLocations' of the first automaton or the corresponding error if some precondition is violated.
-}
validMergeLocs :: (Ord loc1, Foldable m) => String -> AutSyntax m loc1 t tdest -> [loc1] -> Set loc1
validMergeLocs fnName sts1 mergeLocs
    | null mergeLocs = errorWithoutStackTrace $ fnName ++ ": no locations given to merge at"
    | not (all (`Set.member` locs1) mergeLocs) = errorWithoutStackTrace $ fnName ++ ": one or more locations are not reachable in the first automaton"
    | otherwise = locs1
    where
    locs1 = allLocations sts1

{- |
    Sequentially compose two automata: sequentiallyAt sts1 locs sts2 merges sts2 into sts1 at the given locations of sts1. Where a merge 
    location already specifies a transition for an action also in sts2's alphabet, and the copied transition from sts2 is also specified, 
    the two are conjuncted with (/\). If only one of the two is specified (the other being forbidden or underspecified), that one is used as-is.
-}
sequentiallyAt :: (Ord loc1, Ord loc2, Show loc1, Show loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, Either loc1 loc2)), Completable t, MeetSemiLattice (m (tdest, Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> [loc1] -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
sequentiallyAt sts1 mergeLocs sts2 = locs1 `seq` automaton newInitConf newAlphabet switches
    where
    locs1 = validMergeLocs "sequentiallyAt" sts1 mergeLocs
    locs2 = allLocations sts2
    mergeLocSet = Set.fromList mergeLocs

    newAlphabet = alphabet sts1 `Set.union` alphabet sts2
    newInitConf = Left BM.<#> initConf sts1

    -- transitions out of the initial location(s) of sts2, to be replicated onto every merge location of sts1
    initTransOf2 = Map.fromList
        [ (t, BM.ordMap (second Right) (BM.ordBind (initConf sts2) (\l2 -> transRel sts2 l2 Map.! t)))
        | t <- Set.toList (alphabet sts2) ]

    -- conjunct sts1's own transition with the copied one, but only where both are specified
    pick own other
        | BM.isIndefinite own && BM.isIndefinite other = own /\ other
        | BM.isIndefinite own                          = own
        | otherwise                                     = other

    transOf1 l1
        | l1 `Set.member` mergeLocSet = Map.unionWith pick ownTrans initTransOf2
        | otherwise                   = ownTrans
        where
        ownTrans = Map.map (BM.ordMap (second Left)) (transRel sts1 l1)

    switches1 = Map.fromList [ (Left l1, transOf1 l1) | l1 <- Set.toList locs1 ]
    switches2 = Map.fromList
        [ (Right l2, Map.map (BM.ordMap (second Right)) (transRel sts2 l2))
        | l2 <- Set.toList locs2 ]

    allSwitches = switches1 `Map.union` switches2
    switches loc = Map.findWithDefault Map.empty loc allSwitches

infixl 1 |>
-- | Sequentially compose two automata at all sink locations of the first. Throws an error if the first automaton does not have any sink locations.
(|>) :: (Ord loc1, Ord loc2, Show loc1, Show loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, Either loc1 loc2)), Completable t, MeetSemiLattice (m (tdest, Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
sts1 |> sts2 = case Set.toList $ Set.filter (isSinkLocation sts1) (allLocations sts1) of
    []      -> errorWithoutStackTrace "(|>): the first automaton has no sink location to sequentially compose at"
    locList -> sequentiallyAt sts1 locList sts2

{- |
    Sequentially compose two automata that share the same location semantics, e.g. an automaton composed with itself: selfSequentiallyAt sts1 locs sts2
    merges sts2 into sts1 at the given locations of sts1. Where a merge location already specifies a transition for an action also
    in sts2's alphabet, and the copied transition from sts2 is also specified, the two are conjuncted with (/\). If only one of the 
    two is specified (the other being forbidden or underspecified), that one is used as-is.
-}
selfSequentiallyAt :: (Ord loc, Show loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, loc)), Completable t, MeetSemiLattice (m (tdest, loc))) =>
    AutSyntax m loc t tdest -> [loc] -> AutSyntax m loc t tdest -> AutSyntax m loc t tdest
selfSequentiallyAt sts1 mergeLocs sts2 = locs1 `seq` automaton newInitConf newAlphabet switches
    where
    locs1 = validMergeLocs "selfSequentiallyAt" sts1 mergeLocs
    locs2 = allLocations sts2
    mergeLocSet = Set.fromList mergeLocs

    newAlphabet = alphabet sts1 `Set.union` alphabet sts2
    newInitConf = initConf sts1

    -- transitions out of the initial location(s) of sts2, to be replicated onto every merge location of sts1
    initTransOf2 = Map.fromList
        [ (t, BM.ordBind (initConf sts2) (\l2 -> transRel sts2 l2 Map.! t))
        | t <- Set.toList (alphabet sts2) ]

    -- conjunct sts1's own transition with the copied one, but only where both are specified
    pick own other
        | BM.isIndefinite own && BM.isIndefinite other = own /\ other
        | BM.isIndefinite own                          = own
        | otherwise                                     = other

    transOf1 l1
        | l1 `Set.member` mergeLocSet = Map.unionWith pick (transRel sts1 l1) initTransOf2
        | otherwise                   = transRel sts1 l1

    switches1 = Map.fromList [ (l1, transOf1 l1) | l1 <- Set.toList locs1 ]
    switches2 = Map.fromList
        [ (l2, transRel sts2 l2)
        | l2 <- Set.toList locs2 ]

    allSwitches = switches1 `Map.union` switches2
    switches loc = Map.findWithDefault Map.empty loc allSwitches

infixl 1 |>>
-- | `selfSequentiallyAt` applied to all sink locations of the first automaton. Throws an error if the first automaton does not have any sink locations.
(|>>) :: (Ord loc, Show loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, loc)), Completable t, MeetSemiLattice (m (tdest, loc))) =>
    AutSyntax m loc t tdest -> AutSyntax m loc t tdest -> AutSyntax m loc t tdest
sts1 |>> sts2 = case Set.toList $ Set.filter (isSinkLocation sts1) (allLocations sts1) of
    []      -> errorWithoutStackTrace "(|>>): the first automaton has no sink location to sequentially compose at"
    locList -> selfSequentiallyAt sts1 locList sts2

{- |
    Redirect a transition's destination to the given composed initial state configuration wherever it points to one of the original
    automata own initial locations.
-}
redirectToComposed :: (BoundedMonad m, Ord tdest, Ord loc') => (loc' -> Bool) -> m loc' -> m (tdest, loc') -> m (tdest, loc')
redirectToComposed isOldInit composedInit dest = BM.ordBind dest $ \(td, l) -> if isOldInit l
    then BM.ordMap (td,) composedInit
    else BM.ordReturn (td, l)

-- | Rename locations of a given STS with the given renaming function, returning the renamed initial configuration and
-- the renamed transition relation.
renameLocs :: (Ord loc, Ord loc', Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, loc'))) =>
    (loc -> loc') -> AutSyntax m loc t tdest ->
    (m loc', Map.Map loc' (Map.Map t (m (tdest, loc'))))
renameLocs renamingFun sts = (renamingFun BM.<#> initConf sts, wrappedSwitches)
  where
    wrappedSwitches = Map.fromList
        [ (renamingFun l, Map.map (BM.ordMap (second renamingFun)) (transRel sts l))
        | l <- Set.toList (allLocations sts)
        ]

-- | Combine automata with the same loc type
composeGeneric :: (Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, loc)), Completable t) =>
    (m loc -> m loc -> m loc) -> Set.Set t ->
    [(m loc, Map.Map loc (Map.Map t (m (tdest, loc))))] ->
    AutSyntax m loc t tdest
composeGeneric combine newAlphabet renamedLocs = automaton newInitConf newAlphabet switches
  where
    allInitLocs = Set.unions [ Set.fromList (Foldable.toList ic) | (ic, _) <- renamedLocs ]
    isOldInit l = l `Set.member` allInitLocs

    newInitConf = foldr1 combine [ ic | (ic, _) <- renamedLocs ]

    allSwitches = Map.map (Map.map (redirectToComposed isOldInit newInitConf))
                $ Map.unions [ sw | (_, sw) <- renamedLocs ]

    switches loc = Map.findWithDefault Map.empty loc allSwitches

{- |
    Compose the initial state of two automata with the given operator, and redirect every transition in either automaton that
    leads back to one of its own original initial locations to the composed initial state instead.
    Every other transition is kept as-is (just expressed as 'Either loc1 loc2' location type).
-}
composeInitial :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, Either loc1 loc2)), Completable t) =>
    (m (Either loc1 loc2) -> m (Either loc1 loc2) -> m (Either loc1 loc2)) ->
    AutSyntax m loc1 t tdest -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
composeInitial combine sts1 sts2 =
    composeGeneric combine (alphabet sts1 `Set.union` alphabet sts2)
        [ renameLocs Left sts1, renameLocs Right sts2 ]

infixl 1 //\\
{- |
    Given two automata, return their conjunction. This conjunction is done by merging the initial states of both with /\, and replacing all instances
    of the initial locations in the transitions of sts1 and sts2 with the composed initial state. The resulting automaton has a joint alphabet and locations of
    type 'Either loc1 loc2'.
-}
(//\\) :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, Either loc1 loc2)), Completable t, MeetSemiLattice (m (Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
(//\\) = composeInitial (/\)

infixl 1 \\//
{- |
    Given two automata, return their disjunction. This disjunction is done by merging the initial states of both with \/, and replacing all instances
    of the initial locations in the transitions of sts1 and sts2 with the composed initial state. The resulting automaton has a joint alphabet and locations of
    type 'Either loc1 loc2'.
-}
(\\//) :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, Either loc1 loc2)), Completable t, JoinSemiLattice (m (Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
(\\//) = composeInitial (\/)

{- |
    Compose the initial state of any number of labeled automata (all sharing the same location type) with the given operator, and
    redirect every transition in each automaton that leads back to one of its own initial locations to the composed initial state instead. 
    Every other transition is kept as-is, just tagged as a tuple (k, loc) where k is the automaton's label.
    Throws an error if the list is empty, or if any label is used more than once.
-}
composeInitialAll :: (Ord k, Show k, Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, (k, loc))), Completable t) =>
    (m (k, loc) -> m (k, loc) -> m (k, loc)) -> [(k, AutSyntax m loc t tdest)] -> AutSyntax m (k, loc) t tdest
composeInitialAll _ [] = errorWithoutStackTrace "composeInitialAll: no automata to combine"
composeInitialAll combine labeledSTSList
    | not (null duplicateLabels) =
        errorWithoutStackTrace $ "composeInitialAll: labels used more than once: " ++ show duplicateLabels
    | otherwise = composeGeneric combine newAlphabet [ renameLocs (k,) sts | (k, sts) <- labeledSTSList ]
  where
    duplicateLabels = Map.keys $ Map.filter (> 1) $ Map.fromListWith (+) [ (k, 1 :: Int) | (k, _) <- labeledSTSList ]
    newAlphabet = Set.unions [ alphabet sts | (_, sts) <- labeledSTSList ]

{- |
    The conjunction of any number of labeled automata. Locations are identified with a tuple of sts identifier and location of such automaton.
    All STSs must share the same location type. Throws an error if the list is empty, or if any label is used more than once.
-}
conjunctionAll :: (Ord k, Show k, Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, (k, loc))), Completable t, MeetSemiLattice (m (k, loc))) =>
    [(k, AutSyntax m loc t tdest)] -> AutSyntax m (k, loc) t tdest
conjunctionAll = composeInitialAll (/\)

{- |
    The disjunction of any number of labeled automata. Locations are identified with a tuple of sts identifier and location of such automaton.
    All STSs must share the same location type. Throws an error if the list is empty, or if any label is used more than once.
-}
disjunctionAll :: (Ord k, Show k, Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Ord (m (tdest, (k, loc))), Completable t, JoinSemiLattice (m (k, loc))) =>
    [(k, AutSyntax m loc t tdest)] -> AutSyntax m (k, loc) t tdest
disjunctionAll = composeInitialAll (\/)

{- |
    A location of an STS is either 'Stable' (a location's own behaviour) or 'Pending' 
    a specific output.
-}
data CheckLoc loc g = Stable loc | Pending loc g loc deriving (Eq, Ord)

instance (Show loc, Show g) => Show (CheckLoc loc g) where
    show (Stable loc)          = show loc
    show (Pending src g target) = "pending " ++ show g ++ " -> " ++ show target

{- |
    Complete an STS by prepending a "check" input before every output switch: an original switch l0 --o1!--> l1
    becomes Stable l0 --prefix_o1?--> Pending o1 l1 --o1!--> Stable l2, where prefix is configurable. Locations are 
    identified as 'Stable', the original STS location, and 'Pending', intermediate locations reached only via a check gate.

    Where two or more original switches share both the same output gate and the target location, their pending state
    configurations are merged with the given operator:'\/' if any guard may be satisfied, or '/\' if they must 
    all hold at once.
-}
prependOutputChecks :: (Ord loc, Ord i, Ord o, BoundedMonad m, Foldable m) =>
    (m (STStdest, CheckLoc loc (IOSymInteract i o)) -> m (STStdest, CheckLoc loc (IOSymInteract i o)) -> m (STStdest, CheckLoc loc (IOSymInteract i o))) ->
    (o -> i) -> AutSyntax m loc (IOSymInteract i o) STStdest -> AutSyntax m (CheckLoc loc (IOSymInteract i o)) (IOSymInteract i o) STStdest
prependOutputChecks combine checkNaming sts = automaton newInitConf newAlphabet switches
    where
    newInitConf = Stable BM.<#> initConf sts

    outputGates = [ t | t <- Set.toList (alphabet sts), isOutputInteract t ]
    newAlphabet = alphabet sts `Set.union` Set.fromList (checkGateFor <$> outputGates)

    checkGateFor (SymInteract (Out o) _) = SymInteract (In (checkNaming o)) []
    checkGateFor _                       = error "prependOutputChecks: checkGateFor called on a non-output gate"

    identityTdest = stsTLoc sTrue noAssignment

    -- Switches starting from stable locations
    switches (Stable loc) = Map.fromList $
        -- keep input switches as-is
        [ (t, BM.ordMap (second Stable) mval) | (t, mval) <- Map.toList (transRel sts loc), not (isOutputInteract t) ]
        ++
        -- output switches are replaced by a check gate leading to a pending state
        [ (checkGateFor t, BM.ordMap (\(_, target) -> (identityTdest, Pending loc t target)) mval)
        | (t, mval) <- Map.toList (transRel sts loc), isOutputInteract t ]

    -- Additional switches starting from `pending` locations
    switches (Pending src t target) = Map.singleton t outcomes
        where
        mval = Map.findWithDefault
                 (error "prependOutputChecks: pending state refers to a nonexistent transition")
                 t (transRel sts src)

        matching = [ (tdest, Stable target)
                   | (tdest, dest) <- Foldable.toList mval
                   , dest == target
                   ]

        -- combine posible target states with the given operator (/\ or \/)
        outcomes = case matching of
            []     -> error "prependOutputChecks: pending state has no matching outcome"
            (x:xs) -> List.foldl' combine (BM.ordReturn x) (BM.ordReturn <$> xs)

prettyPrint :: (Show (m (tdest, loc)), Show (m loc), Show loc, Show t, Ord loc, Foldable m) => AutSyntax m loc t tdest -> String
prettyPrint aut = prettyPrintFrom aut (initConf aut)

prettyPrintFrom :: (Show (m (tdest, loc)), Show (m loc), Show loc, Show t, Ord loc, Foldable m, Foldable f) => AutSyntax m loc t tdest -> f loc -> String
prettyPrintFrom aut fromLocs = "initial location configuration: " ++ printInitial ++ "\nlocations: " ++ printLocations ++ "\ntransitions:\n" ++ printTransitions
    where
    locations = Set.toList $ reachableFrom aut fromLocs `Set.union` Set.fromList (Foldable.toList (initConf aut))
    printInitial = show $ initConf aut
    printLocations = List.intercalate ", " (show <$> locations)
    printTransitions = List.intercalate "\n" (printTransitionsFrom <$> locations)
    printTransitionsFrom q = List.intercalate "\n" (printTransition q <$> Map.toList (transRel aut q))
    printTransition q (t, mt) = show q ++ "  ――" ++ show t ++ "⟶  " ++ show mt

prettyPrintIntrp :: (Show (m (tdest, loc)), Show (m loc), Show loc, Show (m q), Show t, Ord loc, Foldable m) => AutIntrpr m loc q t tdest act -> String
prettyPrintIntrp intrp = "current state configuration: " ++ printStateConf ++ "\n" ++ printAut
    where
    printStateConf = show $ stateConf intrp
    printAut = prettyPrint $ syntacticAutomaton intrp


