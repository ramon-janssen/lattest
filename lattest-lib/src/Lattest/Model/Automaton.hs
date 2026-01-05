{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
--{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

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
IOStepSemantics,
after,
afters,
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
prettyPrint,
prettyPrintFrom,
prettyPrintIntrp
)
where

import Prelude hiding (lookup)

import Lattest.Model.BoundedMonad(BoundedApplicative, BoundedMonad, BoundedConfiguration, BooleanConfiguration, isForbidden, forbidden, underspecified, isSpecified, asDualValExpr)
import Lattest.Model.Alphabet(IOAct(In,Out),isOutput,IOSuspAct,Suspended(Quiescence),IFAct(..),InputAttempt(..),fromSuspended,asSuspended,fromInputAttempt,asInputAttempt,SuspendedIF,asSuspendedInputAttempt,fromSuspendedInputAttempt,
    SymInteract(..),IOSymInteract,GateValue(..), IOGateValue, IOSuspGateValue, IFGateValue, SuspendedIFGateValue, SymGuard, addTypedVal, isOutputGate, isOutputInteract, interactionGate)
--import Lattest.Model.Symbolic.SolveSTS(solveAnySequential)
import Lattest.SMT.SMT(SMTRef, runSMT, SMT)
import Lattest.SMT.SMTData(SmtEnv)
import Lattest.Util.Utils((&&&), takeArbitrary, distributeMonadOverFoldable)
import Control.Exception(throw,Exception)
import qualified Control.Monad as Monad(join)
import Control.Arrow(second)
import Data.Either.Utils (fromRight)
import qualified Data.Foldable as Foldable
import Data.Functor.Identity(Identity(Identity), runIdentity)
import Data.IORef(IORef)
import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tuple.Extra(first)
import GHC.OldList(find)
import GHC.Stack(CallStack,callStack)
import Lattest.Model.Symbolic.ValExpr.ValExpr(Valuation, VarModel, Variable(..),Type(..),ValExpr(..), ValExprInt, ValExprBool, ValExprString, eval, constType, varType, evalConst, evalConst', assignedExpr, Eval, Subst, subst)
import Lattest.Model.Symbolic.ValExpr.Constant(Constant(..), toBool, toInteger, toText)

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
    takeTransition :: (BoundedApplicative m) => q -> Set t -> act -> (t -> m (tdest, loc)) -> Move m t tdest loc
    takeTransition q alph act trans' = case asTransition alph act of
        Nothing -> LocationMove $ pure (asLoc q)
        Just t -> TransitionMove (t, trans' t)

class (Ord t, Completable act, TransitionMapping t act, StateSemantics loc q) => IOTransitionSemantics loc q t tdest act z | t act -> tdest where
    {- |
        Find the syntactic transition that applies for the given semantic action value, or alternatively a move within the location.
        The function may be partial, following the given alphabet.
    -}
    ioTakeTransition :: (BoundedApplicative m, BooleanConfiguration m) => IORef z -> q -> Set t -> act -> (t -> m (tdest, loc)) -> IO (Move m t tdest loc)
    ioTakeTransition _ q alph act trans' = return $ case asTransition alph act of
        Nothing -> LocationMove $ pure (asLoc q)
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
class (StateSemantics loc q, TransitionSemantics loc q t tdest act, BoundedMonad m) => StepSemantics m loc q t tdest act where
    {- |
        Given the current state, an action and the transition matching that action, and a new location and local transition, produce the new state
        The case of no transition (i.e. no transition applies in the TransitionSemantics) can be used to move within a location.
    -}
    move :: q -> act -> Maybe (t, tdest) -> loc -> m q

class (StateSemantics loc q, IOTransitionSemantics loc q t tdest act z, BoundedMonad m) => IOStepSemantics m loc q t tdest act z where
    ioMove :: IORef z -> q -> act -> Maybe (t, tdest) -> loc -> IO (m q)

{- |
    Take a step for the given action, according to the step semantics to move from one state configuration to another. May throw an AutomatonException.
-}
after :: StepSemantics m loc q t tdest act => AutIntrpr m loc q t tdest act -> act -> AutIntrpr m loc q t tdest act
after aut act = runIdentity $ afterInternal takeTransitionId moveId fmapId fmapId fmapId aut act
    where
    takeTransitionId :: (BoundedApplicative m, TransitionSemantics loc q t tdest act) => q -> Set t -> act -> (t -> m (tdest, loc)) -> Identity (Move m t tdest loc)
    takeTransitionId q alph act trans' = Identity $ takeTransition q alph act trans'
    moveId :: StepSemantics m loc q t tdest act => q -> act -> Maybe (t, tdest) -> loc -> Identity (m q)
    moveId q act mt loc = Identity $ move q act mt loc
    fmapId :: Functor f => (x -> Identity y) -> f x -> Identity (f y)
    fmapId f = Identity . fmap (runIdentity . f)

class IOAfter m loc q t tdest act ioState where
    ioAfter :: ioState -> AutIntrpr m loc q t tdest act -> act -> IO (AutIntrpr m loc q t tdest act)

instance StepSemantics m loc q t tdest act => IOAfter m loc q t tdest act () where
    ioAfter () aut act = return $ after aut act

instance (IOStepSemantics m loc q t tdest act z, BooleanConfiguration m, Foldable m, Ord tdest, Ord q, Ord loc) => IOAfter m loc q t tdest act (IORef z) where
    ioAfter execState = afterInternal (ioTakeTransition execState) (ioMove execState) distributeMonadOverFoldable distributeMonadOverFoldable distributeMonadOverFoldable

--takeTransition :: (BoundedApplicative m) => q -> Set t -> act -> (t -> m (tdest, loc)) -> Move m t tdest loc
--ioTakeTransition :: (BoundedApplicative m) => IORef z -> q -> Set t -> act -> (t -> m (tdest, loc)) -> IO (Move m t tdest loc)

-- distributeMonadOverFoldable :: (Functor m, Foldable m, Monad execM, Ord x) => (x -> execM y) -> m x -> execM (m y)
-- fmapInternal?? :: (Functor m, Monad execM) => (x -> execM y) -> m x -> execM (m y)
afterInternal :: (Monad m, Monad execM, Ord t, BoundedConfiguration m, StateSemantics loc q) =>
    (q -> Set t -> act -> (t -> m (tdest, loc)) -> execM (Move m t tdest loc)) ->
    (q -> act -> Maybe (t, tdest) -> loc -> execM (m q)) ->
    ((q -> execM (m q)) -> m q -> execM (m (m q))) ->
    ((loc -> execM (m q)) -> m loc -> execM (m (m q))) ->
    (((tdest, loc) -> execM (m q)) -> m (tdest, loc) -> execM (m (m q))) ->
    AutIntrpr m loc q t tdest act -> act -> execM (AutIntrpr m loc q t tdest act)
afterInternal internalTakeTransition internalMove fmapmq fmapmloc fmaptdestloc intrpr act' = do
    let aut = syntacticAutomaton intrpr
        toNewStateConfig = afterInternal' internalTakeTransition internalMove fmapmloc fmaptdestloc (alphabet aut) (transRel $ aut) act'
    stateConf' <- toNewStateConfig `fmapmq` stateConf intrpr
    return $ intrpr { stateConf = Monad.join stateConf' }

afterInternal' :: (Monad m, BoundedConfiguration m, Ord t, StateSemantics loc q, Monad execM) =>
    (q -> Set t -> act -> (t -> m (tdest, loc)) -> execM (Move m t tdest loc)) ->
    (q -> act -> Maybe (t, tdest) -> loc -> execM (m q)) ->
    ((loc -> execM (m q)) -> m loc -> execM (m (m q))) ->
    (((tdest, loc) -> execM (m q)) -> m (tdest, loc) -> execM (m (m q))) ->
    Set t -> (loc -> Map t (m (tdest, loc))) -> act -> q -> execM (m q)
afterInternal' internalTakeTransition internalMove fmapmloc fmaptdestloc alph transMap act q = do
    t <- internalTakeTransition q alph act (lookupAction $ transMap $ asLoc q)
    Monad.join <$> case t of
        LocationMove mloc -> internalMove q act (nothingTTdest transMap) `fmapmloc` mloc
            where
            -- ugly solution to get a Nothing of the type (Maybe (t, tdest)) without ScopedTypeVariables
            nothingTTdest :: (x1 -> Map t (x2 (tdest, x3))) -> Maybe (t, tdest)
            nothingTTdest _ = Nothing
        TransitionMove (t, mtdestloc) -> moveAlongTransition q act t `fmaptdestloc` mtdestloc
            where
            moveAlongTransition q act t (tdest, loc) = internalMove q act (Just (t, tdest)) loc
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
    The class of automata with a finite list of concrete actions matching to outgoing transitions for every state.
    This property is useful for e.g. test selection.
-}
class TransitionMapping t act => FiniteMenu t act where
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

instance (Ord act) => TransitionMapping act act where
    asTransition _ = Just

instance (Ord act) => TransitionSemantics q q act () act

instance (Ord act) => FiniteMenu act act where
    asActions t = [t] 
    locationActions _ = []

instance StateSemantics q q where
    asLoc = id

instance (TransitionSemantics q q t () act, BoundedMonad m) => StepSemantics m q q t () act where
    move _ _ _ q = pure q

----------------
-- quiescence --
----------------
instance (Completable (IOAct i o)) where
    implicitDestination (Out _) = forbidden
    implicitDestination _ = underspecified

instance (Ord i, Ord o) => TransitionMapping (IOAct i o) (IOSuspAct i o) where
    asTransition _ (Out Quiescence) = Nothing
    asTransition _ other = Just $ fromSuspended other

instance (Ord i, Ord o) => TransitionSemantics q q (IOAct i o) () (IOSuspAct i o) where
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    takeTransition loc alph (Out Quiescence) m = LocationMove $ if hasQuiescence (Map.fromSet m alph) then pure loc else forbidden
    takeTransition _ _ act m = TransitionMove (fromSuspended act, m $ fromSuspended act)

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (IOSuspAct i o) where
    asActions t = [asSuspended t]
    locationActions _ = [Out Quiescence]

hasQuiescence :: BoundedApplicative m => Map (IOAct i o) (m (tdest, loc)) -> Bool
hasQuiescence m = not $ any (isOutput . fst &&& not . isForbidden . snd) (Map.toList m)

-------------------
-- input-failure --
-------------------

instance TransitionMapping (IOAct i o) (IFAct i o) where
    asTransition _ (In (InputAttempt(i, False))) = Nothing
    asTransition _ other = Just $ fromInputAttempt other

instance (Ord i, Ord o) => TransitionSemantics q q (IOAct i o) () (IFAct i o) where
    takeTransition loc _ (In (InputAttempt(i, False))) m = 
        let mtdestloc = m $ In i
        in LocationMove $ if isSpecified mtdestloc
            then forbidden -- if ?i is specified, then the failure of ?i is forbidden
            else underspecified -- input failure is not repetitive: it is allowed, and nothing can be done afterwards, i.e., underspecified
    takeTransition _ _ act m = TransitionMove (fromInputAttempt act, m $ fromInputAttempt act)

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (IFAct i o) where
    asActions t = [asInputAttempt t]
    locationActions _ = []

--------------------------------
-- input-failure + quiescence --
--------------------------------
-- Ideally this would automatically follow from the above two interpretations stacked to avoid the boilerplate below, but that is a hassle

instance TransitionMapping (IOAct i o) (SuspendedIF i o) where
    asTransition _ (In (InputAttempt(i, False))) = Nothing
    asTransition _ (Out Quiescence) = Nothing
    asTransition _ other = Just $ fromSuspendedInputAttempt other

instance (Ord i, Ord o) => TransitionSemantics q q (IOAct i o) () (SuspendedIF i o) where
    takeTransition loc _ (In (InputAttempt(i, False))) m = 
        let mtdestloc = m $ In i
        in LocationMove $ if isSpecified mtdestloc
            then forbidden -- if ?i is specified, then the failure of ?i is forbidden
            else underspecified -- input failure is not repetitive: it is allowed, and nothing can be done afterwards, i.e., underspecified
    takeTransition loc alph (Out Quiescence) m = LocationMove $ if hasQuiescence (Map.fromSet m alph) then pure loc else forbidden
    takeTransition _ _ act m = TransitionMove (fromSuspendedInputAttempt act, m $ fromSuspendedInputAttempt act)

instance (Ord i, Ord o) => FiniteMenu (IOAct i o) (SuspendedIF i o) where
    asActions t = [asSuspendedInputAttempt t]
    locationActions _ = [Out Quiescence]

--------------------------------
-- STS interpretation --
--------------------------------

data IntrpState a = IntrpState a Valuation deriving (Eq, Ord, Show)

newtype STStdest = STSLoc (SymGuard,VarModel) deriving (Eq, Ord)

stsTLoc :: SymGuard -> VarModel -> STStdest
stsTLoc g a = STSLoc (g,a)

instance Show STStdest where
    show (STSLoc (g,a)) =  "[[" ++ show g ++ "]] " ++ show a

instance (Completable g) => Completable (GateValue g) where
    implicitDestination (GateValue g _) = implicitDestination g

instance StateSemantics a (IntrpState a) where
    asLoc (IntrpState l _) = l

instance (Ord g, TransitionMapping g g') => TransitionMapping (SymInteract g) (GateValue g') where
    asTransition interactions (GateValue g values) = do
        let ts = Set.map interactionGate interactions
        ig' <- asTransition ts g
        case List.find (\(SymInteract ig _) -> ig == ig') (Set.toList interactions) of
            Nothing -> errorWithoutStackTrace $ "gate not in STS alphabet"
            Just i@(SymInteract g vars) ->
                if List.length values /= List.length vars
                    then errorWithoutStackTrace $ "nr of values unequal to nr of parameters"
                    else if List.all (\(var,val) -> varType var == constType val) (zip vars values)
                            then Just i
                            else errorWithoutStackTrace "type of variable and value do not match"

instance (Completable g, Ord g, TransitionMapping g g') => TransitionSemantics loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') where

instance (Ord g, Ord loc, BoundedMonad m, TransitionMapping g g') => StepSemantics m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') where
    move (IntrpState l1 stateValuation) gv@(GateValue g gateVals) (Just (SymInteract g2 gateVars, STSLoc (guard,assign))) l2 =
        let gateValuation = buildGateValuation gateVars gateVals
            -- valuation = Map.foldrWithKey (\x xval m -> addTypedVal x xval m) gateValuation stateValuation
            valuation = stateValuation `Map.union` gateValuation
        in if not $ evalBool valuation guard
            then implicitDestination gv
            else let stateValuation2 = Map.mapWithKey (\var val -> assignNewValue var val valuation assign) stateValuation
                 in return $ IntrpState l2 stateValuation2
        where
        assignNewValue :: Variable -> Constant -> Valuation -> VarModel -> Constant
        -- the following case distinctino could be removed if constants were also typed
        assignNewValue var@(Variable _ IntType) oldVal valuation assign = maybe oldVal (evalVal valuation) (assignedExpr var assign :: Maybe ValExprInt)
        assignNewValue var@(Variable _ BoolType) oldVal valuation assign = maybe oldVal (evalVal valuation) (assignedExpr var assign :: Maybe ValExprInt)
        assignNewValue var@(Variable _ StringType) oldVal valuation assign = maybe oldVal (evalVal valuation) (assignedExpr var assign :: Maybe ValExprInt)
buildGateValuation :: [Variable] -> [Constant] -> Valuation
buildGateValuation gateVars gateVals= List.foldr (\(gateVar,gateVal) m -> addTypedVal gateVar gateVal m) (Map.empty) (zip gateVars gateVals)
evalVal :: (Subst t, Eval t) => Valuation -> ValExpr t -> Constant
evalVal valuation = fromRight . evalConst valuation
evalBool :: Valuation -> ValExprBool-> Bool
evalBool valuation = toBool . evalVal valuation

--------------------
-- STS quiescence --
--------------------
instance (Ord i, Ord o) => IOTransitionSemantics loc (IntrpState loc) (IOSymInteract i o) STStdest (IOSuspGateValue i o) SmtEnv where
    -- TODO this takeTransition only detects plain 'forbidden', not if hidden in e.g. symbolic locations
    -- TODO do something with the values (now "_"), even if just throwin an exception if non-empty
    ioTakeTransition smtRef (IntrpState loc stateVal) alph (GateValue (Out Quiescence) _) m = do
        qui <- hasSymbolicQuiescence smtRef stateVal (Map.fromSet m alph)
        return $ LocationMove $ if qui then pure loc else forbidden
    ioTakeTransition _ q alph act m = return $ takeTransition q alph (fromSuspended <$> act) m

instance (Ord i, Ord o, Ord loc, BoundedMonad m) => IOStepSemantics m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOSuspGateValue i o) SmtEnv where
    ioMove = error "?!?"

hasSymbolicQuiescence :: (BoundedApplicative m, BooleanConfiguration m) => SMTRef -> Valuation -> Map (IOSymInteract i o) (m (STStdest, loc)) -> IO Bool
hasSymbolicQuiescence smtRef stateVal m = do
    let syntacticallySpecifiedOutputs = filter (isOutputInteract . fst &&& not . isForbidden . snd) (Map.toList m)
        outputsAndCombinedGuards = second (combineGuards . fmap (substituteInGuard stateVal . tdestlocToGuard)) <$> syntacticallySpecifiedOutputs
    -- FIXME this should not solve sequentially, flattening the full list to a single guard is potentially more efficient (e.g. when the last guard in the list is trivially true)
    Maybe.isNothing <$> (runSMT smtRef $ solveAnySequential outputsAndCombinedGuards)
    where
    tdestlocToGuard (STSLoc (guard, _), _) = guard
    
-- TODO refactor module structure, this should beong somewhere in a SMT/symbolic module
combineGuards :: (Functor m, BooleanConfiguration m) => m SymGuard -> SymGuard
combineGuards = asDualValExpr

-- TODO refactor module structure, this should beong somewhere in a SMT/symbolic module
substituteInGuard :: Valuation -> SymGuard -> SymGuard
substituteInGuard valuation guard = evalConst' valuation guard

-- TODO refactor module structure, this should beong somewhere in a SMT/symbolic module
solveAnySequential :: [(SymInteract g,SymGuard)] -> SMT (Maybe (GateValue g))
solveAnySequential = error "still to refactor: call solveAnySequential from SMT module without cyclic dependencies"

-- TODO refactor module structure, this should beong somewhere in a SMT/symbolic module
evaluateGuard :: SymGuard -> Bool
evaluateGuard guard = case eval guard of
    Left e -> error e -- TODO proper exception
    Right (Cbool b) -> b

-----------------------
-- STS input-failure --
-----------------------
instance (Ord i, Ord o) => IOTransitionSemantics loc (IntrpState loc) (IOSymInteract i o) STStdest (IFGateValue i o) SmtEnv where
    ioTakeTransition _ (IntrpState loc stateVal) alph (GateValue (In (InputAttempt(i, False))) gateVals) m =
        case asTransition alph (coerceIO (GateValue (In (InputAttempt(i, True))) gateVals) alph) of
            Nothing -> error "TransitionSemantics IFGateValue: error"
            Just interact@(SymInteract _ gateVars) ->
                let gateVal = buildGateValuation gateVars gateVals
                    mtdestloc = m interact
                    guard = combineGuards $ tdestlocToGuard <$> mtdestloc
                    guardVal = evaluateGuard $ substituteInGuard gateVal $ substituteInGuard stateVal guard
                in return $ LocationMove $ if isSpecified mtdestloc && guardVal
                    then forbidden
                    else underspecified
        where
        tdestlocToGuard (STSLoc (guard, _), _) = guard
        coerceIO :: IFGateValue i o -> Set.Set (IOSymInteract i o) -> IFGateValue i o
        coerceIO = const
    ioTakeTransition _ q alph gateValue m = return $ takeTransition q alph (fromInputAttempt <$> gateValue) m

instance (Ord i, Ord o, Ord loc, BoundedMonad m) => IOStepSemantics m loc (IntrpState loc) (IOSymInteract i o) STStdest (IFGateValue i o) SmtEnv where
    ioMove = error "?!?"

------------------------------------
-- STS input-failure + quiescence --
------------------------------------
-- Ideally this would automatically follow from the above two interpretations stacked to avoid the boilerplate below, but that is a hassle
instance (Ord i, Ord o) => IOTransitionSemantics loc (IntrpState loc) (IOSymInteract i o) STStdest (SuspendedIFGateValue i o) SmtEnv where
    ioTakeTransition smtRef (IntrpState loc stateVal) alph (GateValue (Out Quiescence) _) m = do
        qui <- hasSymbolicQuiescence smtRef stateVal (Map.fromSet m alph)
        return $ LocationMove $ if qui then pure loc else forbidden
    ioTakeTransition _ (IntrpState loc stateVal) alph (GateValue (In (InputAttempt(i, False))) gateVals) m =
        case asTransition alph (coerceIO (GateValue (In (InputAttempt(i, True))) gateVals) alph) of
            Nothing -> error "TransitionSemantics IFGateValue: error"
            Just interact@(SymInteract _ gateVars) ->
                let gateVal = buildGateValuation gateVars gateVals
                    mtdestloc = m interact
                    guard = combineGuards $ tdestlocToGuard <$> mtdestloc
                    guardVal = evaluateGuard $ substituteInGuard gateVal $ substituteInGuard stateVal guard
                in return $ LocationMove $ if isSpecified mtdestloc && guardVal
                    then forbidden
                    else underspecified
        where
        tdestlocToGuard (STSLoc (guard, _), _) = guard
        coerceIO :: IFGateValue i o -> Set.Set (IOSymInteract i o) -> IFGateValue i o
        coerceIO = const
    ioTakeTransition _ q alph gateValue m = return $ takeTransition q alph (fromSuspendedInputAttempt <$> gateValue) m

instance (Ord i, Ord o, Ord loc, BoundedMonad m) => IOStepSemantics m loc (IntrpState loc) (IOSymInteract i o) STStdest (SuspendedIFGateValue i o) SmtEnv where
    ioMove = error "?!?"

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


