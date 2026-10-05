{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE TypeOperators #-}

{- |
    This module contains some simple automata types, and auxiliary functions for constructing them in a convenient manner.
    Note that the types are no more than type aliases, so if the automata type with your favorite combination of type parameters
    is not listed, don't hesitate to construct an automaton type ('AutSyntax' or 'AutIntrpr') yourself instead of using the StandardAutomata.
    The base function `automaton` for constructing automata is re-exported here for convenience.
-}

module Lattest.Model.StandardAutomata (
-- * Automaton construction
automaton,
-- * Sequential composition
sequentiallyAt,
sequentiallyAtPruned,
(|>),
sequentiallyPruned,
selfSequentiallyAtPruned,
selfSequentiallyPruned,
Pruned(..),
selfSequentiallyAt,
(|>>),
prependOutputChecks,
CheckLoc(..),
-- * Conjunction and Disjunction Helper functions
(//\\),
(\\//),
conjunctionAll,
disjunctionAll,
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
STSIntrp,
IOSTSIntrp,
accessSequences,
interpretSTS,
SuspSTSIntrp,
interpretSTSQuiescent,
SuspInputAttemptSTSIntrp,
interpretSTSQuiescentInputAttemptConcrete,
allLocations
)
where

import Lattest.Model.Alphabet (IOAct(..), IOSuspAct, IFAct, SuspendedIF, SymInteract (..), IOSymInteract, SymGuard, GateValue, SuspendedIFGateValue, IOSuspGateValue, isOutputInteract)
import Lattest.Model.BoundedMonad (Det(..), BoundedMonad, FreeLattice, atom, top, bot, (\/), (/\), JoinSemiLattice, BoundedConfiguration, MeetSemiLattice)
import Lattest.Model.Automaton (AutSyntax (..), automaton, AutIntrpr (..), interpret, Completable, implicitDestination,IntrpState(..),STStdest (..), transRel,syntacticAutomaton, reachable, stsTLoc)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Util.Utils(takeArbitrary)

import Data.Foldable (toList)

import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import  Data.Maybe as Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bifunctor (Bifunctor(..))
import Lattest.Model.Symbolic.Expr
import qualified Data.List as List
import Lattest.Model.Symbolic.SolveSTS (SymIntrpState, indexExpr, indexVar)
import Lattest.SMT (Some)
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef')
import Lattest.Model.Symbolic.SolveSymPrim (solveGuard)
import qualified Debug.Trace

-- | construct an alphabet of input-output-actions (`IOAct`) from separate alphabets of inputs and outputs
ioAlphabet :: (Traversable t, Ord i, Ord o) => t i -> t o -> Set.Set (IOAct i o)
ioAlphabet ti to = Set.fromList $ (In <$> toList ti) ++ (Out <$> toList to)

{- |
    Create a deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as explicit states.
    Having multiple occurrences of a transition label is forbidden, i.e., leads to a Nothing result.
-}
detConcTransFromRel :: (Ord loc, Ord t) => [(loc, t, loc)] -> Maybe (loc -> Map t (Det ((), loc)))
detConcTransFromRel = transFromRelWith combineDet vacuousTrans (\l () _ -> Det $ vacuousLoc l)

{- |
    Create a deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as deterministic state
    configuration. Having multiple occurrences of a transition label is forbidden, i.e., leads to a Nothing result.
-}
detConcTransFromMRel :: (Ord loc, Ord t) => [(loc, t, Det loc)] -> Maybe (loc -> Map t (Det ((), loc)))
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
nonDetConcTransFromRel :: (Ord loc, Ord t, BM.OrdMonad m, JoinSemiLattice (m ((), loc))) => [(loc, t, loc)] -> (loc -> Map t (m ((), loc)))
nonDetConcTransFromRel = fromJust <$> transFromRelWith combineNonDet vacuousTrans (\l () _ -> BM.ordReturn $ vacuousLoc l)

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
nonDetConcTransFromMRel :: (Ord loc, Ord t, BM.OrdMonad m, JoinSemiLattice (m ((), loc))) => [(loc, t, m loc)] -> (loc -> Map t (m ((), loc)))
nonDetConcTransFromMRel = fromJust <$> transFromRelWith combineNonDet vacuousTrans (\ndl () _ -> BM.ordMap vacuousLoc ndl)

combineNonDet :: JoinSemiLattice a => a -> a -> Maybe a
combineNonDet x y = Just $ x \/ y

combineDet :: p1 -> p2 -> Maybe a
combineDet _ _ = Nothing

vacuousTrans :: (a, b, d) -> (a, b, (), d)
vacuousTrans (a,b,c) = (a,b,(),c)

vacuousLoc :: b -> ((), b)
vacuousLoc l = ((), l)

transFromRelWith :: (Ord loc, Ord t) =>
    (m (tdest, loc) -> m (tdest, loc) -> Maybe (m (tdest, loc))) -- the way of combining the monadic transitions resulting from two list elements, or Nothing if they cannot be combined
    -> (te -> (loc, t, tdest, loc')) -- the way of creating a 4-tuple with all the transition info from a list element
    -> (loc' -> tdest -> t -> m (tdest, loc)) -- the way of creating a monadic transition result from the transition info of a list element
    -> [te] -- the transition relation in a list representation
    -> Maybe (loc -> Map t (m (tdest, loc))) -- a transition function, or Nothing if combining two monadic transitions failed
transFromRelWith c' fe' f' trans = do
    tMapMap <- foldr (addToMap c' fe' f') (Just Map.empty) trans -- map from locations to a map from transitions to Dets
    Just $ \loc -> fromMaybe Map.empty $ loc `Map.lookup` tMapMap
    where
    addToMap :: (Ord loc, Ord t) => (m (tdest, loc) -> m (tdest, loc) -> Maybe (m (tdest, loc))) -> (te -> (loc, t, tdest, loc')) -> (loc' -> tdest -> t -> m (tdest, loc)) -> te -> Maybe (Map loc (Map t (m (tdest, loc)))) -> Maybe (Map loc (Map t (m (tdest, loc))))
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
concTransFromFunc fTrans alph loc = Map.fromSet fTransConc (foldableAsSet alph)
    where
    fTransConc t = ((),) <$> fTrans loc t

foldableAsSet :: (Foldable fld, Ord a) => fld a -> Set.Set a
foldableAsSet fld = Set.fromList $ Foldable.toList fld

accessSequences :: (Ord loc, Foldable m) => AutIntrpr m loc loc t tdest act -> loc -> Map loc [t]
accessSequences aut initLoc =
    let initialMap = Map.singleton initLoc []
    in fst $ accessSequences' (syntacticAutomaton aut) initialMap $ Set.singleton initLoc

accessSequences' :: (Ord loc, Foldable m) => AutSyntax m loc t tdest -> Map loc [t] -> Set.Set loc -> (Map loc [t], Set.Set loc)
accessSequences' aut accMap boundary = case takeArbitrary boundary of
    Nothing -> (accMap, Set.empty)
    Just (q, boundaryRem) ->
        let ts = transRel aut q
            labelqs = concatMap (\(l,qs) -> zip (replicate (length qs) l) qs) $ Map.toList $ Map.map getStates ts
            (accMap',new) = foldr (\(label,dq) (m,new') -> insertLabelAndDestLocInAccMap q label dq m new') (accMap,Set.empty) labelqs
        in accessSequences' aut accMap' (boundaryRem `Set.union` new)
        where
        getStates = fmap snd . Foldable.toList

insertLabelAndDestLocInAccMap :: (Ord loc) => loc -> t -> loc -> Map loc [t] -> Set.Set loc -> (Map loc [t], Set.Set loc)
insertLabelAndDestLocInAccMap q label dq accMap new = case Map.lookup q accMap of
    Nothing -> error "could not lookup known location for access sequence"
    Just accSeq -> case addStateAndAccSeq accMap dq (accSeq ++ [label]) of
        (newMap,Nothing) -> (newMap, new)
        (newMap, Just q') -> (newMap, Set.insert q' new)

addStateAndAccSeq :: (Ord loc) => Map loc [t] -> loc -> [t] -> (Map loc [t], Maybe loc)
addStateAndAccSeq accMap q accSeq = case Map.lookup q accMap of
        Nothing -> (Map.insert q accSeq accMap, Just q)
        Just _ -> (accMap, Nothing)

---------------------------------
-- instantiations of interpret --
---------------------------------

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions.
type ConcreteAutIntrpr m q act = AutIntrpr m q q act () act

-- | Interpret syntactical states and actions directly as literal, semantical states and actions.
interpretConcrete :: (BoundedMonad m, Ord t, Ord loc, Completable t) => AutSyntax m loc t () -> ConcreteAutIntrpr m loc t
interpretConcrete = flip interpret id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with timeouts as possible output observations.
type ConcreteSuspAutIntrpr m q i o = AutIntrpr m q q (IOAct i o) () (IOSuspAct i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with timeouts as possible output observations.
interpretQuiescentConcrete :: (BoundedMonad m, Ord i, Ord o, Ord loc) => AutSyntax m loc (IOAct i o) () -> ConcreteSuspAutIntrpr m loc i o
interpretQuiescentConcrete = flip interpret id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with input failures as possible input observations.
type ConcreteInputAttemptAutIntrpr m q i o = AutIntrpr m q q (IOAct i o) () (IFAct i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with input failures as possible input observations.
interpretInputAttemptConcrete :: (BoundedMonad m, Ord i, Ord o, Ord loc) => AutSyntax m loc (IOAct i o) () -> ConcreteInputAttemptAutIntrpr m loc i o
interpretInputAttemptConcrete = flip interpret id

-- | Semantics of automata in which syntactical states and actions are directly interpreted as literal, semantical states and actions, but with timeouts and input failures as possible observations.
type ConcreteSuspInputAttemptAutIntrpr m q i o = AutIntrpr m q q (IOAct i o) () (SuspendedIF i o)

-- | Interpret syntactical states and actions are directly as literal, semantical states and actions, but with timeouts and input failures as possible observations.
interpretQuiescentInputAttemptConcrete :: (BoundedMonad m, Ord i, Ord o, Ord loc) => AutSyntax m loc (IOAct i o) () -> ConcreteSuspInputAttemptAutIntrpr m loc i o
interpretQuiescentInputAttemptConcrete = flip interpret id

type STS m loc g = AutSyntax m loc (SymInteract g) STStdest
type IOSTS m loc i o = STS m loc (IOAct i o)

type STSIntrp m loc g = AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g)
type IOSTSIntrp m loc i o = STSIntrp m loc (IOAct i o)

interpretSTS :: (Ord loc, BoundedMonad m, Completable (GateValue g)) => STS m loc g -> Valuation -> STSIntrp m loc g
interpretSTS sts initialValuation = interpret sts (`IntrpState` initialValuation)

type SuspSTSIntrp m loc i o = AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOSuspGateValue i o)

interpretSTSQuiescent :: (Ord loc, BoundedMonad m) => IOSTS m loc i o -> Valuation -> SuspSTSIntrp m loc i o
interpretSTSQuiescent sts initialValuation = interpret sts (`IntrpState` initialValuation)

-- TODO also list an interpretation for quiescence only and input-failure only
type SuspInputAttemptSTSIntrp m loc i o = AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (SuspendedIFGateValue i o)

interpretSTSQuiescentInputAttemptConcrete  :: (Ord loc, BoundedMonad m) => IOSTS m loc i o -> Valuation -> SuspInputAttemptSTSIntrp m loc i o
interpretSTSQuiescentInputAttemptConcrete sts initialValuation = interpret sts (`IntrpState` initialValuation)

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
    | not (all (`Set.member` locs1) mergeLocs) = errorWithoutStackTrace $ fnName ++ ": one or more merging locations are not reachable in the first automaton"
    | otherwise = locs1
    where
    locs1 = allLocations sts1

-- | The transitions out of the initial location(s) of an automaton, for every element of its alphabet.
initialSwitches :: (Ord loc, Ord t, Ord tdest, BoundedMonad m) => AutSyntax m loc t tdest -> Map t (m (tdest, loc))
initialSwitches sts = Map.fromSet (\t -> BM.ordBind (initConf sts) (\l -> transRel sts l Map.! t)) (alphabet sts)

-- | Merge a transition of a merge location with the one copied onto it by a sequential composition: the two are conjuncted, but
-- only where both are specified (and not forbidden). Otherwise, the one that is specified is used as-is.
-- TODO: I feel like this should differ between inputs and outputs? This somehow feels wrong, but should look
-- at concrete examples to see what makes most sense.
-- It seems like it would be easier to reason about, as a user, if this function was simpler. For example,
-- mergeSwitch x Bottom = x, but mergeSwitch x y followed by a transition from y to Bottom is Bottom.
-- The obvious (to me) simple options are either always using 'other' (leave sts1 at the mergeloc), or always using 'own /\ other'.
-- And the main alternative I see is to choose between these options depending on whether it's an input or output.
mergeSwitch :: (BoundedConfiguration m, MeetSemiLattice (m a)) => m a -> m a -> m a
mergeSwitch own other
    | BM.isIndefinite own && BM.isIndefinite other = own /\ other
    | BM.isIndefinite own                          = own
    | otherwise                                    = other

{- |
    Sequentially compose two automata: sequentiallyAt sts1 locs sts2 merges sts2 into sts1 at the given locations of sts1. Where a merge
    location already specifies a transition for an action also in sts2's alphabet, and the copied transition from sts2 is also specified,
    the two are conjuncted with (/\). If only one of the two is specified (the other being forbidden or underspecified), that one is used as-is.
-}
sequentiallyAt :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, MeetSemiLattice (m (tdest, Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> [loc1] -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
sequentiallyAt sts1 mergeLocs sts2 = locs1 `seq` automaton newInitConf newAlphabet switches
    where
    locs1 = validMergeLocs "sequentiallyAt" sts1 mergeLocs
    locs2 = allLocations sts2
    mergeLocSet = Set.fromList mergeLocs

    newAlphabet = alphabet sts1 `Set.union` alphabet sts2
    newInitConf = Left BM.<#> initConf sts1

    -- transitions out of the initial location(s) of sts2, to be replicated onto every merge location of sts1
    initTransOf2 = Map.map (BM.ordMap (second Right)) (initialSwitches sts2)

    transOf1 l1
        | l1 `Set.member` mergeLocSet = Map.unionWith mergeSwitch ownTrans initTransOf2
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
(|>) :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, MeetSemiLattice (m (tdest, Either loc1 loc2))) =>
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
selfSequentiallyAt :: (Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, MeetSemiLattice (m (tdest, loc))) =>
    AutSyntax m loc t tdest -> [loc] -> AutSyntax m loc t tdest -> AutSyntax m loc t tdest
selfSequentiallyAt sts1 mergeLocs sts2 = locs1 `seq` automaton newInitConf newAlphabet switches
    where
    locs1 = validMergeLocs "selfSequentiallyAt" sts1 mergeLocs
    locs2 = allLocations sts2
    mergeLocSet = Set.fromList mergeLocs

    newAlphabet = alphabet sts1 `Set.union` alphabet sts2
    newInitConf = initConf sts1

    -- transitions out of the initial location(s) of sts2, to be replicated onto every merge location of sts1
    initTransOf2 = initialSwitches sts2

    transOf1 l1
        | l1 `Set.member` mergeLocSet = Map.unionWith mergeSwitch (transRel sts1 l1) initTransOf2
        | otherwise                   = transRel sts1 l1

    switches1 = Map.fromList [ (l1, transOf1 l1) | l1 <- Set.toList locs1 ]
    switches2 = Map.fromList
        [ (l2, transRel sts2 l2)
        | l2 <- Set.toList locs2 ]

    allSwitches = switches1 `Map.union` switches2
    switches loc = Map.findWithDefault Map.empty loc allSwitches

infixl 1 |>>
-- | `selfSequentiallyAt` applied to all sink locations of the first automaton. Throws an error if the first automaton does not have any sink locations.
(|>>) :: (Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, MeetSemiLattice (m (tdest, loc))) =>
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
renameLocs :: (Ord loc, Ord loc', Ord tdest, BoundedMonad m, Foldable m) =>
    (loc -> loc') -> AutSyntax m loc t tdest ->
    (m loc', Map.Map loc' (Map.Map t (m (tdest, loc'))))
renameLocs renamingFun sts = (renamingFun BM.<#> initConf sts, wrappedSwitches)
  where
    wrappedSwitches = Map.fromList
        [ (renamingFun l, Map.map (BM.ordMap (second renamingFun)) (transRel sts l))
        | l <- Set.toList (allLocations sts)
        ]

-- | Combine automata with the same loc type
composeGeneric :: (Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t) =>
    (m loc -> m loc -> m loc) -> Set.Set t ->
    [(m loc, Map.Map loc (Map.Map t (m (tdest, loc))))] ->
    AutSyntax m loc t tdest
composeGeneric combine newAlphabet renamedLocs
    | any (\(ic, _) -> Foldable.length ic /= 1) renamedLocs = errorWithoutStackTrace
        "composeGeneric: the initial state of the automaton(s) is not atomic, which is currently not supported"
    | otherwise = automaton newInitConf newAlphabet switches
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
composeInitial :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t) =>
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
(//\\) :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, MeetSemiLattice (m (Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
(//\\) = composeInitial (/\)

infixl 1 \\//
{- |
    Given two automata, return their disjunction. This disjunction is done by merging the initial states of both with \/, and replacing all instances
    of the initial locations in the transitions of sts1 and sts2 with the composed initial state. The resulting automaton has a joint alphabet and locations of
    type 'Either loc1 loc2'.
-}
(\\//) :: (Ord loc1, Ord loc2, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, JoinSemiLattice (m (Either loc1 loc2))) =>
    AutSyntax m loc1 t tdest -> AutSyntax m loc2 t tdest -> AutSyntax m (Either loc1 loc2) t tdest
(\\//) = composeInitial (\/)

{- |
    Compose the initial state of any number of labeled automata (all sharing the same location type) with the given operator, and
    redirect every transition in each automaton that leads back to one of its own initial locations to the composed initial state instead. 
    Every other transition is kept as-is, just tagged as a tuple (k, loc) where k is the automaton's label.
    Throws an error if the list is empty, or if any label is used more than once.
-}
composeInitialAll :: (Ord k, Show k, Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t) =>
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
conjunctionAll :: (Ord k, Show k, Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, MeetSemiLattice (m (k, loc))) =>
    [(k, AutSyntax m loc t tdest)] -> AutSyntax m (k, loc) t tdest
conjunctionAll = composeInitialAll (/\)

{- |
    The disjunction of any number of labeled automata. Locations are identified with a tuple of sts identifier and location of such automaton.
    All STSs must share the same location type. Throws an error if the list is empty, or if any label is used more than once.
-}
disjunctionAll :: (Ord k, Show k, Ord loc, Ord t, Ord tdest, BoundedMonad m, Foldable m, Completable t, JoinSemiLattice (m (k, loc))) =>
    [(k, AutSyntax m loc t tdest)] -> AutSyntax m (k, loc) t tdest
disjunctionAll = composeInitialAll (\/)

{- |
    A location of an STS is either 'Stable' (a location's own behaviour) or 'Pending' 
    a specific output.
-}
data CheckLoc loc g = Stable loc | Pending loc g loc deriving (Eq, Ord)

instance (Show loc, Show g) => Show (CheckLoc loc g) where
    show (Stable loc)          = show loc
    show (Pending _ g target) = "pending " ++ show g ++ " -> " ++ show target

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
        -- keep input switches as-is
        -- keep input switches as-is
        -- keep input switches as-is

        -- keep input switches as-is

        -- keep input switches as-is
        
        -- keep input switches as-is
        -- keep input switches as-is

        -- keep input switches as-is
        [ (t, BM.ordMap (second Stable) mval) | (t, mval) <- Map.toList (transRel sts loc), not (isOutputInteract t) ]
        ++
        -- output switches are replaced by a check gate leading to a pending state
        -- output switches are replaced by a check gate leading to a pending state
        -- output switches are replaced by a check gate leading to a pending state
        -- output switches are replaced by a check gate leading to a pending state
        [ (checkGateFor t, BM.ordMap (\(_, target) -> (identityTdest, Pending loc t target)) mval)
        | (t, mval) <- Map.toList (transRel sts loc), isOutputInteract t, not (BM.isForbidden mval) ]

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


-- | What `sequentiallyAtPruned` removed from the composition.
data Pruned loc1 loc2 t
    -- TODO: This is an alternative to returning a warning (we can process it afterwards), but we need this distinction
    = PrunedLocation loc1 -- ^ a location of the first automaton that was removed
    | UnsatisfiableOutput loc1 t [loc1] -- ^ warning: an output switch of the first automaton, given by its location and gate, is unsatisfiable. Its branch is kept, but the given merge locations in that branch are not merged
    | PrunedSwitch loc1 t (FreeLattice loc2) -- ^ the unsatisfiable switches for a gate, from a merge location to locations of the second automaton
    deriving (Eq, Show)

-- | Remove the atoms satisfying the predicate from a state configuration, leaving the rest of its structure intact.
dropAtoms :: Ord a => (a -> Bool) -> FreeLattice a -> FreeLattice a
dropAtoms isDropped conf@(BM.FreeLattice clauses)
    | not (any isDropped conf) = conf
    | otherwise = BM.meets
        [ BM.joins (atom <$> Set.toList clause')
        | clause <- Set.toList clauses
        , let clause' = Set.filter (not . isDropped) clause
        , not (Set.null clause') || Set.null clause ]

{- |
    A single step of symbolic execution. Given the location variables, the number of steps taken so far, and the symbolic
    values of the location variables after those steps, take a switch: return its guard over the interaction variables, 
    and the symbolic values of the location variables after the switch.
-}
symStep :: [Some Variable] -> Int -> VarModel -> STStdest -> (SymGuard, VarModel)
symStep locVars n pvar (STSLoc (tguard, tassign)) = (indexedGuard, pvar')
    where
    completedAssign = tassign `varUnion` identityVarModel locVars
    indexedGuard = subst pvar (indexExpr n tguard)
    pvar' = substVarModel pvar (mapVars (indexVar (n+1)) $ mapVarExprs (indexVar n) completedAssign)

-- | The distinct atoms of a state configuration.
atomsOf :: (Foldable m, Ord a) => m a -> [a]
atomsOf = Set.toList . Set.fromList . toList

-- | Whether a guard is satisfiable, according to the SMT solver. The outcome is cached per guard, so that a guard is only solved once.
satisfiable :: SymGuard -> Bool
satisfiable guard = unsafePerformIO $ do
    cache <- readIORef satisfiableCache
    case Map.lookup guard cache of
        Just isSat -> return isSat
        Nothing -> do
            isSat <- Maybe.isJust <$> solveGuard (toList $ freeVars guard) guard
            atomicModifyIORef' satisfiableCache $ \c -> (Map.insert guard isSat c, ())
            return isSat

-- the guards solved so far by `satisfiable`, with their outcome
satisfiableCache :: IORef (Map SymGuard Bool)
satisfiableCache = unsafePerformIO $ newIORef Map.empty
{-# NOINLINE satisfiableCache #-}

-- | Check that the automaton is a tree: every location has at most one incoming switch, and the initial locations have none.
-- Returns the given locations of the automaton, or throws an error mentioning the given function name.
checkTree :: (Ord loc, Show loc, Ord tdest, Foldable m) => String -> AutSyntax m loc t tdest -> Set loc -> Set loc
checkTree fnName sts locs
    | null offenders = locs
    | otherwise = errorWithoutStackTrace $ fnName ++ ": the first automaton is not a tree; locations with more than one incoming switch"
        <> " (or initial locations with an incoming switch): " <> show offenders
    where
    incoming = Map.fromListWith (+) $
        [ (l, 1 :: Int) | l <- atomsOf (initConf sts) ] ++
        [ (l', 1) | l <- Set.toList locs, dests <- Map.elems (transRel sts l), (_, l') <- atomsOf dests ]
    offenders = Map.keys $ Map.filter (> 1) incoming

{- |
    Symbolic execution of an automaton that is a tree, given the state variables and the symbolic values of those variables in every
    initial location. For every location with a satisfiable path of switches leading to it: the path condition to get there, the
    symbolic values of the state variables once there, and the number of steps taken to get there.
-}
symbolicTree :: (Ord loc, Foldable m) => AutSyntax m loc t STStdest -> [Some Variable] -> (loc -> VarModel) -> Map loc (SymGuard, VarModel, Int)
symbolicTree sts locVars initModel = explore Map.empty [ (l, (sTrue, initModel l, 0)) | l <- atomsOf (initConf sts) ]
    where
    explore acc [] = acc
    explore acc ((l, st@(pathCond, pvar, n)) : rest) = explore (Map.insert l st acc) (successors ++ rest)
        where
        successors =
            [ (l', (pathCond', pvar', n + 1))
            | dests <- Map.elems (transRel sts l)
            , (tdest, l') <- atomsOf dests
            , let (guard, pvar') = symStep locVars n pvar tdest
            , let pathCond' = pathCond .&& guard
            , satisfiable pathCond' ]

{- |
    For the given locations of a symbolically executed tree: the given switches, pruned to the ones that are
    satisfiable there, together with a report of what was pruned away. Within a state configuration, the unsatisfiable switches
    become the implicit destination of their gate. In a location without a symbolic state, nothing is satisfiable.
-}
pruneSwitchesAt :: (Ord loc1, Ord loc2, Ord t, Completable t) =>
    [Some Variable] -> Map loc1 (SymGuard, VarModel, Int) -> [loc1] -> Map t (FreeLattice (STStdest, loc2)) ->
    Map loc1 (Map t (FreeLattice (STStdest, loc2)), [Pruned loc1 loc2 t])
pruneSwitchesAt locVars symStates locs trans = Map.fromList [ (l1, pruneAt l1) | l1 <- locs ]
    where
    pruneAt l1 = (kept, pruned)
        where
        satisfiableSwitches = Set.fromList
            [ (t, dest)
            | Just (pathCond, pvar, n) <- [Map.lookup l1 symStates]
            , (t, dests) <- Map.toList trans
            , dest@(tdest, _) <- atomsOf dests
            , satisfiable (pathCond .&& fst (symStep locVars n pvar tdest)) ]
        isSatisfiable t dest = (t, dest) `Set.member` satisfiableSwitches

        kept = flip Map.mapWithKey trans $ \t dests -> BM.ordBind dests $ \dest ->
            if isSatisfiable t dest
                then BM.ordReturn dest
                else implicitDestination t

        pruned =
            [ PrunedSwitch l1 t (BM.ordMap snd prunedDests)
            | (t, dests) <- Map.toList trans
            , let prunedDests = dropAtoms (isSatisfiable t) dests
            , not (null prunedDests) ]

{- |
    Sequentially compose two automata: sequentiallyAt sts1 locs sts2 merges sts2 into sts1 at the given locations of sts1. Where a merge
    location already specifies a transition for an action also in sts2's alphabet, and the copied transition from sts2 is also specified,
    the two are conjuncted with (/\). If only one of the two is specified (the other being forbidden or underspecified), that one is used as-is.
    This version prunes merge transitions that aren't satisfiable away, but requires sts1 to be a tree (no loops).
    This version takes an AutIntrpr for sts1, because we need an initial valuation to compute reachability. 
    (Input) switches of sts1 that are not satisfiable according to this initial valuation are also pruned. In general, the criteria for
    prunning goes as follows:

    * If an input switch of sts1 is unsatisfiable, the branch that it is on is removed: everything after that switch, and everything
      before it up to the last output switch (or up to and including the initial location, if there is no output switch before it).
    * If an output switch of sts1 is unsatisfiable, the branch that it is on is kept as-is, but the merge locations after that
      switch are not merged. This is reported as an `UnsatisfiableOutput`.
    * A switch from a merge location into sts2 is only kept if its guard is satisfiable in that merge location.

    Returns both the pruned sequentially composed automaton, and a list of pruned switchs (if any).
-}
sequentiallyAtPruned :: forall loc1 loc2 i o act. (Ord loc1, Ord loc2, Show loc1, Ord i, Ord o) =>
    AutIntrpr FreeLattice loc1 (IntrpState loc1) (IOSymInteract i o) STStdest act -> [loc1] -> AutSyntax FreeLattice loc2 (IOSymInteract i o) STStdest ->
    (AutIntrpr FreeLattice (Either loc1 loc2) (IntrpState (Either loc1 loc2)) (IOSymInteract i o) STStdest act, [Pruned loc1 loc2 (IOSymInteract i o)])
sequentiallyAtPruned (AutInterpretation stateconf1 sts1) mergeLocs sts2 = locs1 `seq` (AutInterpretation newStateConf $ automaton newInitConf newAlphabet switches, pruned)
    where
    locs1 = checkTree "sequentiallyAtPruned" sts1 $ validMergeLocs "sequentiallyAtPruned" sts1 mergeLocs
    locs2 = allLocations sts2
    mergeLocSet = Set.fromList mergeLocs

    newAlphabet = alphabet sts1 `Set.union` alphabet sts2
    -- If one of the branches of STS1 is removed, we remove its initial location as well from the initial Configuration
    newInitConf = Left BM.<#> dropAtoms isRemoved (initConf sts1)
    newStateConf = fmap Left BM.<#> dropAtoms (\(IntrpState l _) -> isRemoved l) stateconf1

    initVals = Map.fromList [ (l, v) | IntrpState l v <- toList stateconf1 ]
    locVars = case toList stateconf1 of
        IntrpState _ v : _ -> getVariables v
        []                 -> []

    -- symbolic execution of the tree sts1, starting from the initial valuation
    symStates = symbolicTree sts1 locVars $ \l -> valuationToVarModel $
        Map.findWithDefault (errorWithoutStackTrace $ "sequentiallyAtPruned: no valuation for initial location " <> show l) l initVals

    isReachable l = l `Map.member` symStates
    -- the locations directly after a location, i.e. one switch further
    successorsOf l = [ l' | dests <- Map.elems (transRel sts1 l), (_, l') <- atomsOf dests ]
    -- a location together with all locations after it
    branchFrom l = l : concatMap branchFrom (successorsOf l)
    -- the gate of the single switch leading into a location
    incomingGate = Map.fromList
        [ (l', t) | l <- Set.toList locs1, (t, dests) <- Map.toList (transRel sts1 l), (_, l') <- atomsOf dests ]

    -- the unsatisfiable output switches: the branch after such a switch is kept as-is, but isn't merged
    unsatOutputs =
        [ (l, t, l')
        | l <- Set.toList locs1, isReachable l
        , (t, dests) <- Map.toList (transRel sts1 l), isOutputInteract t
        , (_, l') <- atomsOf dests, not (isReachable l') ]
    postUnsatOutputLocs = Set.fromList $ concat [ branchFrom l' | (_, _, l') <- unsatOutputs ] -- All locations in a branch after an unsat output

    keptMap = Map.fromSet kept locs1
    kept l
        | l `Set.member` postUnsatOutputLocs                    = True     -- Keep locations right after an unsat output (tests derived from this branch will Fail) even when unreachable
        | not (isReachable l)                                   = False    -- Remove non reachable locations
        | isSinkLocation sts1 l || l `Set.member` mergeLocSet   = True     -- Keep merge locations/sink locations
        | any (not . isRemoved) (successorsOf l)                = True     -- Keep l if its successor is kept
        | otherwise                                             = maybe False isOutputInteract (Map.lookup l incomingGate) -- No locations after l: keep only if the incoming switch is an output
    isRemoved l = not $ Map.findWithDefault False l keptMap
    keptLocs = Map.keysSet $ Map.filter id keptMap
    mergeableLocs = Set.filter (\l -> isReachable l && not (isRemoved l)) mergeLocSet

    -- per mergeable location, the initial switches of sts2 that are satisfiable there, and the ones that we pruned away
    prunedAt = pruneSwitchesAt locVars symStates (Set.toList mergeableLocs) (initialSwitches sts2)

    -- sts1's own transitions, where a switch to a removed location is no longer specified
    ownTransOf1 l1 = flip Map.mapWithKey (transRel sts1 l1) $ \t dests -> BM.ordBind dests $ \(tdest, l1') ->
        if isRemoved l1'
            then implicitDestination t
            else BM.ordReturn (tdest, Left l1')

    -- the locations of sts1 and the transitions from sts1 to sts2 that we pruned away, and the unsatisfiable outputs of sts1
    pruned = map PrunedLocation (Set.toList $ locs1 Set.\\ keptLocs) ++
        [ UnsatisfiableOutput l t (filter (`Set.member` mergeLocSet) $ branchFrom l') | (l, t, l') <- unsatOutputs ] ++
        concatMap snd (Map.elems prunedAt)

    transOf1 l1 = case Map.lookup l1 prunedAt of
        Just (newTrans, _) -> Map.unionWith mergeSwitch (ownTransOf1 l1) (Map.map (BM.ordMap (second Right)) newTrans)
        Nothing            -> ownTransOf1 l1

    switches1 = Map.fromList [ (Left l1, transOf1 l1) | l1 <- Set.toList keptLocs ]
    switches2 = Map.fromList
        [ (Right l2, Map.map (BM.ordMap (second Right)) (transRel sts2 l2))
        | l2 <- Set.toList locs2 ]

    allSwitches = switches1 `Map.union` switches2
    switches loc = Map.findWithDefault Map.empty loc allSwitches


infixl 1 `sequentiallyPruned`
-- | Sequentially compose two automata at all sink locations of the first (with pruning). Throws an error if the first automaton does not have any sink locations.
sequentiallyPruned :: (Ord loc1, Ord loc2, Show loc1, Ord i, Ord o) =>
    AutIntrpr FreeLattice loc1 (IntrpState loc1) (IOSymInteract i o) STStdest act -> AutSyntax FreeLattice loc2 (IOSymInteract i o) STStdest ->
    (AutIntrpr FreeLattice (Either loc1 loc2) (IntrpState (Either loc1 loc2)) (IOSymInteract i o) STStdest act, [Pruned loc1 loc2 (IOSymInteract i o)])
sts1 `sequentiallyPruned` sts2 = case Set.toList $ Set.filter (isSinkLocation syn1) (allLocations syn1) of
    []      -> errorWithoutStackTrace "(sequentiallyPruned): the first automaton has no sink location to sequentially compose at"
    locList -> sequentiallyAtPruned sts1 locList sts2
    where syn1 = syntacticAutomaton sts1

{- |
    Sequentially compose an automaton with itself, like `selfSequentiallyAt` with the same automaton twice. This version 
    prunes the copied switches of which the guard isn't satisfiable in that merge location, but requires the automaton to be a tree. 

    The initial valuation is not considered; a switch is pruned if its guard is unsatisfiable after the path of switches to
    the merge location, starting from arbitrary values for the given location variables.

    Returns both the pruned sequentially composed automaton, and a list of the pruned away switches (if any).
-}
selfSequentiallyAtPruned :: (Ord loc, Show loc, Ord i, Ord o) =>
    [Some Variable] -> AutSyntax FreeLattice loc (IOSymInteract i o) STStdest -> [loc] ->
    (AutSyntax FreeLattice loc (IOSymInteract i o) STStdest, [Pruned loc loc (IOSymInteract i o)])
selfSequentiallyAtPruned locVars sts mergeLocs = locs `seq` (automaton (initConf sts) (alphabet sts) switches, pruned)
    where
    locs = checkTree "selfSequentiallyAtPruned" sts $ validMergeLocs "selfSequentiallyAtPruned" sts mergeLocs

    -- symbolic execution of the tree, starting from arbitrary values for the location variables
    symStates = symbolicTree sts locVars (const $ identityVarModel locVars)

    -- per merge location, the initial switches that are satisfiable there, and the ones that we pruned away
    prunedAt = pruneSwitchesAt locVars symStates (Set.toList $ Set.fromList mergeLocs) (initialSwitches sts)
    pruned = concatMap snd (Map.elems prunedAt)

    switches l = case Map.lookup l prunedAt of
        Just (newTrans, _) -> Map.unionWith mergeSwitch (transRel sts l) newTrans
        Nothing            -> transRel sts l

-- | `selfSequentiallyAtPruned` applied to all sink locations of the automaton. Throws an error if the automaton does not have any sink locations.
selfSequentiallyPruned :: (Ord loc, Show loc, Ord i, Ord o) =>
    [Some Variable] -> AutSyntax FreeLattice loc (IOSymInteract i o) STStdest ->
    (AutSyntax FreeLattice loc (IOSymInteract i o) STStdest, [Pruned loc loc (IOSymInteract i o)])
selfSequentiallyPruned locVars sts = case Set.toList $ Set.filter (isSinkLocation sts) (allLocations sts) of
    []      -> errorWithoutStackTrace "selfSequentiallyPruned: the automaton has no sink location to sequentially compose at"
    locList -> selfSequentiallyAtPruned locVars sts locList
