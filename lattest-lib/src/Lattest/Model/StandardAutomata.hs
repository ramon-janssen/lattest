{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
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
-- * Sequential composition
sequentiallyAt,
sequentiallyAtPruned,
(|>),
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
)
where

import Lattest.Model.Alphabet (IOAct(..), IOSuspAct, IFAct, SuspendedIF, SymInteract (..), IOSymInteract, GateValue, SuspendedIFGateValue, IOSuspGateValue, isOutputInteract)
import Lattest.Model.Automaton (AutSyntax (..), automaton, interpret, Completable, implicitDestination,IntrpState(..),STStdest, transRel,syntacticAutomaton, AutIntrpr(..), reachable, stsTLoc)
import Lattest.Model.BoundedMonad (Det(..), BoundedMonad, FreeLattice, atom, top, bot, (\/), (/\), JoinSemiLattice, MeetSemiLattice, BoundedConfiguration)
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
import Lattest.Model.Symbolic.SolveSTS (interactsToSpecifiedCondition, interactsToAllowedCondition)
import System.IO.Unsafe (unsafePerformIO)
import Lattest.SMT (runSMT)
import Lattest.Model.Symbolic.SolveSymPrim (solveGuard)

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
    | not (all (`Set.member` locs1) mergeLocs) = errorWithoutStackTrace $ fnName ++ ": one or more locations are not reachable in the first automaton"
    | otherwise = locs1
    where
    locs1 = allLocations sts1

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
    initTransOf2 = Map.fromList
        [ (t, BM.ordMap (second Right) (BM.ordBind (initConf sts2) (\l2 -> transRel sts2 l2 Map.! t)))
        | t <- Set.toList (alphabet sts2) ]

    -- conjunct sts1's own transition with the copied one, but only where both are specified (and not forbiddden)
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


{- |
    Sequentially compose two automata: sequentiallyAt sts1 locs sts2 merges sts2 into sts1 at the given locations of sts1. Where a merge
    location already specifies a transition for an action also in sts2's alphabet, and the copied transition from sts2 is also specified,
    the two are conjuncted with (/\). If only one of the two is specified (the other being forbidden or underspecified), that one is used as-is.
    This version prunes merge transitions that aren't satisfiable away, but requires sts1 to be a tree (no loops).
    This version takes an AutIntrpr for sts1, because we need an initial valuation to compute reachability.
-}
sequentiallyAtPruned
  :: (Ord loc1, Ord loc2, Show loc1, BoundedMonad m, Foldable m, MeetSemiLattice (m (STStdest, Either loc1 loc2)), BM.BooleanConfiguration m, Ord i, Ord o, forall a. Ord a => Ord (m a))
  => AutIntrpr m loc1 (IntrpState loc1) (IOSymInteract i o) STStdest act
  -> [loc1]
  -> AutSyntax m loc2 (IOSymInteract i o) STStdest
  -> AutSyntax m (Either loc1 loc2) (IOSymInteract i o) STStdest
sequentiallyAtPruned (AutInterpretation initconf sts1) mergeLocs sts2 = locs1 `seq` automaton newInitConf newAlphabet switches
    where
    locs1 = validMergeLocs "sequentiallyAt" sts1 mergeLocs
    locs2 = allLocations sts2
    mergeLocSet = Set.fromList mergeLocs

    newAlphabet = alphabet sts1 `Set.union` alphabet sts2
    newInitConf = Left BM.<#> initConf sts1

    -- transitions out of the initial location(s) of sts2, to be replicated onto every merge location of sts1
    initTransOf2 = Map.fromList
        [ (t, second Right BM.<#> (initConf sts2 BM.#>> \l2 -> transRel sts2 l2 Map.! t))
        | t <- Set.toList (alphabet sts2) ]

    -- the new transitions we actually add to this location, i.e. those of initTransOf2 that are satisfiable
    newTransOf1 l1 = let tr = getTraceTo l1
      in flip Map.filterWithKey initTransOf2 $
          \t _ -> Maybe.isJust $ unsafePerformIO $ runSMT $ solveGuard [] $
             case t of
               SymInteract (In _)  _ -> interactsToSpecifiedCondition (AutInterpretation initconf sts1) (tr ++ [t])
               SymInteract (Out _) _ -> interactsToAllowedCondition (AutInterpretation initconf sts1) (tr ++ [t])


    -- conjunct sts1's own transition with the copied one, but only where both are specified (and not forbiddden)
    -- TODO: I feel like this should differ between inputs and outputs? This somehow feels wrong, but should look
    -- at concrete examples to see what makes most sense
    pick own other
        | BM.isIndefinite own && BM.isIndefinite other = own /\ other
        | BM.isIndefinite own                          = own
        | otherwise                                    = other

    transOf1 l1
        | l1 `Set.member` mergeLocSet = Map.unionWith pick ownTrans $ newTransOf1 l1
        | otherwise                   = ownTrans
        where
        ownTrans = Map.map (second Left BM.<#>) (transRel sts1 l1)

    switches1 = Map.fromList [ (Left l1, transOf1 l1) | l1 <- Set.toList locs1 ]
    switches2 = Map.fromList
        [ (Right l2, Map.map (BM.ordMap (second Right)) (transRel sts2 l2))
        | l2 <- Set.toList locs2 ]

    allSwitches = switches1 `Map.union` switches2
    switches loc = Map.findWithDefault Map.empty loc allSwitches

    getTraceTo = reverse . getInvertedTraceTo
    flippedMap1 = Map.fromList $
      (\xs -> if length xs == length (List.nub $ map fst xs) then xs else error "sts1 is not a tree") $
      [ (snd BM.<#> to, (interact, from))
      | from <- Set.toList $ allLocations sts1
      , (interact, to) <- Map.toList $ transRel sts1 from]
    getInvertedTraceTo l = case flippedMap1 Map.!? BM.ordReturn l of
      Nothing -> if BM.ordReturn l == initConf sts1 then [] else error $ "unreachable location: " <> show l
      Just (interact, source) -> interact : getInvertedTraceTo source

