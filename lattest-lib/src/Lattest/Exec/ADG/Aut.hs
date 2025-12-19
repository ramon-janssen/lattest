{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE  DefaultSignatures #-}

module Lattest.Exec.ADG.Aut(Aut(..),State(..),show,after,computeCompRel,inp,out,enab,trans,initial,states,inputs,outputs,outSet,afterSet,
        statesToAut,addDelta,afterSequence,inSet,getAccesSequences, adgAutFromAutomaton,
        getTransitionExtendedAccesSequences,union,constrAut,printCompRel,getDistingCompPairs) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.List as List
import qualified Data.Foldable as Foldable
import qualified Lattest.Model.Automaton as Automaton
import qualified Lattest.Model.StandardAutomata as StandardAutomata
import Lattest.Model.BoundedMonad(Det(..))
import Lattest.Model.Alphabet(IOAct(..),isInput,asSuspended,IOSuspAct(..),Suspended(..))

import Debug.Trace as Trace

data Aut a b = Aut {initial :: (State a b), states :: Set (State a b), idStateMap :: (Map a (State a b)), inputs ::  (Set b), outputs :: (Set b)}

instance (Show a, Show b) => Show (Aut a b) where
    show (Aut initial states map inps outs) = "Initial: " ++ (show initial) ++ "\n" ++
                                        "States: " ++ (show $ Set.toList $ states) ++ "\n" ++
                                        "Input alphabet:" ++ (show $ inps) ++
                                        "Output alphabet:" ++ (show $ outs)
                                        --"IdStateMap: " ++ (show $ (Map.mapKeys Util.stateToName . Map.map (Util.stateToName . sid)) map)

data State a b = State {sid :: a, inp :: Set b, out :: Set b, trans :: Map b a}
    deriving (Ord)

instance (Show a) => (Show (State a b)) where
    show s = show $ sid s

instance (Eq a) => Eq (State a b) where
    (==) s1 s2 = (sid s1) == (sid s2)
    (/=) s1 s2 = (sid s1) /= (sid s2)

statesToAut :: (Ord a,Ord b) => State a b -> Set (State a b) -> Aut a b
statesToAut ini states = let (map,inps,outs) = Set.foldr (\s (map,inps,outs) -> (Map.insert (sid s) s map, Set.union inps (inp s), Set.union outs (out s))) (Map.empty,Set.empty,Set.empty) states
                            in Aut ini states map inps outs

enab :: Ord b => (State a b) -> Set b
enab s = Set.union (inp s) (out s)

outSet :: Ord b => Set (State a b) -> Set b
outSet set = Set.foldl (\chans state -> Set.union chans (out state)) Set.empty set

inSet :: Ord b => Set (State a b) -> Set b
inSet set = Set.foldl (\chans state -> Set.union chans (inp state)) Set.empty set

after :: (Ord a, Ord b) => (State a b) -> b -> (Aut a b) -> Maybe (State a b)
after state mu aut =  case (Map.lookup mu (trans state)) of
                                    Nothing -> Nothing
                                    Just s -> Map.lookup s (idStateMap aut)

afterSet :: (Ord a, Ord b) => Set (State a b) -> b -> (Aut a b) -> Set (State a b)
afterSet stateSet mu aut = Set.foldl (\set s -> case after s mu aut of Nothing -> set; Just s' -> Set.insert s' set) Set.empty stateSet

afterSequence :: (Ord a, Ord b) => (State a b) -> [b] -> (Aut a b) -> Maybe (State a b)
afterSequence state [] aut = Just state
afterSequence state (mu:mus) aut =
    case after state mu aut of
        Nothing -> Nothing
        Just s -> afterSequence s mus aut

computeCompRel :: (Ord a, Ord b) => Aut a b -> Set (State a b,State a b)
computeCompRel aut = computeCompRelAbstract aut firstCompRel expandCompRel

firstCompRel :: (Ord a, Ord b) => (Aut a b) -> Set (State a b,State a b)
firstCompRel aut = Set.fromList [(q,q') | q <- Set.toList (states aut),  q' <- Set.toList (states aut)]

expandCompRel :: (Ord a, Ord b) => (Aut a b) -> Set (State a b,State a b) -> Set (State a b,State a b)
expandCompRel aut@(Aut _ states _ _ _) rel =
    Set.fromList [(q,q') | q <- Set.toList states, q' <- Set.toList states,
             let mem = compMemFunc aut rel q q',
             (all mem (Set.intersection (inp q) (inp q'))) && (any mem (Set.intersection (out q) (out q')))]
{-
pexpandCompRel :: (Ord a, Ord b, Show a) => (Aut a b) -> Set (State a b,State a b) -> Set (State a b,State a b)
pexpandCompRel aut@(Aut _ states _ _ _) rel =
    fst $ Util.pfold (\(p1,b1) (p2,b2) ->
              if b1 && b2
              then (Set.union p1 p2,True)
              else if b1
                   then (p1,True)
                   else if b2 then (p2,True) else (Set.empty,False))
          (List.map (\(q,q') -> let mem = compMemFunc aut rel q q'
                                in (Set.singleton (q,q), (all mem (Set.intersection (inp q) (inp q'))) && (any mem (Set.intersection (out q) (out q')))))
                 [(q,q') | q <- Set.toList states, q' <- Set.toList states])
-}

compMemFunc :: (Ord a, Ord b) => (Aut a b) -> Set (State a b,State a b) -> State a b -> State a b -> b -> Bool
compMemFunc aut rel q q' c = Set.member (Maybe.fromJust $ after q c aut, Maybe.fromJust $ after q' c aut)  rel

computeCompRelAbstract :: (Ord a, Ord b, Eq c) => Aut a b -> (Aut a b -> c) -> (Aut a b -> c -> c) -> c
computeCompRelAbstract aut firstAbstract expand =
    let first = firstAbstract aut
        second = expand aut first
    in computeCompRecAbstract first second (expand aut)

computeCompRecAbstract :: (Eq c) => c -> c -> (c -> c) -> c
computeCompRecAbstract first second f = if first == second then first
                                        else computeCompRecAbstract second (f second) f

getAccesSequences :: (Ord a,Ord b) => Aut a b -> [[b]]
getAccesSequences aut = Map.elems $ getAccesSequences' aut (Set.singleton $ initial aut) (Map.singleton (initial aut) [])

getAccesSequences' :: (Ord a,Ord b) => Aut a b -> Set (State a b) -> Map (State a b) [b] -> Map (State a b) [b]
getAccesSequences' aut toInv accMap =
    if Set.null toInv then accMap
    else let state = Set.elemAt 0 toInv
             (newToInv,newAccMap) = List.foldr (\(mu,dest) (inv,map) ->
                                                let destState = (idStateMap aut) ! dest
                                                in if Map.notMember destState map
                                                    then (Set.insert destState inv, Map.insert destState ((map ! state) ++ [mu]) map)
                                                    else (inv,map)) ((Set.delete state toInv),accMap) (Map.toList (trans state))
         in getAccesSequences' aut newToInv newAccMap

extendAccWithTransition :: (Ord a,Ord b) => Aut a b -> [b] -> Set [b]
extendAccWithTransition aut acc =
    let state = Maybe.fromJust (afterSequence (initial aut) acc aut)
    in Set.map (\mu -> acc ++ [mu]) (enab state)

getTransitionExtendedAccesSequences :: (Ord a,Ord b) => Aut a b -> [[b]]
getTransitionExtendedAccesSequences aut = Set.toList $ Set.unions $ Set.fromList (getAccesSequences aut) : List.map (extendAccWithTransition aut) (getAccesSequences aut)

union :: (Ord a,Ord b) => Aut a b -> Aut a b -> Aut a b
union (Aut initial1 states1 idStateMap1 inputs1 outputs1) (Aut initial2 states2 idStateMap2 inputs2 outputs2) =
    if Set.null $ Set.intersection states1 states2
    then (Aut initial1 (Set.union states1 states2) (Map.union idStateMap1 idStateMap2) (Set.union inputs1 inputs2) (Set.union outputs1 outputs2))
    else error "states identifiers of automata not disjunct"

constrAut :: (Ord a, Ord b, Show a, Show b) => (a, Set (a,b,a), Set b, Set b) -> Aut a b
constrAut (initial, transs, inps, outs) =
    let statemap = stautToStateMap transs inps outs
        noTransStates = [t | (f,mu,t) <- Set.toList transs, Map.notMember t statemap]
        fullStateMap = List.foldr (\s m -> Map.insert s (Set.empty,Set.empty,Map.empty) m) statemap noTransStates
         in case Map.lookup initial fullStateMap of
                Nothing -> error ("Initial state does not have any transitions")
                Just (ini,outi,tmapi) ->
                    let statesandmap = getStatesAndMap fullStateMap
                     in Aut (State initial ini outi tmapi) (fst statesandmap) (snd statesandmap) inps outs

addDelta :: (Ord a) => String -> (Aut a String) -> (Aut a String)
addDelta delta (Aut initial states idStateMap inputs outputs) =
    let newStates = Set.foldl (\set s@(State sid inp out trans) ->
                                       if Set.null out
                                       then Set.insert (State sid inp (Set.insert delta out) (Map.insert delta sid trans)) set
                                       else Set.insert s set) Set.empty states
        stateMap = (Map.fromList $ List.map (\s -> (sid s,s)) $ Set.toList newStates)
    in (Aut (stateMap Map.! sid initial) newStates stateMap inputs (Set.insert delta outputs))

getStatesAndMap :: (Ord a, Ord b) => Map a (Set b, Set b, Map b a) -> (Set (State a b), Map a (State a b))
getStatesAndMap statemap =
    (Map.foldlWithKey (\setandmap key val -> case val of
        (ins,outs,tmaps) ->
            let state = (State key ins outs tmaps)
            in (Set.insert state (fst setandmap), Map.insert key state (snd setandmap))) (Set.empty,Map.empty) statemap)

stautToStateMap :: (Ord a, Ord b, Show a, Show b) => Set (a,b,a) -> Set b -> Set b -> Map a (Set b, Set b, Map b a)
stautToStateMap transs inps outs =
    Set.foldl (\m t -> case t of
        (f, mu, t) -> -- map: statid -> (inp,out,Map(sym,statid))
            if (Set.member mu inps) then Map.insertWith (mergeMaps f) f (Set.singleton mu, Set.empty,Map.singleton mu t) m
            else if (Set.member mu outs) then Map.insertWith (mergeMaps f) f (Set.empty,Set.singleton mu,Map.singleton mu t) m
            else error ("Channel " ++ (show mu) ++ " neither input nor output!") -- ++ (show (f, mu, t)))
                                       ) Map.empty transs

mergeMaps :: (Ord b, Show a, Show b) => a -> (Set b, Set b, Map b a) -> (Set b, Set b, Map b a) -> (Set b, Set b, Map b a)
mergeMaps f (ni,no,nm) (oi,oo,om) =
    let (c,s) = head $ Map.toList nm in
    case (Map.lookup c om) of
        Nothing -> (Set.union ni oi, Set.union no oo,Map.insert c s om)
        Just d -> error ("stautdef nondeterministic!\n" ++ (show f) ++ " -> " ++ (show c) ++ " -> " ++ (show d) ++ " AND " ++ (show f) ++ " -> " ++ (show c) ++ " -> " ++ (show s))

printCompRel :: (Show a, Eq a) => Set (State a b,State a b) -> String
printCompRel compRel = List.intercalate "\n" (Set.toList $ Set.map (\t -> "(s" ++ (show $ sid $ fst t) ++ ", s" ++ (show $ sid $ snd t) ++ ")") (Set.filter (\t -> fst t /= snd t) compRel))

getDistingCompPairs :: (Ord a, Ord b) => Aut a b -> Set (State a b,State a b) -> [b] -> Int
getDistingCompPairs aut comp sigma =
    List.length [(q1,q2) | (q1,q2) <- Set.toList comp,
                           case (afterSequence q1 sigma aut, afterSequence q2 sigma aut) of
                                (Just q, Nothing) -> True
                                (Nothing, Just q) -> True
                                otherwise -> False]

adgAutFromAutomaton :: (Ord a, Ord b) => StandardAutomata.ConcreteSuspAutIntrpr Det a b b -> b -> Maybe (Aut a b)
adgAutFromAutomaton aut delta = let
    stateIds = Automaton.reachable $ Automaton.syntacticAutomaton aut
    alphabet = Set.map asSuspended $ Automaton.alphabet $ Automaton.syntacticAutomaton aut
    (inputs,outputs) = Set.foldr (\l (i,o) -> if isInput l then (Set.insert l i,o) else (i,Set.insert l o)) (Set.empty,Set.singleton (Out Quiescence)) alphabet
    stateTrans = Set.map (\sid -> (sid, insertTransitions sid (insertTransitions sid Map.empty inputs aut delta) outputs aut delta)) stateIds
    (inp,out) = (Set.map (getLabel delta) inputs, Set.map (getLabel delta) outputs)
    stateMap = Map.fromList $ Set.toList $ Set.map (\(sid,trans) -> (sid, State sid (Set.intersection inp $ Set.fromList $ Map.keys trans) (Set.intersection out $ Set.fromList $ Map.keys trans) trans)) stateTrans
    in case Automaton.stateConf aut of
        Det q -> case Map.lookup q stateMap of
            Nothing -> Nothing
            Just s -> Just $ statesToAut s $ Set.fromList $ Map.elems stateMap
    where
        insertTransition :: (Ord a, Ord b) => a -> (Map b a) -> (IOSuspAct b b) -> StandardAutomata.ConcreteSuspAutIntrpr Det a b b -> b -> (Map b a)
        insertTransition sid m ioact aut delta =
            case Automaton.stateConf (Automaton.toConfiguration aut (Det sid) `Automaton.after` ioact) of
                Det q -> Map.insert (getLabel delta ioact) q m
                _ -> m
        getLabel :: Ord b => b -> IOSuspAct b b -> b
        getLabel delta ioact =  case ioact of
                             (In i) -> i
                             (Out (OutSusp o)) -> o
                             (Out Quiescence) -> delta
        insertTransitions :: (Ord a, Ord b) => a -> Map b a -> Set (IOSuspAct b b) -> StandardAutomata.ConcreteSuspAutIntrpr Det a b b -> b -> Map b a
        insertTransitions sid trans alf aut delta = Set.foldr (\l m -> insertTransition sid m l aut delta) trans alf