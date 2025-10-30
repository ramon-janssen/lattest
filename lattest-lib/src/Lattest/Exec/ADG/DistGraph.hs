{-# LANGUAGE ViewPatterns        #-}
module Lattest.Exec.ADG.DistGraph(buildDistGraph,getPairsForState,getStartStatesLeaves,getEvidenceStats,prune,getEvTrans) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Control.Parallel.Strategies as Parallel

import qualified Lattest.Exec.ADG.SplitGraph as SplitGraph
import Lattest.Exec.ADG.SplitGraph as SplitGraph (SplitGraph, SplitNode,Evidence(..))
import qualified Lattest.Exec.ADG.Aut as Aut
import Lattest.Exec.ADG.Aut as Aut (Aut, State)


buildDistGraph :: (Ord a, Ord b, Show a, Show b, Parallel.NFData a, Parallel.NFData b) => (Aut a b) -> (SplitGraph a b) -> Set (State a b) -> Set ((State a b),(State a b)) -> Bool -> Evidence b
buildDistGraph aut graph stateSet compRel useBucketLCA =
    buildDistGraph' aut graph stateSet Nil compRel (Map.singleton (Aut.states aut) (Set.singleton $ SplitGraph.getRootNode graph)) useBucketLCA

buildDistGraph' :: (Ord a, Ord b, Show a, Show b, Parallel.NFData a, Parallel.NFData b) => (Aut a b) -> (SplitGraph a b) -> Set (State a b) -> Evidence b -> Set ((State a b),(State a b)) -> Map (Set (State a b)) (Set (SplitNode a b)) -> Bool -> Evidence b
buildDistGraph' aut graph stateSet dg compRel lcaMap useBucketLCA =
    if (SplitGraph.isUnsplittable stateSet compRel)
    then -- Trace.trace ((++) "Unsplittable: " $ show $ Set.map Aut.sid stateSet)
        dg
    else case dg of
        Nil -> let (ev,nlcaMap) = (getEvFromLCA aut graph stateSet compRel lcaMap useBucketLCA)
               in -- Trace.trace ((++) "P= " $ show $ Set.map Aut.sid stateSet) $ -- Set.size stateSet)
                  buildDistGraph' aut graph stateSet ev compRel nlcaMap useBucketLCA
        Prefix mu bexp -> -- Trace.trace (((++) "P= " $ show $ Set.map Aut.sid stateSet) ++ " mu= " ++ mu)
                            Prefix mu (buildDistGraph' aut graph (Aut.afterSet stateSet mu aut) bexp compRel lcaMap useBucketLCA)
        Plus bexps -> let todoList = (List.map (\bexp -> buildDistGraph' aut graph stateSet bexp compRel lcaMap useBucketLCA) bexps)
                          resList = todoList `Parallel.using` Parallel.parList Parallel.rdeepseq
                      in Plus resList

getEvFromLCA :: (Ord a, Ord b, Parallel.NFData a, Parallel.NFData b) => (Aut a b) -> (SplitGraph a b) -> Set (State a b) -> Set ((State a b),(State a b)) -> Map (Set (State a b)) (Set (SplitNode a b)) -> Bool -> (Evidence b, Map (Set (State a b)) (Set (SplitNode a b)))
getEvFromLCA aut graph stateSet compRel lcaMap useBucketLCA =
    let (lcas,nlcaMap) = case Map.lookup stateSet lcaMap of
                            Just lcaNodes -> (lcaNodes, lcaMap)
                            Nothing -> let lcaNodes = (if useBucketLCA then SplitGraph.getLCA else SplitGraph.getAllLCAsTopDown) graph stateSet
                                       in (lcaNodes, Map.insert stateSet lcaNodes lcaMap)
        splitnode = SplitGraph.getMaxInjective aut stateSet compRel id lcas
    in -- Trace.trace ((++) "lca= " $ show $ splitnode) $
            (Maybe.fromJust $ SplitGraph.evidence $ splitnode, nlcaMap)

getEvidenceStats :: (Ord a, Ord b) => (Aut a b) -> Evidence b -> (Int,Int,Int,Int,Int,Int)
getEvidenceStats aut adg =
    let evTrans = getEvTrans adg
        pruneEvTrans = getEvTrans $ prune aut (Aut.states aut) adg
    in (getNrTreeNodes evTrans, getNrEvAutNodes evTrans, getNrEvLeaves evTrans, getNrTreeNodes pruneEvTrans, getNrEvAutNodes pruneEvTrans, getNrEvLeaves pruneEvTrans)
    where
        getNrTreeNodes trans = 1 + List.length trans -- root plus alle states die een parent hebben
        getNrEvAutNodes trans = 1+ (Set.size $ Set.fromList [s | (s,_,_) <- trans]) -- leaf Nil + all non-leaf nodes
        getNrEvLeaves trans = List.length $ List.filter (\(_,_,ev) -> case ev of SplitGraph.Nil -> True; _ -> False) trans


prune :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> Evidence b -> Evidence b
prune aut set Nil = Nil
prune aut set (Prefix mu ev) = let nset = Aut.afterSet set mu aut in if Set.null nset then Nil else (Prefix mu (prune aut nset ev))
prune aut set (Plus evs) = let res = List.filter (\ev -> case ev of Nil -> False; _ -> True) $ List.map (prune aut set) evs
                           in if List.null res then Nil else Plus res

getEvTrans :: Evidence b -> [(Evidence b, b, Evidence b)]
getEvTrans Nil = error "Nil encountered"
getEvTrans p@(Prefix mu Nil) = [(p,mu,Nil)]
getEvTrans p@(Prefix mu ev) = (p,mu,ev) : getEvTrans ev
getEvTrans p@(Plus evs) = List.foldl (\tr ev -> case ev of
                                                    Prefix mu Nil -> (p,mu,Nil) : tr
                                                    Prefix mu ev' -> (p,mu,ev'): (getEvTrans ev') ++ tr) [] evs

getStartStatesLeaves :: (Ord a, Ord b) => (Aut a b) -> Evidence b ->  [Set (State a b)]
getStartStatesLeaves aut ev =
    let states = (Aut.states aut)
    in getStartStatesLeaves' aut ev (Set.fromList [ (s,s) | s <- Set.toList states]) states

getStartStatesLeaves' :: (Ord a, Ord b) => (Aut a b) -> Evidence b -> Set ((State a b),(State a b)) -> Set (State a b) ->  [Set (State a b)]
getStartStatesLeaves' _ Nil initcurmap leafStates = [Set.fromList [ i | (i,c) <- Set.toList initcurmap, Set.member c leafStates ]]
getStartStatesLeaves' aut (Prefix mu ev) initcurmap evStates =
    let nevStates = Aut.afterSet evStates mu aut
        ninitcurmap = Set.foldl (\set (i,c) -> case Aut.after c mu aut of
                                                Nothing -> set
                                                Just d -> Set.insert (i,d) set) Set.empty initcurmap
    in getStartStatesLeaves' aut ev ninitcurmap nevStates
getStartStatesLeaves' aut (Plus evs) initcurmap evStates =
    List.concat $ List.map (\ev -> getStartStatesLeaves' aut ev initcurmap evStates) evs

getPairsForState :: (Ord a, Ord b) => (Aut a b) -> Set((State a b),(State a b)) -> (State a b) -> Set (Set (State a b))
getPairsForState aut compRel state =
    Set.foldr (\s set -> if Set.member (s,state) compRel then set else Set.insert (Set.insert s $ Set.singleton state) set) Set.empty (Set.delete state $ Aut.states aut)