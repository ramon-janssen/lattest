{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
module Lattest.Exec.ADG.SuspAut(SuspAut,SuspState,stautToSusp,show,printCompRel) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Map as Map (Map)
import qualified Data.Map as Map
import qualified Data.Foldable as Foldable
import qualified Data.List as List

import qualified Lattest.Exec.ADG.Aut as Aut

type SuspAut = Aut.Aut Int String

type SuspState = Aut.State Int String

instance Show SuspAut where
    show (Aut.Aut _ s _ _ _) = List.concat $ List.map show $ Set.toList s

instance Show SuspState where
    show (Aut.State s inps outs t) = transToString s t
                                   {- show (s,
                                   (Set.toList inps),
                                   (Set.toList outs),
                                   (Map.toList t)) -}

tupleStateSetToString :: Set (SuspState,SuspState) -> String
tupleStateSetToString set = show $ Set.map (\t -> (Aut.sid $ fst t, Aut.sid $ snd t)) set

transToString :: Int -> Map String Int -> String
transToString s map = List.concat $ List.map (\(mu,d) -> (show s) ++ " " ++ mu ++ " " ++ (show d) ++ "\n") (Map.toList map)

stautToSusp :: (Int, Set (Int,String,Int), Set String, Set String) -> SuspAut
stautToSusp (initial, transs, inps, outs) =
    let statemap = stautToStateMap transs inps outs
         in case Foldable.find (\tup -> case tup of (_,o,_) -> Set.null o) statemap of
               Just v -> error ("Automaton is blocking! " ++ (show v))
               Nothing -> case Map.lookup initial statemap of
                            Nothing -> error ("Initial state does not have any transitions")
                            Just (ini,outi,tmapi) ->
                                let statesandmap = getStatesAndMap statemap
                                 in Aut.Aut (Aut.State initial ini outi tmapi) (fst statesandmap) (snd statesandmap) inps outs

getStatesAndMap :: Map Int (Set String, Set String, Map String Int) -> (Set SuspState, Map Int SuspState)
getStatesAndMap statemap = (Map.foldlWithKey (\setandmap key val -> case val of
                                                                       (ins,outs,tmaps) ->
                                                                           let state = (Aut.State key ins outs tmaps) in
                                                                            (Set.insert state (fst setandmap), Map.insert key state (snd setandmap))) (Set.empty,Map.empty) statemap)


stautToStateMap :: Set (Int,String,Int) -> Set String -> Set String -> Map Int (Set String, Set String, Map String Int)
stautToStateMap transs inps outs = Set.foldl (\m t -> case t of (f, mu, t) -> -- map: statid -> (inp,out,Map(sym,statid))
                                                                    if (Set.member mu inps) then Map.insertWith (mergeMaps f) f (Set.singleton mu, Set.empty,Map.singleton mu t) m
                                                                        else if (Set.member mu outs) then Map.insertWith (mergeMaps f) f (Set.empty,Set.singleton mu,Map.singleton mu t) m
                                                                        else error ("Channel " ++ mu ++ " neither input nor output!" ++ (show (f, mu, t)))
                                       ) Map.empty transs

mergeMaps :: Int -> (Set String, Set String, Map String Int) -> (Set String, Set String, Map String Int) -> (Set String, Set String, Map String Int)
mergeMaps f (ni,no,nm) (oi,oo,om) =
    let (c,s) = head $ Map.toList nm in
    case (Map.lookup c om) of
        Nothing -> (Set.union ni oi, Set.union no oo,Map.insert c s om)
        Just d -> error ("stautdef nondeterministic!\n" ++ (show f) ++ " -> " ++ c ++ " -> " ++ (show d) ++ " AND " ++ (show f) ++ " -> " ++ c ++ " -> " ++ (show s))

printCompRel :: Set (SuspState,SuspState) -> String
printCompRel compRel = List.intercalate "\n" (Set.toList $ Set.map (\t -> "(s" ++ (show $ Aut.sid $ fst t) ++ ", s" ++ (show $ Aut.sid $ snd t) ++ ")") (Set.filter (\t -> fst t /= snd t) compRel))
