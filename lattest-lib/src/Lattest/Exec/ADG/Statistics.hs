module Lattest.Exec.ADG.Statistics (getStatistics, getAutTable, getExpTable) where

import qualified Data.Map as Map
import Data.Map as Map (Map)
import qualified Data.Set as Set
import Data.Set as Set (Set)
import Data.Maybe as Maybe
import Data.List as List

import qualified Lattest.Exec.ADG.Aut as Aut
import qualified Lattest.Exec.ADG.SplitGraph as SplitGraph
import qualified Lattest.Exec.ADG.DistGraph as DistGraph
import Lattest.Exec.ADG.SplitGraph as SplitGraph (SplitGraph, Evidence)
import Lattest.Exec.ADG.Aut as Aut (Aut, State)

getStatistics :: (Show a, Ord a, Ord b, Show b) => (Aut a b, Set (State a b, State a b), SplitGraph a b, Evidence b, Set (Set (State a b))) -> String
getStatistics res =
    case getExpStats res of
        [nrStates,nrComp,compPerc,nrGraph,depth,nrNonInj,nrInComp,inCompPerc,hist,med,avg,wavg] ->
            List.intercalate "\n"
            ["Nr of states: " ++ nrStates,
            "Distinct compatible state pairs: " ++ nrComp ++
            " (" ++ compPerc ++ ")",
            "Nr of nodes in splitting graph: " ++ nrGraph,
            "Depth of distinguishing graph: " ++ depth,
            "Distinguishing all but " ++ nrNonInj ++ " pairs out of " ++ nrInComp ++
            " (" ++ inCompPerc ++ ")",
            "Leaf size histogram (leaf size: count):",
            hist,
            "Median leaf size: " ++ med,
            "Average leaf size: " ++ avg,
            "Weighted average leaf size: " ++ wavg]

getExpTable :: (Ord a, Ord b, Show b) => String -> (Aut a b, Set (State a b, State a b), SplitGraph a b, Evidence b, Set (Set (State a b))) -> String
getExpTable specName res =
    case getExpStats res of
        [nrStates,nrComp,compPerc,nrGraph,depth,nrNonInj,nrInComp,inCompPerc,hist,med,avg,wavg] ->
            specName ++ " , " ++ (List.intercalate " , " [nrComp,compPerc,nrGraph,depth,nrNonInj,inCompPerc,avg,wavg])

getExpStats :: (Ord a, Ord b, Show b) => (Aut a b, Set (State a b, State a b), SplitGraph a b, Evidence b, Set (Set (State a b))) -> [String]
getExpStats (spec, compRel, graph, adg, nonInj) =
    let nrStates = Set.size $ Aut.states spec
        nrComp = Set.size compRel
        nrNonInj = Set.size nonInj * 2
        nrInComp = nrStates * nrStates - nrComp
        hist = Map.delete 0 $ getHistogram $ DistGraph.getStartStatesLeaves spec adg
        (med,avg) = getMedianAndAvgHistogram hist
    in [show nrStates,
    (show $ nrComp - nrStates),
    (show $ round2Dec $ 100.0 * fromIntegral (nrComp - nrStates) / (fromIntegral $ nrStates * (nrStates - 1))) ++ "%",
    (show $ SplitGraph.size graph),
    (show $ SplitGraph.depth adg),
    (show nrNonInj),
    (show nrInComp),
    (show $ round2Dec $ 100.0 * fromIntegral nrNonInj / fromIntegral nrInComp) ++ "%",
    histToString hist,
    (show $ round2Dec med),
    (show $ round2Dec avg),
    (show $ round2Dec $ getWeightedLeafSize spec adg)]

getAutTable :: String -> (b -> Bool) -> Aut a b -> String
getAutTable specName isInput spec =
    let nrstates = Set.size $ Aut.states spec :: Int
        trans = [ Map.keysSet $ Aut.trans state | state <- Set.toList $ Aut.states spec]
        nrtrans = List.sum $ map Set.size trans
        nrinp = Set.size $ Aut.inputs spec
        nrout = Set.size $ Aut.outputs spec
        nrinptrans = List.sum $ map (Set.size . (Set.filter isInput))  trans
        nrouttrans = nrtrans - nrinptrans
        results = [nrstates, nrinp, nrout, nrtrans, nrinptrans, nrouttrans]
    in specName ++ " , " ++ (List.intercalate " , " $ map show results)

getWeightedLeafSize :: (Ord a, Ord b, Show b) => Aut a b -> Evidence b -> Double
getWeightedLeafSize aut adg =
    let obs = SplitGraph.getObservations adg
        leafSize sigma = Set.size $ Set.fromList [ q | q <- Set.toList $ Aut.states aut, Maybe.isJust $ Aut.afterSequence q sigma aut]
    in sum [ 1.0 / (fromIntegral $ SplitGraph.getWeight sigma adg (Aut.states aut) aut) * (fromIntegral $ leafSize sigma)  | sigma <- Set.toList obs]

getMedianAndAvgHistogram :: Map Int Int -> (Double,Double)
getMedianAndAvgHistogram hist =
    let nrLeaves = sum $ Map.elems hist
        avg = (fromIntegral $ sum $ map (\(k,v) -> k * v) $ Map.toList hist) / (fromIntegral nrLeaves)
        histList = List.concat $ map (\(s,c) -> replicate c s) $ Map.toList hist
        half =  nrLeaves `div` 2
        med = if half * 2 == nrLeaves
              then (fromIntegral $ (histList List.!! (half-1)) + (histList List.!! (half))) /2.0
              else fromIntegral $ histList List.!! (half-1)
    in (med,avg)

getHistogram :: [Set a] -> Map Int Int
getHistogram set =
    List.foldr (\count map -> case Map.lookup count map of
                                Just v -> Map.insert count (v+1) map
                                Nothing -> Map.insert count 1 map)
        Map.empty (List.map Set.size set)

histToString :: Map Int Int -> String
histToString map =  List.intercalate "\n" $ List.map (\(s,c) -> (show s) ++ ": " ++ (show c)) $ Map.toList map

round2Dec :: Double -> Double
round2Dec d = fromIntegral (round $ d * 100.0) / 100.0

getDistGraphStats :: (Ord a, Ord b) => Aut a b -> Evidence b -> String
getDistGraphStats spec adg =
    let (evAutTreeNodes,evAutNodes,evLeaves,pevAutTreeNodes,pevAutNodes,pevLeaves) = DistGraph.getEvidenceStats spec adg
    in "Leaf size histogram (leaf size, count)\n" ++
        (histToString $ getHistogram $ DistGraph.getStartStatesLeaves spec adg) ++
        "Nr nodes in ADG: " ++ (show $ evAutNodes) ++
        "\nNr tree nodes in ADG: " ++ (show $ evAutTreeNodes) ++
        "\nNr leaves in ADG: " ++ (show $ evLeaves) ++
        "\nNr nodes in pruned ADG: " ++ (show $ pevAutNodes) ++
        "\nNr tree nodes in pruned ADG: " ++ (show $ pevAutTreeNodes) ++
        "\nNr leaves in pruned ADG: " ++ (show $ pevLeaves)
    -- writeFile (fileStorageDir ++ "DistGraphStats" ++ storeName ++ ".txt") s