module Lattest.Exec.ADG.DistGraphConstruction (getAutomaton,getDistGraph,readSerializedFile,computeAdaptiveDistGraphPure) where

import qualified Data.List   as List
import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Serialize
import qualified Data.ByteString as ByteString
import Control.DeepSeq as DeepSeq

import qualified Lattest.Exec.ADG.DistGraph as DistGraph
import qualified Lattest.Exec.ADG.SplitGraph as SplitGraph
import Lattest.Exec.ADG.SplitGraph as SplitGraph (SplitGraph, Evidence)
import qualified Lattest.Exec.ADG.Aut as Aut
import Lattest.Exec.ADG.Aut as Aut (Aut, State)

readSerializedFile :: (Serialize a) => String -> String -> IO a
readSerializedFile fileStorageDir fileName = do
    b <- ByteString.readFile (fileStorageDir ++ fileName ++ ".serialized")
    case runGet get b of
                Left s -> error s
                Right a -> return a

saveSerializedFile :: (Serialize a,NFData a) => String -> String -> a -> IO ()
saveSerializedFile fileStorageDir fileName obj = do
    ByteString.writeFile (fileStorageDir ++ fileName ++ ".serialized") (runPut $ put $ force obj)
    -- putStrLn $ "Stored file for " ++ fileName

readAndStoreAutomaton :: (Ord a, Ord b, Serialize a, Serialize b, NFData a, NFData b) => String -> String -> String -> String -> (String -> String -> IO (Aut a b)) -> IO (Aut a b)
readAndStoreAutomaton fileReadDir readFileName fileStorageDir storeName readAut = do
    aut <- readAut fileReadDir readFileName
--    writeFile (fileStorageDir ++ "stautDef" ++ storeName ++ ".txs") (AutomataDot.toStautDefString aut)
    saveSerializedFile fileStorageDir ("Automaton" ++ storeName) aut
    return aut

getAutomaton :: (Ord a, Ord b, Serialize a, Serialize b, NFData a, NFData b) => String -> String -> String -> String -> (String -> String -> IO (Aut a b)) -> Bool -> IO (Aut a b)
getAutomaton fileReadDir readName fileStorageDir storeName readAut isStored =
    if isStored then readSerializedFile fileStorageDir $ "Automaton" ++ storeName
    else readAndStoreAutomaton fileReadDir readName fileStorageDir storeName readAut

computeSplitGraph :: (Ord a, Ord b, Show a, Show b, Serialize a, Serialize b, NFData a, NFData b) => String -> String ->  (Aut a b) -> Set ((State a b),(State a b)) -> SplitGraph.SplitGraphAdmin -> IO (SplitGraph a b)
computeSplitGraph fileStorageDir storeName aut compRel admin = do
    let (graph,nadmin) = SplitGraph.buildSplitGraph aut compRel admin
    saveSerializedFile fileStorageDir ("SpitGraph" ++ storeName) graph
    writeFile (fileStorageDir ++ "Stats" ++ storeName ++ ".txt") (SplitGraph.splitGraphAdminToString nadmin ++ "\nSize split graph: " ++ (show $ SplitGraph.size graph))
    return graph

getDistGraph :: (Ord a, Ord b, Show a, Show b, Serialize a, Serialize b, NFData a, NFData b) => String -> String ->  (Aut a b) -> Bool -> Bool -> Bool -> Bool -> Bool -> Set (State a b) -> IO (Evidence b,Set (Set (State a b)),SplitGraph a b, Set (State a b, State a b))
getDistGraph fileStorageDir storeName aut graphStored compRelIsStored adgIsStored doBestSplit splitOutputFirst dgStates = do
    compRel <- if compRelIsStored
               then readSerializedFile fileStorageDir $ "CompRel" ++ storeName
               else do
                let comp = Aut.computeCompRel aut
                saveSerializedFile fileStorageDir ("CompRel" ++ storeName) comp
                return comp
    (adg,nonInj,graph) <- if adgIsStored && graphStored
                   then do
                        (adg,ni) <- readSerializedFile fileStorageDir $ "ADG" ++ storeName
                        graph <- readSerializedFile fileStorageDir $ "SpitGraph" ++ storeName
                        return (adg,ni,graph)
                   else do
                       graph <-  if graphStored
                                 then readSerializedFile fileStorageDir $ "SpitGraph" ++ storeName
                                 else computeSplitGraph fileStorageDir storeName aut compRel (SplitGraph.initializeSplitGraphAdmin doBestSplit splitOutputFirst True)
                       (dg,nj) <- computeAdaptiveDistGraph aut graph compRel fileStorageDir storeName dgStates True
                       return (dg,nj,graph)
    return (adg,nonInj,graph,compRel)

computeAdaptiveDistGraph :: (Ord a, Ord b, Show a, Show b, Serialize a, Serialize b, NFData a, NFData b) => (Aut a b) -> (SplitGraph a b) -> Set ((State a b),(State a b)) -> String -> String -> Set (State a b) -> Bool -> IO (Evidence b, Set (Set (State a b)))
computeAdaptiveDistGraph aut graph compRel fileStorageDir storeName dgStates useBucketLCA = do
    let dg = DistGraph.buildDistGraph aut graph dgStates compRel useBucketLCA
    let (b,nonInjective) = SplitGraph.evidenceInjectiveForStates aut dg dgStates compRel
    -- putStrLn $ show $ Set.map (Set.map Aut.sid) nonInjective
    saveSerializedFile fileStorageDir ("ADG" ++ storeName) (dg,nonInjective)
    return (dg, nonInjective)

computeAdaptiveDistGraphPure :: (Ord a, Ord b, NFData a, NFData b) => Aut a b -> Bool -> Bool -> Bool -> Evidence b
computeAdaptiveDistGraphPure aut doBestSplit splitOutputFirst useBucketLCA = let
    compRel = Aut.computeCompRel aut
    (splitGraph,nadmin) = SplitGraph.buildSplitGraph aut compRel (SplitGraph.initializeSplitGraphAdmin doBestSplit splitOutputFirst True)
    in DistGraph.buildDistGraph aut splitGraph (Aut.states aut) compRel useBucketLCA