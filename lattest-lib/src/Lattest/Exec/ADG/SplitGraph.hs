{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE  DefaultSignatures #-}

module Lattest.Exec.ADG.SplitGraph(SplitGraph,SplitNode,buildSplitGraph,show,getLCA,getLCAgreedy,getAllLCAsTopDown,evidence,injectiveSet,injectiveSetWithInfo,Evidence(..),size,
                    isUnsplittable,depth,initializeSplitGraphAdmin,SplitGraphAdmin,splitGraphAdminToString,getNodeSizeCount,getRootNode,getMaxInjective,
                    evidenceInjectiveForStates, getObservations, getWeight) where

import Data.Set as Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map as Map (Map, (!))
import qualified Data.Maybe as Maybe
import qualified Data.List as List
import qualified Data.Foldable as Foldable
import qualified Control.Parallel.Strategies as ParallelS
import qualified Control.Parallel as Parallel

import qualified Lattest.Exec.ADG.Aut as Aut
import Lattest.Exec.ADG.Aut as Aut (Aut, State)

data SplitNode a b = SplitNode {nodeStates :: (Set (State a b)), children :: Set (Set (State a b)), evidence :: Maybe (Evidence b)} -- , isInjective :: Maybe Bool} --, splittedStates :: Maybe (Set SuspState)
    deriving (Eq,Ord)

instance (Ord a, Ord b, Show a, Show b) => Show (SplitNode a b) where
    show (SplitNode s c e) = "node: " ++ (show $ Set.toList $  Set.map  (Aut.sid) s) ++ ", " ++
                               "children: " ++ (show $ Set.toList $  Set.map (\n -> Set.toList $ Set.map  (Aut.sid) n) c) ++ ", " ++
                               "evidence: " ++ (case e of Nothing -> "No evidence"; Just ev -> show ev)

data SplitGraph a b = SplitGraph {root :: (Set (State a b)), nodeMap :: Map (Set (State a b)) (SplitNode a b)} --, lcaMap :: Map (Set SuspState) (Set SplitNode)

instance (Ord a, Ord b, Show a, Show b) => Show (SplitGraph a b) where
    show (SplitGraph r map) = Map.foldr (\s str -> str ++ (show s) ++ "\n\n") "" map

data Evidence b = Nil | Prefix b (Evidence b) | Plus [Evidence b]
    deriving (Eq,Ord)

instance (Show b) => Show (Evidence b) where
    show Nil = "Nil"
    show (Prefix mu (Plus ev)) = (show mu) ++ ".(" ++ (show (Plus ev)) ++ ")"
    show (Prefix mu ev) = (show mu) ++ "." ++ (show ev)
    show (Plus []) = "empty evidence error"
    show (Plus (x:[])) = (show x)
    show (Plus (x:xs)) = (show (Plus [x])) ++ " + " ++ (show (Plus xs))

depth :: (Ord b) => Evidence b -> Int
depth Nil = 0
depth (Prefix mu ev) = 1 + (depth ev)
depth (Plus evs) = if evs == [] then error "empty!" else maximum (List.map depth evs)

getObservations :: (Ord b) => Evidence b -> Set [b]
getObservations Nil = Set.singleton []
getObservations (Prefix mu ev) = Set.fromList [ mu : sigma | sigma <- Set.toList $ getObservations ev ]
getObservations (Plus evs) = Set.unions $ List.map getObservations evs

getWeight :: (Ord a, Ord b, Show b) => [b] -> Evidence b -> Set (State a b) -> Aut a b -> Int
getWeight [] _ _ _ = 1
getWeight (mu : sigma) (Prefix nu ev) states aut = if mu == nu then getWeight sigma ev (Aut.afterSet states mu aut) aut else error $ "Prefix: observation not matching evidence: " ++ (show mu) ++ " " ++ (show nu)
getWeight (mu : sigma) (Plus evs) states aut =
     case List.find (\ev -> case ev of (Prefix nu _) -> nu == mu) evs of
        Just (Prefix _ nuev) -> (getWeight sigma nuev (Aut.afterSet states mu aut) aut) * (List.length [ev | ev <- evs, case ev of (Prefix nu _) -> Set.member nu (Aut.outSet states) ; otherwise -> False])
        Nothing -> error $ "Plus: observation not matching evidence: " ++ (show mu) ++ " " ++ (show evs)

getNodeSizeCount :: (SplitGraph a b) -> Map Int Int
getNodeSizeCount (SplitGraph _ nodeMap) =
    List.foldr (\count map -> case Map.lookup count map of
                              Just v -> Map.insert count (v+1) map
                              Nothing -> Map.insert count 1 map)
        Map.empty (List.map Set.size (Map.keys nodeMap))

size :: (Ord a, Ord b) => (SplitGraph a b) -> Int
size graph = Map.size $ nodeMap graph

getRootNode :: (Ord a, Ord b) => (SplitGraph a b) -> (SplitNode a b)
getRootNode graph = nodeMap graph ! root graph

data SplitGraphAdmin = SplitGraphAdmin {doBestSplit :: Bool, splitOutputFirst :: Bool, addInputStates :: Bool, outputSplit :: Int, inputSplit :: Int}

initializeSplitGraphAdmin :: Bool -> Bool -> Bool -> SplitGraphAdmin
initializeSplitGraphAdmin bests ofirst addinp = SplitGraphAdmin bests ofirst addinp 0 0

splitGraphAdminToString :: SplitGraphAdmin -> String
splitGraphAdminToString (SplitGraphAdmin dobest ofirst addinp os is) =
    "doBestSplit: " ++ (show dobest) ++
    "\nsplitOutputFirst: " ++ (show ofirst) ++
    "\naddInputStates: " ++ (show addinp) ++
    "\noutputSplit: " ++ (show os) ++
    "\ninputSplit: " ++ (show is) ++ "\n"

isUnsplittable :: (Ord a, Ord b) => Set (State a b) -> Set ((State a b),(State a b)) -> Bool
isUnsplittable stateSet compRel = Set.isSubsetOf (Set.fromList [(q,q') | q <- Set.toList stateSet, q' <- Set.toList stateSet]) compRel

isLeaf :: (SplitNode a b) -> Bool
isLeaf node = Set.null $ children node

isNonLeaf :: (SplitNode a b) -> Bool
isNonLeaf n = not $ isLeaf n

getInducedSplit :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> b -> (SplitNode a b) -> Set (Set (State a b))
getInducedSplit aut stateSet mu node = let ind = (Set.fromList [Set.fromList [ q | q <- Set.toList stateSet,
                                                                                    case Aut.after q mu aut of
                                                                                        Nothing -> False
                                                                                        (Just s) -> Set.member s c ] | c <- Set.toList (children node)])
                                        in (Set.delete Set.empty ind)

injective :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> Set (State a b,State a b) -> b -> Bool
injective aut stateSet compRel mu = and [ ((Set.member mu $ Aut.outputs aut) && ((Set.notMember mu $ Set.intersection (Aut.out q) (Aut.out q'))))
                                        ||
                                         ((Set.member mu (Set.intersection (Aut.enab q) (Aut.enab q')))
                                         && (Set.notMember (Maybe.fromJust $ Aut.after q mu aut, Maybe.fromJust $ Aut.after q' mu aut) compRel))
                                         | (q,q') <- Set.toList $ (Set.fromList [(q,q') | q <- Set.toList stateSet, q' <- Set.toList stateSet]) Set.\\ compRel]

injectiveSet :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> Set ((State a b),(State a b)) -> (Set b) -> Bool
injectiveSet aut stateSet compRel chanSet =
    pfold (&&) [injective aut stateSet compRel c | c <- Set.toList chanSet]

injectiveSetWithInfo :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> Set (State a b,State a b) -> (Set b) -> (Bool,Set (Set (State a b)))
injectiveSetWithInfo aut stateSet compRel chanSet =
    let boolchans = Set.map (\chan -> (injective aut stateSet compRel chan,chan)) chanSet
        (b,chans) = Set.foldr (\(b,c) (bs,cs) -> (b && bs,if b then cs else Set.insert c cs)) (True,Set.empty) boolchans
    in if b then (b,Set.empty) else (b, Set.fromList [qs  | c <- Set.toList chans, q <- Set.toList stateSet, q' <- Set.toList stateSet,
                                                            let qs = Set.insert q $ Set.singleton q', not $ injective aut qs compRel c])

getMaxInjective :: (Ord a, Ord b) => Aut a b -> Set (State a b) -> Set (State a b, State a b) -> (t a b -> SplitNode a b) -> Set (t a b) -> t a b
getMaxInjective aut stateSet compRel getNode lcas =
     getMaxInjectiveAbstract (\n -> evidenceInjectiveForStates aut (Maybe.fromJust $ evidence n) stateSet compRel)
                            getNode
                            lcas

getMaxInjectiveAbstract :: (Ord a, Ord b) => ((SplitNode a b) -> (Bool,Set (Set (State a b)))) -> ((t a b) -> SplitNode a b) -> Set (t a b) -> (t a b)
getMaxInjectiveAbstract f getNode nodes =
    let res = [(n,f (getNode n)) | n <- Set.toList nodes]
    in if Set.null nodes
       then error ("no LCAs!")
       else
            case Foldable.find (fst . snd) res of
                Just (n,_) -> n
                Nothing -> fst $ List.foldr (\el (best,bestNr) -> let (n,nr) = getNr el in if nr < bestNr then (n,nr) else (best,bestNr)) (getNr $ head res) (tail res)
              where getNr (n,(b,s)) = (n,Set.size s)

evidenceInjectiveForStates :: (Ord a, Ord b) => (Aut a b) -> Evidence b -> Set (State a b) -> Set ((State a b),(State a b)) -> (Bool,Set (Set (State a b)))
evidenceInjectiveForStates aut ev stateSet compRel =
    case ev of
        Nil -> (True, Set.empty)
        Prefix mu evc ->
            let (stateSetInjective,nonInjectiveStates) = injectiveSetWithInfo aut stateSet compRel (Set.singleton mu)
                (afterStatesInjective, nonInjectiveAfterStates) = evidenceInjectiveForStates aut evc (Aut.afterSet stateSet mu aut) compRel
                nonInjectiveBeforeAfterStates = Set.fromList [qs | q <- Set.toList stateSet, q' <- Set.toList stateSet, q /= q', let qs = Set.insert q $ Set.singleton q',
                                                                   Set.member (Aut.afterSet qs mu aut) nonInjectiveAfterStates ]
            in (stateSetInjective && afterStatesInjective,  Set.union nonInjectiveStates nonInjectiveBeforeAfterStates)
        Plus evs -> List.foldr (\(b,s) (bt,st) -> (b && bt,Set.union s st)) (True,Set.empty) [evidenceInjectiveForStates aut evc stateSet compRel | evc <- evs]

getLCAgreedy :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> Set (SplitNode a b)
getLCAgreedy graph states =
    case getLCAgreedyStep graph states (getRootNode graph) of
        Nothing -> Set.empty
        Just n -> Set.singleton n

getLCAgreedyStep :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> (SplitNode a b) -> Maybe (SplitNode a b)
getLCAgreedyStep graph states node =
    if isLeaf node then -- Trace.trace ("leaf node lca: " ++ (show node) ++
                           -- (case evidence node of Just (Prefix mu ev) -> " after " ++ mu ++ "= " ++ (show $ Set.map (\s -> Map.lookup mu $ Aut.trans s) (nodeStates node)); _ -> ""))
                            Nothing
    else let cont = Set.filter (\ch -> Set.isSubsetOf states ch) (children node)
         in if Set.null cont then Just node
            else case Foldable.find (\m -> case m of Nothing -> False; Just a -> True) $
                                    (let todoList = (List.map (\ch -> (getLCAgreedyStep graph states) (nodeMap graph ! ch)) (Set.toList cont))
                                      in todoList `ParallelS.using` ParallelS.parList ParallelS.rseq) of
                Nothing -> Nothing
                Just a -> a

getAllLCAsTopDown :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> Set (SplitNode a b)
getAllLCAsTopDown graph states = getAllLCAs graph states (getRootNode graph)

getAllLCAs :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> (SplitNode a b) -> Set (SplitNode a b)
getAllLCAs graph states node =
    if isLeaf node then Set.empty
    else let cont = Set.filter (\ch -> Set.isSubsetOf states ch) (children node)
         in if Set.null cont then Set.singleton node
            else List.foldl  Set.union
                            Set.empty
                            (let todoList = List.map (\ch -> getAllLCAs graph states ((nodeMap graph) ! ch)) (Set.toList cont)
                             in todoList `ParallelS.using` ParallelS.parList ParallelS.rpar)

isLCA :: (Ord a, Ord b) => (SplitNode a b) -> Set (State a b) -> Bool
isLCA node lcaStates =
    (isNonLeaf node)
    && (Set.isSubsetOf lcaStates (nodeStates node))
    && (all (\ch -> not $ Set.isSubsetOf lcaStates ch) (children node))

getLCA :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> Set (SplitNode a b)
getLCA g@(SplitGraph r map) lcaStates =  let (lca,_,_) = getLCA' g (Maybe.fromMaybe (error "root node lookup") $ Map.lookup r map) lcaStates Map.empty in lca

-- getLCA' splitgraph needlcsforthesestates currentnode visitedsplitnodes -> foundlcas foundcandidate visitedsplitnodes
getLCA' :: (Ord a, Ord b) => (SplitGraph a b) -> (SplitNode a b) -> Set (State a b) -> Map (SplitNode a b) Bool -> (Set (SplitNode a b), Bool,Map (SplitNode a b) Bool)
getLCA' g currentNode lcaStates visited =
    case Map.lookup currentNode visited of
        Just b -> (Set.empty,b,visited)
        Nothing ->
         if isLeaf currentNode
         then if any (flip Set.member lcaStates) (nodeStates currentNode)
              then (Set.empty, True, Map.insert currentNode True visited)
              else(Set.empty, False, Map.insert currentNode False visited)
         else let childNodes = (Set.map (\childstates -> Maybe.fromMaybe (error ("child node lookup: ")) $ Map.lookup childstates (nodeMap g)) (children currentNode)) -- :: Set (SplitNode a)
                  (totalFound,childrenFoundLCA,totalVisited) = parallelLCAsearch g lcaStates childNodes visited
              in if childrenFoundLCA
                 then if isLCA currentNode lcaStates -- done
                      then (Set.insert currentNode totalFound,True,Map.insert currentNode True totalVisited)
                      else (totalFound,True, Map.insert currentNode True totalVisited)
                 else (totalFound,False,Map.insert currentNode False totalVisited)

parallelLCAsearch :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> Set (SplitNode a b) -> Map (SplitNode a b) Bool -> (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool)
parallelLCAsearch g lcaStates childNodes visited = pfold mergeLCAsearchResult [ getLCA' g child lcaStates visited | child <- Set.toList childNodes]

linearLCAsearch :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> Set (SplitNode a b) -> Map (SplitNode a b) Bool -> (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool)
linearLCAsearch g lcaStates childNodes visited = Set.fold (processChildForLCAsearch g lcaStates) (Set.empty,False,visited) childNodes

processChildForLCAsearch :: (Ord a, Ord b) => (SplitGraph a b) -> Set (State a b) -> (SplitNode a b) -> (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool) -> (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool)
processChildForLCAsearch g lcaStates child (totalFound,otherChildrenFoundLCA,totalVisited) =
    mergeLCAsearchResult (totalFound,otherChildrenFoundLCA,totalVisited) (getLCA' g child lcaStates totalVisited)

mergeLCAsearchResult :: (Ord a, Ord b) => (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool) -> (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool) -> (Set (SplitNode a b), Bool, Map (SplitNode a b) Bool)
mergeLCAsearchResult (a1,b1,c1) (a2,b2,c2) = (Set.union a1 a2, b1 || b2, Map.union c1 c2)

makeRoot :: (Aut a b) -> (SplitGraph a b)
makeRoot aut = SplitGraph (Aut.states aut) (Map.singleton (Aut.states aut) (SplitNode (Aut.states aut) Set.empty Nothing)) -- Nothing))

assignChildren :: (Ord a, Ord b) => (SplitGraph a b) -> (SplitNode a b) -> (Set (Set (State a b))) -> Evidence b -> (SplitGraph a b)
assignChildren (SplitGraph r nodeMap) oldNode@(SplitNode states _ _ ) newChildren evidence
    = if (isLeaf oldNode)
        then let newNode = SplitNode states newChildren (Just evidence)
                 childNodes = Set.map (\ch -> case Map.lookup ch nodeMap of Nothing -> SplitNode ch Set.empty Nothing ; Just n -> n) newChildren
                 newNodeMap = Map.insert states newNode (Set.foldr (\ch map -> Map.insert (nodeStates ch) ch map) nodeMap childNodes)
               in  -- Trace.trace ("splitted: " ++ (show newNode))
                    (SplitGraph r newNodeMap)
        else error ("Cannot assign child nodes to non-leaf node!")

buildSplitGraph :: (Ord a, Ord b) => (Aut a b) -> Set ((State a b),(State a b)) -> SplitGraphAdmin -> ((SplitGraph a b), SplitGraphAdmin)
buildSplitGraph aut compRel admin =
    let g = makeRoot aut
    in if Set.size compRel == (Set.size $ Aut.states aut) * (Set.size $ Aut.states aut) then (g,admin) -- all states of automaton are compatible
       else buildSplitGraphSimple aut g (Set.singleton $ nodeMap g ! root g) Set.empty compRel admin

buildSplitGraphSimple :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> Set (SplitNode a b) -> Set (SplitNode a b) -> Set ((State a b),(State a b)) -> SplitGraphAdmin -> ((SplitGraph a b), SplitGraphAdmin)
buildSplitGraphSimple aut graph todo notSplitYet compRel admin =
    if (Set.null todo) && (Set.null notSplitYet) then (graph, admin)
    else if Set.null todo then buildSplitGraphSimple aut graph notSplitYet Set.empty compRel admin
    else let node = Set.elemAt 0 todo
         in -- Trace.trace ("todo: " ++ (show $ Set.map (\n -> show $ Set.map Aut.sid (nodeStates n) ) todo)
            --                ++ " notSplitYet: " ++ (show $ Set.map (\n -> show $ Set.map Aut.sid (nodeStates n) ) notSplitYet)) $
            -- Trace.trace ("todo: " ++ (show $ Set.size todo) ++ " notSplitYet: " ++ (show $ Set.size notSplitYet)) $
            case splitNode aut graph node compRel admin of
                (Nothing,_) -> -- Trace.trace("skipping " ++ (show $ Set.map Aut.sid $ nodeStates node))
                            buildSplitGraphSimple aut graph (Set.delete node todo) (Set.insert node notSplitYet) compRel admin
                (Just newGraph,nadmin) -> buildSplitGraphSimple aut newGraph (Set.foldr (\ch todoset ->
                                                                                 let newNode = nodeMap newGraph ! ch
                                                                                 in if isUnsplittable ch compRel
                                                                                        || Set.member newNode notSplitYet
                                                                                        || (Map.member ch (nodeMap graph))
                                                                                    then todoset
                                                                                    else Set.insert newNode todoset)
                                                                               (Set.delete node todo)
                                                                               (children $ (nodeMap newGraph) ! nodeStates node)) notSplitYet compRel nadmin

splitNode :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> (SplitNode a b) -> Set ((State a b),(State a b)) -> SplitGraphAdmin -> (Maybe (SplitGraph a b),SplitGraphAdmin)
splitNode aut graph node compRel admin =
    let  outputSplitRes = getSplitOnOutputTransition aut graph node compRel (doBestSplit admin)
         inputSplitRes = getSplitOnInputTransition aut graph node compRel (doBestSplit admin) (addInputStates admin)
    in case (outputSplitRes,inputSplitRes) of
        (Nothing,Nothing) -> (Nothing, admin)
        (Nothing,Just (ci,ei)) -> (Just (assignChildren graph node ci ei), admin{inputSplit = (inputSplit admin) + 1}) -- ii)
        (Just (co,eo),Nothing) -> (Just (assignChildren graph node co eo), admin{outputSplit = (outputSplit admin) + 1}) -- io)
        (Just (co,eo),Just (ci,ei)) -> if (splitOutputFirst admin)
                                       then (Just (assignChildren graph node co eo), admin{outputSplit = (outputSplit admin) + 1})
                                       else (Just (assignChildren graph node ci ei), admin{inputSplit = (inputSplit admin) + 1})

outputCondition :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> (SplitNode a b) -> Set ((State a b),(State a b)) -> Maybe (Map b (Set (SplitNode a b)))
outputCondition aut graph node compRel =
    let states = (nodeStates node)
        (bools,map) = getSymbolSplitNodeMap aut graph node (Aut.outSet states) (\x -> any (\q -> Set.notMember x (Aut.out q)) states)
    in if and bools then Just map else Nothing

getSymbolSplitNodeMap :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> (SplitNode a b) -> Set b -> (b -> Bool) -> ([Bool], Map b (Set (SplitNode a b)))
getSymbolSplitNodeMap aut graph node symbols isTrivial =
    Set.foldr (\mu res -> -- Trace.trace ("looking at symbol: " ++ mu) $
        if isTrivial mu
        then (True:(fst res), Map.insert mu Set.empty (snd res))
        else let lcaNodes = getLCAgreedy graph $ Aut.afterSet (nodeStates node) mu aut
             in -- Trace.trace ("found lca for " ++ mu ++ ": " ++ (show $ Set.map (\n -> Set.map Aut.sid $ nodeStates n) lcaNodes))
                (if Set.null lcaNodes
                 then (False:(fst res), (snd res))
                 else (True:(fst res), Map.insert mu lcaNodes (snd res)))) ([],Map.empty) symbols

selectSplitNodeForLabel :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> Set (State a b, State a b) -> Map b (Set (SplitNode a b)) -> Bool -> Map b (Maybe (SplitNode a b))
selectSplitNodeForLabel aut stateSet compRel spMap doBestSplit =
    Map.foldrWithKey (\mu splitNodes selMap -> if Set.null splitNodes -- if isTrivial mu in getSymbolSplitNodeMap
                                               then Map.insert mu Nothing selMap
                                               else if doBestSplit
                                                    then Map.insert mu (Just (getBestSplitNode aut stateSet compRel id splitNodes)) selMap -- node with smallest largest child\
                                                    else Map.insert mu (Just (getFirstSplitNode splitNodes)) selMap)
                                           Map.empty spMap

getBestSplitNode :: (Ord a, Ord b) => (Aut a b) -> Set (State a b) -> Set (State a b, State a b) -> (t a b -> SplitNode a b) -> Set (t a b) -> (t a b)
getBestSplitNode aut stateSet compRel getNode splitNodes =
    if Set.null splitNodes then error "cannot select best of zero items"
    else getMaxInjective aut stateSet compRel getNode splitNodes -- Foldable.minimumBy (comparing (\node -> Foldable.maximumBy (comparing Set.size) $ children node)) splitNodes

getFirstSplitNode :: Set (t a b) -> (t a b)
getFirstSplitNode splitNodes =
    if Set.null splitNodes then error "cannot select best of zero items"
    else Set.elemAt 0 splitNodes
                                    --                           Just children evidence isInjective | Nothing=no split
getSplitOnOutputTransition :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> (SplitNode a b) -> Set ((State a b),(State a b)) -> Bool -> Maybe ((Set (Set (State a b))), Evidence b)
getSplitOnOutputTransition aut graph node compRel doBestSplit =
    case outputCondition aut graph node compRel of
     Nothing -> Nothing
     Just spMap -> Just (Map.foldrWithKey (\mu bestSplitNode (children, ev) ->
                                                let (xChildren,xEvidence) = getChildsEvForSplitNode aut node mu bestSplitNode
                                                  in (Set.union children xChildren,
                                                     (case ev of
                                                            Nil -> xEvidence
                                                            Plus bexps -> Plus (xEvidence:bexps)
                                                            Prefix _ _ -> Plus [xEvidence,ev])))
                                                    (Set.empty,Nil)
                                                    (selectSplitNodeForLabel aut (nodeStates node) compRel spMap doBestSplit))

inputCondition :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> (SplitNode a b) -> Set ((State a b),(State a b)) -> Maybe (Map b (Set (SplitNode a b)))
inputCondition aut graph node compRel = let (bools,map) = getSymbolSplitNodeMap aut graph node
                                                                    (Aut.inSet (nodeStates node))
                                                                    (const False)
                                       in if or bools then Just map else Nothing

getChildsEvForSplitNode :: (Ord a, Ord b) => (Aut a b) -> (SplitNode a b) -> b -> Maybe (SplitNode a b) -> ((Set (Set (State a b))), Evidence b)
getChildsEvForSplitNode aut node mu maybesplitNode =
    case maybesplitNode of
        Nothing -> (Set.singleton (Set.filter (\s -> Set.member mu (Aut.out s)) (nodeStates node)), Prefix mu Nil)
        Just splitNode -> (getInducedSplit aut (nodeStates node) mu splitNode, Prefix mu (Maybe.fromMaybe (error "evidence") (evidence splitNode)))

addNonEnabledStatesToChildren :: (Ord a, Ord b) => Set (Set (State a b)) -> Set (State a b) -> b -> Set (Set (State a b))
addNonEnabledStatesToChildren indsplit states input =
    let nonEnabledStates = Set.filter (\s -> Set.notMember input (Aut.inp s)) states
    in Set.map (\c -> Set.union c nonEnabledStates) indsplit

data ATup a b = ATup b (Maybe (SplitNode a b)) deriving (Eq,Ord)

getSplitOnInputTransition :: (Ord a, Ord b) => (Aut a b) -> (SplitGraph a b) -> SplitNode a b -> Set ((State a b),(State a b))
                                                        -> Bool -> Bool -> Maybe (Set (Set (State a b)), Evidence b)
getSplitOnInputTransition aut graph node compRel doBestSplit addInputStates =
    case inputCondition aut graph node compRel of
        Nothing -> Nothing
        Just spMap ->  let splitNodePerLabel = Set.fromList $ List.map (\(a,b) -> ATup a b) $
                                               Map.toList (selectSplitNodeForLabel aut (nodeStates node) compRel spMap doBestSplit)
                           (ATup a (Just bestNode)) = if doBestSplit
                                                      then getBestSplitNode aut (nodeStates node) compRel (\(ATup a (Just n)) -> n) splitNodePerLabel
                                                      else getFirstSplitNode splitNodePerLabel
                           (indsplit, ev) = getChildsEvForSplitNode aut node a (Just bestNode)
                       in if Set.null indsplit then error $ "no children for node" ++ -- (show node) ++
                                "with after set .." ++ -- (show $ Set.map Aut.sid $ Aut.afterSet (nodeStates node) a aut) ++
                                " using splitter: .." -- ++ (show bestNode)
                          else if addInputStates
                               then Just (addNonEnabledStatesToChildren indsplit (nodeStates node) a, ev)
                               else Just (indsplit, ev)

pfold :: (a -> a -> a) -> [a] -> a
pfold _ [x] = x
pfold mappend xs  = Parallel.pseq (Parallel.par ys zs) (ys `mappend` zs) where
  len = length xs
  (ys', zs') = splitAt (len `div` 2) xs
  ys = pfold mappend ys'
  zs = pfold mappend zs'