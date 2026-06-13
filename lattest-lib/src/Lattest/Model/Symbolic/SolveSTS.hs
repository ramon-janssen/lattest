{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
interactsToGuard, -- FIXME maybe this doesn't need to be exposed but we want to test this
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard)
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr)
import Lattest.Model.BoundedMonad(BooleanConfiguration, asDualExpr)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.StandardAutomata(STS)
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential)
import Lattest.Model.Symbolic.Expr(substConst, Expr(..), VarModel, valuationToVarModel, sTrue, (.&&), assign, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, varsToGuard, identityVarModel, getVariables)
import Lattest.SMT.SMT(SMT)
import Lattest.Util.Utils(takeJusts, distributeFirstMaybe)

import Control.Arrow((&&&))
import Control.Exception(throw)

import Data.Foldable(toList)
import qualified Data.Map as Map
import qualified Data.List as List
import GHC.Stack(callStack)
import List.Shuffle(shuffle)
import System.Random(RandomGen)

{-|
    For the given STS and a subset function, using SMT solving, find a interaction of the STS in that subset for which the guard is true from the
    current STS state. The interaction is picked uniformly randomly among interactions with satisfied gates, if any. This uses the supplied random 
    generator and returns the new random generator state. The returned gate values for that interaction are not randomized in any way, picking values
    is left to the SMT solver.
-}
solveRandomInteraction :: (BM.OrdMonad m, BooleanConfiguration m, Ord g, Ord (m (Expr Bool)), RandomGen r) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g'') -> (SymInteract g -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    fmap (,r') $ solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (BM.OrdMonad m, BooleanConfiguration m, Ord g, Ord (m (Expr Bool))) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g'') -> (SymInteract g -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr' subsetFunction' =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr'
        in takeJusts $ fmap (distributeFirstMaybe . (subsetFunction' &&& interactToGuard intrpr')) $ alph

interactToGuard :: (BM.OrdMonad m, BooleanConfiguration m, Ord g, Ord (m (Expr Bool))) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') -> SymInteract g -> SymGuard
interactToGuard intrpr interaction = let
        aut = syntacticAutomaton intrpr
    in asDualExpr $ BM.ordJoin $ stateAndInteractToGuards aut interaction BM.<#> stateConf intrpr

stateAndInteractToGuards :: (Ord g, BM.OrdFunctor m) => STS m loc g -> SymInteract g -> IntrpState loc -> m SymGuard
stateAndInteractToGuards aut interaction (IntrpState l valuation) =
    case Map.lookup interaction (transRel aut l) of
        Nothing -> throw $ ActionOutsideAlphabet callStack
        Just mtdestloc -> BM.ordMap guardAndLocToGuard mtdestloc
    where
    guardAndLocToGuard (STSLoc (tguard,_), _) = substConst valuation tguard




{-
    FIXME replace `interactToGuard` and `stateAndInteractToGuards` by the code below entirely, since
    a 1-step lookahead is just a specific version of the n-step lookahead.
    !EXCEPT! that the code below adds "primes" (encoded as ..._0), which need to be stripped first.
-}

data PathNode loc = PathNode {
    pathDepth :: Int, -- needed for adding the right number of primes
    pathLoc :: loc,
    pathVars :: VarModel,
    pathCondition :: SymGuard
    } deriving (Eq, Ord)

interactsToGuard :: (BM.OrdMonad m, Foldable m, BooleanConfiguration m, Ord g, Ord loc, Ord (m (Expr Bool))) => AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g') -> [SymInteract g] -> SymGuard
interactsToGuard intrpr interactions = let
        aut = syntacticAutomaton intrpr
        initialNodes = BM.ordMap initializeNode $ stateConf intrpr
    in asDualExpr $ BM.ordMap pathCondition $ initialNodes BM.>># BM.ordKleisliChain (pathStep aut <$> interactions)
    where
    initializeNode (IntrpState loc vals) = 
        let initialVarModel = addVarPrimes 0 $ valuationToVarModel vals
        in PathNode {
            pathDepth = 0,
            pathLoc = loc,
            pathVars = initialVarModel,
            pathCondition = varsToGuard initialVarModel
        }
    stateVars =
        let mArbitraryState = (toList $ stateConf intrpr) List.!? 0
        in case mArbitraryState of
            Just (IntrpState _ arbitraryValuation) -> getVariables arbitraryValuation
            Nothing -> []
    pathStep :: (Ord g, Ord loc, BM.OrdFunctor m) => STS m loc g -> SymInteract g -> PathNode loc -> m (PathNode loc)
    pathStep aut interaction pathNode =
        case Map.lookup interaction (transRel aut $ pathLoc pathNode) of
            Nothing -> throw $ ActionOutsideAlphabet callStack
            Just mtdestloc -> BM.ordMap (addToPath pathNode) mtdestloc
        where
        addToPath (PathNode len _ vars pCond) (STSLoc (tguard, tassign), tloc) =
            let completeAssign = tassign `varUnion` identityVarModel stateVars 
                primedAssign = addVarPrimes (len + 1) $ addValPrimes len completeAssign
            in PathNode {
                pathDepth = len + 1,
                pathLoc = tloc,
                pathVars = vars `varUnion` primedAssign,
                pathCondition = pCond .&& varsToGuard primedAssign .&& mapExpressionVars (varToPrime len) tguard -- TODO the varsToGuard could also be done with substitution, resulting in less intermediate variables
            }
    addVarPrimes :: Int -> VarModel -> VarModel
    addVarPrimes n = mapVars $ varToPrime n
    addValPrimes :: Int -> VarModel -> VarModel
    addValPrimes n = mapVarExprs $ varToPrime n
    varToPrime :: Int -> Variable -> Variable
    varToPrime n v = v {varName = varName v ++ "_" ++ show n} -- Hack. Ideally we have a nice representation which avoids collisions, and maybe a statically typed distinction between primed and unprimed variables


