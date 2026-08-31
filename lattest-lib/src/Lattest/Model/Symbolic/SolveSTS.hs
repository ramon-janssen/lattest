{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-|
    Find concrete values to take transitions in STSes, using an SMT solver.
-}

module Lattest.Model.Symbolic.SolveSTS (
solveRandomInteraction,
interactsToSpecifiedCondition,
interactsToAllowedCondition,
seTree,
treeToGuard,
SETree(..),
SEIte(..),
offlineTests,
OfflineTests(..),
toTrace
)
where

import Lattest.Model.Alphabet(SymInteract(..), GateValue(..), SymGuard, IOSymInteract, IOAct(..), IOGateValue, TestChoice)
import Lattest.Model.Automaton(stateConf, IntrpState(..), transRel, AutomatonException(ActionOutsideAlphabet), STStdest(STSLoc), syntacticAutomaton, alphabet, AutIntrpr, after, IOAfter, StepSemantics, Valuation (..))
import Lattest.Model.BoundedMonad(BooleanConfiguration, asExpr, asDualExpr)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.Symbolic.SolveSymPrim(solveAnySequential, solveGuard)
import Lattest.Model.Symbolic.Expr(subst, substVarModel, VarModel, valuationToVarModel, sTrue, (.&&), (.||), sNot, varUnion, mapVars, varName, Variable, mapVarExprs, mapExpressionVars, identityVarModel, getVariables, Constant (..), sFalse, (.==), sVar, sConst, ExprView (And), Val (..), withExprConstraints)
import Lattest.Model.Symbolic.Internal.ExprDefs(Expr(..), ExprType (..))
import Lattest.SMT(SMT, runSMT, Some (..))
import Lattest.Util.Utils(distributeFirstMaybe)

import Control.Arrow((&&&))
import Control.Exception(throw)

import Data.Foldable(toList)
import qualified Data.List as List
import qualified Data.Map as Map
import GHC.Stack(callStack)
import List.Shuffle(shuffle)
import System.Random(RandomGen)
import Data.Maybe (mapMaybe, catMaybes)
import Lattest.Exec.Testing (Verdict (..), TestController (..), InconclusiveReason (..))
import Control.Monad (forM)
import qualified Data.Set as Set
import Data.Some (mapSome)
import Data.Type.Equality ((:~:)(..))
import Data.Constraint.Extras (Has(..))
import Data.GADT.Compare (GEq(..))
import qualified Data.Dependent.Map as DMap

{-|
    For the given STS and a subset function, using SMT solving, find a interaction of the STS in that subset for which the guard is true from the
    current STS state. The interaction is picked uniformly randomly among interactions with satisfied gates, if any. This uses the supplied random 
    generator and returns the new random generator state. The returned gate values for that interaction are not randomized in any way, picking values
    is left to the SMT solver.
-}
solveRandomInteraction :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, RandomGen r, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g'') -> (IOSymInteract i o -> Maybe (SymInteract g')) -> r -> SMT (Maybe (GateValue g'), r)
solveRandomInteraction intrpr subsetFunction r = do
    let interactionsWithGuards = selectInteractionsAndGuards intrpr subsetFunction
        (interactionsWithGuards', r') = shuffle interactionsWithGuards r
    (,r') <$> solveAnySequential interactionsWithGuards' -- prepend the new random state to the solved result
    where
    -- select the subset of gates according to the subsetFunction, together with the guards from the current state configuration according to the STS interpretation
    selectInteractionsAndGuards :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g'') -> (IOSymInteract i o -> Maybe (SymInteract g')) -> [(SymInteract g', SymGuard)]
    selectInteractionsAndGuards intrpr' subsetFunction' =
        let alph = toList $ alphabet $ syntacticAutomaton intrpr'
        in mapMaybe (distributeFirstMaybe . (fmap indexParams . subsetFunction' &&& (\interaction -> interactsToSpecifiedCondition intrpr' [interaction]))) alph
        where
        -- `interactsToSpecifiedCondition` puts the (single) step's variables in SSA form, indexing them with `_0`, so
        -- index the gate parameters we solve for and read the solution back from with the same suffix. Otherwise the
        -- SMT declarations (taken from these parameters) wouldn't match the variables mentioned in the guard.
        indexParams (SymInteract g' params) = SymInteract g' (mapSome (indexVar 0) <$> params)


interactsToSpecifiedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToSpecifiedCondition = interactsToGuard asDualExpr

interactsToAllowedCondition :: (BM.BoundedMonad m, Foldable m, BooleanConfiguration m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a)) => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToAllowedCondition = interactsToGuard asExpr

interactsToGuard :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a))
    => (m SymGuard -> SymGuard) -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> [IOSymInteract i o] -> SymGuard
interactsToGuard f intrpr interacts = f (treeToGuard f interacts BM.<#> seTree intrpr)

{- |
    map a symbolic execution tree to the path condition for a given sequence of interactions, where 
    the monadic branching at each step is collapsed with @f@.
-}
treeToGuard :: (BM.BoundedMonad m, Ord i)
    => (m SymGuard -> SymGuard) -> [i] -> SETree m i -> SymGuard
treeToGuard _ [] _ = sTrue
treeToGuard f (i:is) (SETree setree) = f (stepGuard BM.<#> Map.findWithDefault err i setree)
    where
    stepGuard (SEIte g tTree fTree) = (g .&& f (treeToGuard f is BM.<#> tTree)) .|| (sNot g .&& f (treeToGuard f is BM.<#> fTree))
    err = throw $ ActionOutsideAlphabet callStack

-- | The symbolic state: the location and the mapping of state variables to /indexed/ interaction variables. 
data SymIntrpState loc = SymIntrpState loc VarModel deriving (Eq, Ord)

intrpStateToSym :: IntrpState a -> SymIntrpState a
intrpStateToSym (IntrpState loc vals) = SymIntrpState loc (mapVars (indexVar 0) (valuationToVarModel vals))

-- | Symbolic if-then-else branching
data SEIte t = SEIte SymGuard t t deriving (Eq, Ord)

{- |
    Symbolic execution tree: every interaction monadically leads to guards (over parameters in that interaction, and in previous interactions) and new trees (for the true/false branches).

    Note: the if-then-else @SEIte@ type allows quite general forms of monadic branching, but currently, the use in @seTree@ is quite limited: the
    then-branch is always singular (ordReturn) and the else-branch is always underspecified or forbidden.
-}
newtype SETree m i = SETree (Map.Map i (m (SEIte (m (SETree m i)))))
deriving instance (Ord i, forall a. Ord a => Ord (m a)) => Eq (SETree m i)
deriving instance (Ord i, forall a. Ord a => Ord (m a)) => Ord (SETree m i)

seTree :: (BM.BoundedMonad m, Foldable m, Ord i, Ord o, Ord loc, forall a. Ord a => Ord (m a))
    => AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (GateValue g') -> m (SETree m (IOSymInteract i o))
seTree intrpr =
    let smlocs = intrpStateToSym BM.<#> stateConf intrpr
    in seTree' 0 BM.<#> smlocs
    where
    --t :: loc -> Map.Map (IOSymInteract i o) (m (SymGuard, VarModel, loc))
    t loc = Map.map (BM.ordMap completeSTSLoc) (transRel (syntacticAutomaton intrpr) loc)
    --seTree' :: Int -> SymIntrpState loc -> SETree m i
    -- the LHS pvar contains the indexed vars of the previous step, RHS contains only interaction variables
    seTree' n (SymIntrpState ploc pvar) = SETree $ Map.mapWithKey (BM.ordMap . seStep') (t ploc)
        where
        --seStep' :: (SymGuard, VarModel, loc) -> SEBranch (SETree m i)
        seStep' i (tguard, completedAssign, tloc) =
            let indexedGuard = subst pvar (indexExpr n tguard)
                pvar' = substVarModel pvar (indexLeft (n+1) $ indexRight n completedAssign)
                nextSeTree = BM.ordReturn $ seTree' (n+1) (SymIntrpState tloc pvar')
                negNextSeTree = ioInteractToImpliticLocation i
            in SEIte indexedGuard nextSeTree negNextSeTree
        indexLeft :: Int -> VarModel -> VarModel
        indexLeft k = mapVars $ indexVar k
        indexRight :: Int -> VarModel -> VarModel
        indexRight k = mapVarExprs $ indexVar k
    completeSTSLoc :: (STStdest, loc) -> (SymGuard, VarModel, loc)
    completeSTSLoc (STSLoc (tguard, tassign), tloc) =
        let completedAssign = tassign `varUnion` identityVarModel locVarSet
        in (tguard, completedAssign, tloc)
    locVarSet :: [Some Variable]
    locVarSet = -- a bit hacky: we assume that there is a global set of state variables, but we extract it from the assignment of an arbitrary transition
        let mArbitraryState = toList (stateConf intrpr) List.!? 0
        in case mArbitraryState of
            Just (IntrpState _ arbitraryValuation) -> getVariables arbitraryValuation
            Nothing -> []
    ioInteractToImpliticLocation (SymInteract (In _) _) = BM.underspecified -- this shouldn't be hard-coded
    ioInteractToImpliticLocation (SymInteract (Out _) _) = BM.forbidden

indexExpr :: Int -> Expr t -> Expr t
indexExpr n = mapExpressionVars (indexVar n)
indexVar :: Int -> Variable a -> Variable a
indexVar 0 v = v
indexVar n v  -- don't add a suffix for 0 primes, this avoids dealign with primes in a 1-step lookahead
    | n < 0 = error $ "left symbolic variable with index " ++ show n
    | otherwise = v {varName = varName v ++ "_" ++ show n} -- Hack. Ideally we have a nice representation which avoids collisions, and maybe a statically typed distinction between primed and unprimed variables

-- TODO: unsure whether this should hold arbitrary 'r's, or Verdicts, or both.
-- If 'r's: it would be good to have a test controller combinator that makes a test controller return a Verdict
-- If 'Verdict's: See the final couple lines of this file: I'm not sure how to disambiguate them. Should I just pass the interaction to the automaton and look at the state?
data OfflineTests i o r
  = OfflineTests
      (Map.Map o             -- Map each output to:
        ([Some Constant]          -- The expected valuation;
        , OnlyOrInconclusive -- Whether that is the only allowed valuation, or other valuations should be marked as 'inconclusive';
        , OfflineTests i o r)) -- And the rest of the test.
      (Either (GateValue i, OfflineTests i o r) r) -- Either the chosen input from this state, and the rest of the test following it, or the result if there's no more outputs at this point

data OnlyOrInconclusive = Only | Inconclusiv deriving Show

instance (Show i, Show o, Show r) => Show (OfflineTests i o r) where
  show (OfflineTests os is) = "\\case\n" <> indentOfflineTree os' <> indentOfflineTree is'
    where
      os' = unlines $ map (\(o,(cs, ooi, ot)) -> "!"<> show o <> show cs <> " -> \n" <> indentOfflineTree (show ot) <> case ooi of
                  Only -> ""
                  Inconclusiv -> "!"<> show o <> "[..] -> Inconclusive") $ Map.toList os
      is' = case is of
        Right r -> if Map.null os then show r else ""
        Left (i, ot) -> "?" <> show i <> " -> \n" <> indentOfflineTree (show ot)
      indentOfflineTree "" = ""
      indentOfflineTree s = reverse . ('\n':) . dropWhile (\x -> x == '\n' || x == ' ') . reverse -- ugly hack to remove empty lines
                          . unlines . map ("  " ++) $ lines s

getInputOffline :: OfflineTests i o r -> Either (GateValue i, OfflineTests i o r) r
getInputOffline (OfflineTests _ i) = i

giveOutputOffline :: Ord o => OfflineTests i o Verdict -> GateValue o -> Either (OfflineTests i o Verdict) Verdict
giveOutputOffline (OfflineTests m _) (GateValue o os) = case m Map.!? o of
  Nothing -> Right Fail
  Just (cs, ooi, rest)
    | cs == os  -> Left rest
    | otherwise -> case ooi of
      Only -> Right Fail
      Inconclusiv -> Right $ Inconclusive OutputNotInOfflineTest

offlineTests :: forall m loc i o state r. (forall a. Ord a => Ord (m a), BM.BooleanConfiguration m, Ord i, Ord o, Foldable m, Ord loc, Ord (m (IntrpState loc)), IOAfter m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o), StepSemantics m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o), TestChoice (GateValue i) (IOGateValue i o))
             => AutIntrpr      m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o)
             -> TestController m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o) state (GateValue i) r
             -> IO (OfflineTests i o r)
offlineTests intrpr tc = do
  inputselect <- selectTest tc (testControllerState tc) intrpr (stateConf intrpr)
  i <- case inputselect of -- this is the only reason we need a TestController for offline testing: the choice of input. The alternative is just randomly picking gates, solving guards.
        Right r -> pure $ Right r
        Left (i', st) -> handleAction (In <$> i') (tc {testControllerState = st}) intrpr >>= \case
          Right r -> pure $ Right r
          Left (tc', intrpr') -> do
            ot <- offlineTests intrpr' tc'
            pure $ Left (i', ot)
  o <- Map.fromList . catMaybes <$> do
    let os = mapMaybe (\case
                SymInteract (Out o) vs -> Just $ SymInteract o vs
                SymInteract (In _) _ -> Nothing)
              (toList $ alphabet $ syntacticAutomaton intrpr)
    forM os $ \(SymInteract o vs) -> do
      let guard = interactsToAllowedCondition intrpr [SymInteract (Out o) vs]
      mv <- runSMT $ solveGuard vs guard
      case mv of
        Nothing -> pure Nothing
        Just (runValuation -> m) -> let vs' = map (\(Some v) -> case DMap.lookup v m of
                                                              Just (Val x) -> Some $ Constant (has @ExprType v $ typeOf' v) x
                                                              Nothing -> error $ show v <> "is not in" <> show m) vs in
          (\x y -> Just (o,(vs',x,y)))
          <$> do -- checking whether this is the only valid assignment for this gate, by adding a guard specifying that at least one value should differ
                let guard' = guard .&& (if null vs then sFalse else sNot $ Expr $ And $ Set.fromList
                           $ zipWith (\(Some v) (Some (Constant tp c)) -> has @ExprType v $ case geq (typeOf' v) tp of
                                    Just Refl -> withExprConstraints (typeOf' v) $ view $ sVar v .== sConst c
                                    Nothing -> error "internal type mismatch") vs vs')
                runSMT $ solveGuard vs guard' >>= \case
                  Nothing -> pure Only -- Nothing matches the new guard, so we had the only valuation
                  Just{}  -> pure Inconclusiv -- At least one new valuation is possible, so if the SUT emits other values than expected here we cannot fail it
          <*> (handleAction (GateValue (Out o) vs') tc intrpr >>= \case
             Right r -> pure $ OfflineTests mempty $ Right r
             Left (tc', intrpr') -> offlineTests intrpr' tc')
  pure $ OfflineTests o i
  where
    handleAction :: IOGateValue i o
                 ->   TestController m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o) state (GateValue i) r
                 ->   AutIntrpr      m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o)
                 -> IO (Either
                    ( TestController m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o) state (GateValue i) r
                    , AutIntrpr      m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o))
                    r)
    handleAction x t i = updateTestController t (testControllerState t) i x (stateConf i) >>= \case
      Right r -> pure $ Right r
      -- $ case x of
        -- GateValue (In  _) _ -> Pass -- TODO: testcontrollers with a fixed number of steps do trigger this. Need a way to also deal with them in in the output case! -- error "this should never happen, I think: the testcontroller choosing to stop rather than update based on an input it chose itself"
        -- GateValue (Out _) _ -> Fail -- If the test controller refuses to accept an output, it's a fail? Not necessarily, what if it's just a stopcondition?
      Left st -> pure $ Left (t {testControllerState = st}, after i x)

-- | Given an OfflineTests, checks whether it is a trace (no branching), and returns it.
-- For outputs, it returns both the given output and the starting location.
toTrace :: (forall a. Ord a => Ord (m a), BM.BooleanConfiguration m, Ord i, Ord o, Foldable m, Ord loc, Ord (m (IntrpState loc)), IOAfter m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o), StepSemantics m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o), TestChoice (GateValue i) (IOGateValue i o))
        => AutIntrpr      m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o)
        -> OfflineTests i o r
        -> Maybe [IOAct (GateValue i) (o, OnlyOrInconclusive, [Some Constant], m (IntrpState loc))]
toTrace _ (OfflineTests (Map.toList -> []) (Right _)) = Just []
toTrace intrpr (OfflineTests (Map.toList -> []) (Left (gv, ot))) = (In gv :) <$> toTrace (after intrpr (In <$> gv)) ot
toTrace intrpr (OfflineTests (Map.toList -> [(o,(cs, ooi, ot))]) (Right _)) = (Out (o, ooi, cs, stateConf intrpr) :) <$> toTrace (after intrpr (GateValue (Out o) cs)) ot
toTrace _ _ = Nothing -- either multiple outputs, or input and output

