{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Lattest.Exec.StandardTestControllers.CompleteTestSuite (
accessSeqSelector,
adgTestSelector,
nCompleteSingleState,
runNCompleteTestSuite,
randomCoveringTestSelector,
randomCoveringTestSelectorFromSeed,
randomCoveringTestSelectorFromGen,
slowRandomInputCoverer,
Switch,
allSwitches,
isInputSwitch,
switchesTaken,
observeInputCoverage,
mergeInputCoverage,
prettyPrintInputCoverage,
InputCoverageReport, InputCoverageKey, InputCoverageValue
)
where
import Lattest.Adapter.Adapter(Adapter,close)
import Lattest.Adapter.StandardAdapters(withQuiescenceMillis)
import Lattest.Exec.ADG.Aut(adgAutFromAutomaton)
import Lattest.Exec.ADG.DistGraph(computeAdaptiveDistGraph)
import Lattest.Exec.ADG.SplitGraph(Evidence(..))
import Lattest.Exec.StandardTestControllers(andThen,randomTestSelectorFromSeed,untilCondition,stopAfterSteps,observingOnly,printActions,traceObserver,andObserving,stateObserver, TestSelector, selector, solveRandomInput, TestObserver, observer)
import Lattest.Exec.Testing(TestController(..), runTester,Verdict)
import Lattest.Model.Alphabet(IOAct(..), IOSuspAct, Suspended(..), asSuspended, SymInteract (..), IOSymInteract, IOGateValue, GateValue(..), SymGuard)
import Lattest.Model.Automaton(AutIntrpr(..),AutSyntax (..), After, TransitionMapping (..), STStdest(..), IntrpState(..), buildGateValuation, evalBool, implicitDestination)
import Lattest.Model.BoundedMonad(Det(..), asConjunction, FreeLattice, ordBind, ordReturn)
import Lattest.Model.StandardAutomata(ConcreteSuspAutIntrpr, accessSequences, interpretQuiescentConcrete, IOSTSIntrp, allLocations, symStep)
import Lattest.Model.Symbolic.SolveSymPrim(substituteInGuard, isGuardSatisfiable, solveGuardAny, valuationToGateValue)

import Control.Monad (forM, (>=>), filterM)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Dependent.Sum (DSum (..))
import qualified Data.Set as Set
import System.Random(StdGen, initStdGen, mkStdGen)
import Data.Maybe (fromMaybe)
import Data.Foldable (toList)
import Data.Either (fromRight)
import Lattest.Model.Symbolic.Expr (Variable (..), Val (..), Constant (..), withExprConstraints, Type, sTrue, (.||), (.&&), VarModel (..), valuationToVarModel, getVariables, freeVars, sAnd, sNot, sExists, varsToGuard, Expr, sVar, (.==), reduce)
import Lattest.Model.Symbolic.Internal.ExprDefs (Expr(..))
import Lattest.Model.Symbolic.SolveSTS (solveRandomInteractionWith, indexVar)
import Data.Dependent.Map (DMap)
import Data.Some (Some(..), mapSome)
import Data.Type.Equality ((:~:)(..))
import Data.GADT.Compare (GEq(..), GCompare (..), GOrdering (..))
import qualified Data.Dependent.Map as DMap
import Data.GADT.Show (GShow (..), defaultGshowsPrec)
import Data.Constraint.Extras (Has (..))
import Data.Constraint.Compose (ComposeC)
import qualified Data.Maybe as Maybe
import Control.Monad.Extra (findM, anyM, firstJustM)
import Control.Monad.State (StateT, runStateT)
import Data.Containers.ListUtils (nubOrdOn)
import Data.Char (ord)
import qualified Debug.Trace

{- | A TestController that selects inputs that lead to the given targetState. If unexpected outputs are selected by the SUT the TestSelector still tries to provide the inputs of the access sequence, but this may result in reaching another state.
 Result Bool is True when access sequence has been followed and false when the SUT deviated
-}
accessSeqSelector :: (Ord q, Eq i, Eq o) => ConcreteSuspAutIntrpr Det q i o -> q -> TestController Det q q (IOAct i o) () (IOSuspAct i o) [IOAct i o] (Maybe i) Bool
accessSeqSelector aut targetState =
    let initState = case stateConf aut of
            Det q -> q
            _ -> error "Access sequence: model must be in a specified initial state"
        accSeqs = accessSequences aut initState
    in TestController {
        testControllerState = Maybe.fromJust $ accSeqs Map.!? targetState,
        selectTest = accSeqSelectTest,
        updateTestController = accSeqUpdateTest,
        handleTestClose = \testState' -> return $ case testState' of [] ->  True; _ -> False
    }
    where
    accSeqSelectTest [] _ _ = return $ Right True
    accSeqSelectTest (l:ls) _ _ = return $ case l of
        In i -> Left (Just i, l:ls)
        _ -> Left (Nothing, l:ls)
    accSeqUpdateTest [] _ _ _ = return $ Right True
    accSeqUpdateTest (l:ls) _ label _ = return $ if asSuspended l == label then Left ls else Right False

{- | A TestController that selects inputs according to the adaptive distinguishing sequence of the given automaton
-}
adgTestSelector :: (Ord q, Ord l) => ConcreteSuspAutIntrpr Det q l l -> l ->  TestController Det q q (IOAct l l) () (IOSuspAct l l) (Evidence l) (Maybe l) (Set.Set q)
adgTestSelector aut delta =
    let adgaut = case adgAutFromAutomaton aut delta of
                    Just a -> a
                    Nothing ->  error "could not transform Lattest auomaton into ADG automaton"
        adg = computeAdaptiveDistGraph adgaut False False True
    in TestController {
        testControllerState = adg,
        selectTest = adgSelectTest,
        updateTestController = adgUpdateTest,
        handleTestClose = \_ -> return Set.empty
    }
    where
    adgSelectTest testState _ _ =
        return $ case testState of
            Nil -> Right Set.empty
            Prefix l _ -> Left (Just l, testState)
            Plus _ -> Left (Nothing,testState)

    adgUpdateTest testState _ ioact _ =
       return $ case testState of
            Nil -> Right Set.empty
            Prefix l next -> if ioact == In l then Left next else error "Error: expected to have selected an input but seeing some ioact"
            Plus ls ->
                let nextList = concatMap getNextState ls
                in case nextList of
                    [next] -> Left next
                    _ -> error "ADG error: expected to have observed one output or quiescence"
                where
                getNextState ev = case ev of
                    Nil -> []
                    Prefix l next -> if l == delta
                                        then [next | ioact == Out Quiescence]
                                     else [next | ioact == Out (OutSusp l)]
                    Plus ls' -> concatMap getNextState ls'

{- | A TestController that yields tests that tries to take an access sequence to the targetState and then executes the adaptive distinguishing sequence
-}
nCompleteSingleState :: (Ord q, Ord l) => ConcreteSuspAutIntrpr Det q l l -> Int -> Int -> l -> q
                                                    -> TestController Det q q (IOAct l l) () (IOSuspAct l l) (((), [IOSuspAct l l]), Maybe (Det q)) i20 ([IOSuspAct l l], Maybe (Det q))
                                                    -> IO (TestController Det q q (IOAct l l) () (IOSuspAct l l) (Either (Either [IOAct l l] StdGen, Int) (Evidence l), (((), [IOSuspAct l l]), Maybe (Det q))) (Maybe l) ([IOSuspAct l l], Maybe (Det q)))
nCompleteSingleState model seed nrSteps delta targetState observer' = do
    return $ accessSeqSelector model targetState
        `andThen` randomTestSelectorFromSeed seed `untilCondition` stopAfterSteps nrSteps
            `andThen` adgTestSelector model delta `observingOnly` observer'

{- | Runs tests from nCompleteSingleState for each given targetState and seed
-}
runNCompleteTestSuite :: (Ord q, Ord l, Show q, Show l) => IO (Adapter (IOAct l l) l) -> AutSyntax Det q (IOAct l l) () -> Int -> l -> [(q, Int)] -> IO [(q, Verdict, ([IOSuspAct l l], Maybe (Det q)))]
runNCompleteTestSuite adapter spec nrSteps delta targetStatesAndSeeds =
        forM targetStatesAndSeeds $ \(targetState,seed) -> do
            putStrLn "connecting..."
            adap <- adapter
            imp <- withQuiescenceMillis 200 adap
            let model = interpretQuiescentConcrete spec
            putStrLn "starting test..."
            putStrLn $ "accessing state: " ++ show targetState
            selector' <- testSelector model seed targetState
            (verdict,(observed, maybeMq)) <- runTester model selector' imp
            close adap
            return (targetState, verdict, (observed, maybeMq))
    where testSelector model seed targetState = nCompleteSingleState model seed nrSteps delta targetState $ printActions `observingOnly` traceObserver `andObserving` stateObserver

-- The most basic version: randomly pick an uncovered input, if any, and otherwise just random
-- If a 'to cover' set is not provided, it gets initialized to the set of every transition
-- Using 'observeControllerState', the set of uncovered transitions can be passed on to the next test.
randomCoveringTestSelector
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Show i', Show o, Show loc, Ord i', Ord o, Ord q, Ord loc
     , tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> IO (TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o)) i)
randomCoveringTestSelector intrpr mtocover = randomCoveringTestSelectorFromGen intrpr mtocover <$> initStdGen

-- | As 'randomCoveringTestSelector', starting with the given random seed.
randomCoveringTestSelectorFromSeed
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Show i', Show o, Show loc, Ord i', Ord o, Ord q, Ord loc
     , tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> Int
  -> TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o)) i
randomCoveringTestSelectorFromSeed intrpr mtocover seed = randomCoveringTestSelectorFromGen intrpr mtocover (mkStdGen seed)

randomCoveringTestSelectorFromGen
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Show i', Show o, Show loc, Ord i', Ord o, Ord loc, Ord q,
     tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> StdGen
  -> TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o)) i
randomCoveringTestSelectorFromGen intrpr mtocover g = selector (g, fromMaybe (allSwitches intrpr) mtocover) select update
  where
    select :: (StdGen, Set.Set (Switch loc i' o))
           -> AutIntrpr m loc q t tdest act
           -> m q
           -> IO (Maybe (i, (StdGen, Set.Set (Switch loc i' o))))
    select (g', tocover) intrpr' mq = do
      -- as in randomDataTestSelectorFromGen, except we try to take new transitions
      (maybeGateValue, g'') <- solveRandomInteractionWith intrpr' maybeNewInAct g'
      case maybeGateValue of
        Just value -> pure $ Just (value, (g'',tocover))
        Nothing -> do
          (maybeGateValue', g''') <- solveRandomInput g'' maybeFromIOAct intrpr'
          return $ case maybeGateValue' of
            Just value -> Just (value, (g''',tocover))
            Nothing -> Nothing
      where
        maybeFromIOAct (SymInteract io xs) = case io of
          In i -> Just $ SymInteract i xs
          Out _ -> Nothing
        maybeNewInAct = maybeFromIOAct >=> \(SymInteract i vs) -> case asConjunction mq of
          -- The state has disjunction, so we're not covering any new transitions anyway.
          -- Just take a random transition.
          Left _ -> Just (SymInteract i vs, sTrue)
          -- The actual filtering: besides picking a gate with an uncovered switch, require the guard of some uncovered switch
          -- to hold. Otherwise the solver is free to keep picking values for the already covered switches of that gate.
          Right qs -> case [ substituteInGuard v guard | IntrpState l v <- Set.toList qs, Switch loc act (STSLoc (guard, _)) _dest <- Set.toList tocover, loc == l, act == SymInteract (In i) vs ] of
            [] -> Nothing
            gs -> Just (SymInteract i vs, foldr1 (.||) gs)  -- or'd guards of uncovered switches to make sure we cover at least one

    -- note: coverage is computed from the `m q` before the transition, which is passed in as the last argument.
    update :: (a, Set.Set (Switch loc i' o))
           -> AutIntrpr m loc q t tdest act
           -> IOGateValue i' o
           -> m q
           -> IO (Maybe (a, Set.Set (Switch loc i' o)))
    update (g', tocover) intrpr' act mq =
      let newcover = switchesTaken intrpr' mq act
      in pure $ Just (g', tocover Set.\\ newcover)

-- | A switch of an STS: source location, interaction (gate and parameters), guard and assignment, and target location.
data Switch loc i o = Switch loc (IOSymInteract i o) STStdest loc deriving (Eq, Ord, Show)

-- | All switches present in the model.
allSwitches :: (Ord loc, Ord i, Ord o) => IOSTSIntrp FreeLattice loc i o -> Set.Set (Switch loc i o)
allSwitches intrpr = let syn = syntacticAutomaton intrpr
  in Set.fromList [ Switch l t td l' | l <- Set.toList (allLocations syn), (t, dests) <- Map.toList (transRel syn l), (td, l') <- toList dests ]

isInputSwitch :: Switch loc i o -> Bool
isInputSwitch (Switch _ (SymInteract (In _) _) _ _) = True
isInputSwitch _ = False

{- |
    The switches taken by an action from the given state configuration. If the configuration contains a disjunction, it is unknown
    which switches were taken, so none are reported.
-}
switchesTaken :: (Ord loc, Ord i, Ord o)
  => IOSTSIntrp FreeLattice loc i o -> FreeLattice (IntrpState loc) -> IOGateValue i o -> Set.Set (Switch loc i o)
switchesTaken intrpr mq gv@(GateValue _ vals) = case (asConjunction mq, asTransition (alphabet syn) gv) of
  (Right qs, Just t@(SymInteract _ vars)) -> Set.unions
    [ fromRight mempty $ asConjunction $ dests `ordBind` \(td@(STSLoc (g, _)), l') ->
        if evalBool (buildGateValuation vars vals) (substituteInGuard v g)
          then ordReturn $ Switch l t td l'
          else implicitDestination gv
    | IntrpState l v <- Set.toList qs
    , Just dests <- [Map.lookup t (transRel syn l)] ]
  _ -> mempty
  where syn = syntacticAutomaton intrpr

data InputCoverageKey i tp = ICK i SymGuard (Variable tp) deriving Show
data InputCoverageValue tp = ICV (Type tp) (Set.Set (Val tp)) deriving Show
type InputCoverageReport i = DMap (InputCoverageKey i) InputCoverageValue
instance GEq (InputCoverageKey i) where
  geq (ICK _ _ v) (ICK _ _ v') = geq v v'
instance Ord i => GCompare (InputCoverageKey i) where
  gcompare (ICK i g v) (ICK i' g' v') = case compare i i' of
    GT -> GGT
    LT -> GLT
    EQ -> case compare g g' of
      GT -> GGT
      LT -> GLT
      EQ -> gcompare v v'
instance Show i => GShow (InputCoverageKey i) where
  gshowsPrec = defaultGshowsPrec
instance Has a Type => Has a InputCoverageValue where
  has (ICV t _) = has @a t
instance Has (ComposeC Show InputCoverageValue) (InputCoverageKey i) where
  has (ICK _ _ v) = withExprConstraints v

{- |
    Combine two input coverage reports.
-}
mergeInputCoverage :: Ord i => InputCoverageReport i -> InputCoverageReport i -> InputCoverageReport i
mergeInputCoverage = DMap.unionWithKey (\_ (ICV t a) (ICV _ b) -> ICV t (Set.union a b))

{- |
    Render an input coverage report: per input gate, per guard, the values used for each parameter.
-}
prettyPrintInputCoverage :: (Show i, Ord i) => InputCoverageReport i -> String
prettyPrintInputCoverage icr = unlines $ concat
    [ show gate' : concat
        [ ("  guard: " <> guard) : [ "    " <> var <> ": " <> List.intercalate ", " vals <> " (" <> show (length vals) <> " different input values)" | (var, vals) <- params ]
        | (guard, params) <- Map.toList guards ]
    | (gate', guards) <- Map.toList grouped ]
  where
    grouped = Map.fromListWith (Map.unionWith (<>))
        [ (gate', Map.singleton (show guard) [(show v, show <$> Set.toList vals)]) | ICK gate' guard v :=> ICV _ vals <- DMap.toList icr ]

observeInputCoverage :: (Show i, Ord loc, Ord i, Ord o) => TestObserver FreeLattice loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o) (InputCoverageReport i) (InputCoverageReport i)
observeInputCoverage = observer mempty update pure
  where
    update icr _ (GateValue (Out _) _) _ = pure icr
    update icr intrpr (GateValue (In gate') consts) mq = pure $ foldr (\(guard, c :=> v) icr' -> DMap.insertWith (\(ICV t a) (ICV _ b) -> ICV t $ Set.union a b) (ICK gate' guard v) (ICV (constType c) $ Set.singleton $ withExprConstraints c Val $ constValue c) icr') icr $ cartesian guards taggedvals
      where
        -- the guards of the switches that are taken: the ones that hold for the input values, in the state before the transition
        guards
          | Right qs <- asConjunction mq = concatMap (\(IntrpState loc v) -> case asConjunction $ transRel (syntacticAutomaton intrpr) loc Map.! SymInteract (In gate') vars of
                Right tdests -> [ guard | (STSLoc (guard, _), _) <- Set.toList tdests, evalBool (buildGateValuation vars consts) (substituteInGuard v guard) ]
                Left _ -> error "TODO: compute input coverage for disjunctions") $ Set.toList qs
          | otherwise = error "TODO: compute input coverage for disjunctions" -- mempty
        taggedvals :: [DSum Constant Variable]
        taggedvals = zipWith
          (\(Some c@(Constant tp1 _)) (Some v@(Variable _ tp2)) -> case geq tp1 tp2 of
              Nothing -> error "type mismatch"
              Just Refl -> c :=> v)
          consts
          vars
        alph = alphabet $ syntacticAutomaton intrpr
        vars = case Set.toList $ flip Set.filter alph \case
          SymInteract (Out _) _ -> False
          SymInteract (In i) _ -> i == gate' of
            [SymInteract _ vs] -> vs
            _ -> error $ "zero or more than one inputs in the alphabet match " <> show gate'
        cartesian as bs = [(a,b) | a <- as, b <- bs]

slowRandomInputCoverer
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Show i', Show o, Show loc, Ord i', Ord o, Ord loc, Ord q,
     tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> Int
  -> StdGen
  -> TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o), Maybe [act], Int) i
slowRandomInputCoverer intrpr mtocover maxSteps g = selector (g, fromMaybe (allSwitches intrpr) mtocover, Nothing, maxSteps) select update
  where
    select :: (StdGen, Set.Set (Switch loc i' o), Maybe [act], Int)
           -> AutIntrpr m loc q t tdest act
           -> m q
           -> IO (Maybe (i, (StdGen, Set.Set (Switch loc i' o), Maybe [act], Int)))
    select (g', tocover, Just (act:plan), budget) _ _ = case act of -- There is a plan; we execute it.
      GateValue (Out _) _ -> pure Nothing -- the plan is to wait for an output here, so we don't choose an input
      GateValue (In i) cs -> pure $ Just (GateValue i cs, (g', tocover, Just (act:plan), budget)) -- don't remove the act from the plan here, only in update!
    select (g', tocover, Just [], budget) intrpr' mq = select (g', tocover, Nothing, budget) intrpr' mq
    select (g', tocover, Nothing, budget) intrpr' mq = do
      -- don't currently have a plan. If there's immediately any untaken switches available, we take one
      (maybeGateValue, g'') <- solveRandomInteractionWith intrpr' maybeNewInAct g'
      case maybeGateValue of
        Just value -> pure $ Just (value, (g'',tocover, Nothing, budget))
        Nothing -> do
          -- There are no untaken switches available currently, so we create a plan
          case asConjunction mq of
            Left _ -> do -- Not going to BFS in a disjunction state, default to a random transition
              takeRandomInput g''
            Right currStates -> do
              let initial = [ (loc, (sTrue, valuationToVarModel v, 0)) | IntrpState loc v <- Set.toList currStates ]
              -- only look for plans that can be completed, including taking the uncovered switch afterwards, in the steps that are left
              found <- breadthFirstSearch2 key "a" visit substract (Map.fromList $ map (\a -> (key a, a)) initial) (map (,[]) initial) bfsStep bfsPred (budget - 1)
              -- found <- breadthFirstSearch key (Set.fromList $ map key initial) (map (,[]) initial) bfsStep bfsPred (budget - 1)
              (plan, g''') <- runStateT (maybe (pure Nothing) concretise found) g''
              case plan of
                -- Note: the plan only goes to a state where the switch _can_ be taken, but doens't take it.
                -- Could add taking it, but this testcontroller will, once the plan is done,
                -- just take a random untaken switch anyway (of which we know at least one is present).
                Just (act:acts) -> select (g''', tocover, Just (act:acts), budget) intrpr' mq
                _ -> takeRandomInput g'''
      where
        maybeFromIOAct (SymInteract io xs) = case io of
          In i -> Just $ SymInteract i xs
          Out _ -> Nothing
        maybeNewInAct = maybeFromIOAct >=> \(SymInteract i vs) -> case asConjunction mq of
          -- The state has disjunction, so we're not covering any new transitions anyway.
          -- Just take a random transition.
          Left _ -> Just (SymInteract i vs, sTrue)
          -- The actual filtering: besides picking a gate with an uncovered switch, require the guard of some uncovered switch
          -- to hold. Otherwise the solver is free to keep picking values for the already covered switches of that gate.
          Right qs -> case [ substituteInGuard v guard | IntrpState l v <- Set.toList qs, Switch loc act (STSLoc (guard, _)) _dest <- Set.toList tocover, loc == l, act == SymInteract (In i) vs ] of
            [] -> Nothing
            gs -> Just (SymInteract i vs, foldr1 (.||) gs)  -- or'd guards of uncovered switches to make sure we cover at least one
        takeRandomInput g'' = do
          (maybeGateValue', g''') <- solveRandomInput g'' maybeFromIOAct intrpr'
          return $ case maybeGateValue' of
            Just value -> Just (value, (g''',tocover, Nothing, budget))
            Nothing -> Nothing

        locVars = case toList mq of
          IntrpState _ v : _ -> getVariables v
          [] -> []
        isSat (Expr . reduce . view -> guard) = Debug.Trace.traceShow guard $ isGuardSatisfiable (toList $ freeVars guard) guard
        -- the gate parameters as they occur in the guard of the n-th step of a path, see `symStep`
        indexParams n (SymInteract gate' vars) = SymInteract gate' (mapSome (indexVar n) <$> vars)

        -- arguments to the BFS
        -- branch to all satisfiable options
        bfsStep :: SymNode loc -> IO [(SymNode loc, IOSymInteract i' o)]
        bfsStep (loc, (pathCond, pvar, n)) = filterM (\((_, (pathCond', varmodel, _)), _) -> Debug.Trace.trace "bfsStep" $ isSat $ pathCond' .&& varsToGuard varmodel)
          [ ((loc', (pathCond .&& guard, pvar', n + 1)), indexParams n t)
          | (t, dests) <- Map.toList $ transRel (syntacticAutomaton intrpr') loc
          , (tdest, loc') <- Set.toList $ Set.fromList $ toList dests
          , let (guard, pvar') = symStep locVars n pvar tdest ]

        -- check whether an uncovered switch can be taken from this location
        bfsPred :: SymNode loc -> IO Bool
        bfsPred = anyM (Debug.Trace.trace "bfsPred" $ isSat . snd) . targetConds

        key :: SymNode loc -> loc
        key = fst

        visit :: SymNode loc -> SymNode loc -> String -> (String, SymNode loc)
        visit (l1, (g1, v1, _)) (l2, (g2, v2, _)) nms
          | l1 == l2 = (nms3, (l1, (g3, v3, undefined)))
            where
              -- - rename parameters in both guard and varmodel to avoid clashes
              -- - return a guard&varmodel that together represent the union ('or')
              --   of the spaces. The varmodel should resolve each conflict by
              --   assigning to a variable. The guard should be one big 'or' of
              --   two guards, each of which includes the corresponding original guard
              --   as well as equalities of the aforementioned variables to their valuations
              --   in the original varmodels.
              g3 = g1' .|| g2'
              (nms1, r1) = renameVarModel v1 nextname nms
              (nms2, r2) = renameVarModel v2 nextname nms1
              v3x = Set.toList $ Set.union (Set.fromList $ DMap.keys $ runVarModel v1) (Set.fromList $ DMap.keys $ runVarModel v2)
              (nms3, r3) = renameVarModel (VarModel $ DMap.fromList $ map (\(Some x) -> x :=> sVar x) v3x) nextname nms2
              v3 = VarModel $ DMap.fromList $ map (\(Some var) -> var :=> sVar (r3 DMap.! var)) v3x
              g1' = g1 .&& foldr (\(original :=> renamed) xs -> withExprConstraints original $ xs .&& (sVar renamed .== sVar (r1 DMap.! original))) sTrue (DMap.toList r3)
              g2' = g2 .&& foldr (\(original :=> renamed) xs -> withExprConstraints original $ xs .&& (sVar renamed .== sVar (r2 DMap.! original))) sTrue (DMap.toList r3)
        visit _ _ _ = error "mismatched locs"

        -- for generating fresh variable names
        nextname "" = "a"
        nextname ('z':rest) = 'a' : nextname rest
        nextname (c:rest) = toEnum (ord c + 1) : rest

        substract :: SymNode loc -> SymNode loc -> SymNode loc
        -- return roughly "this && not (exists parameters exceptthat)"
        -- That corresponds to the solution space that is accepted by 'this',
        -- but not satisfiable by 'exceptthat'.
        substract _this@(l, (gthis,v,i)) _exceptthat@(_,(gET,v',_)) = (l, (guard,v,i))
          where
            exceptthatparameters = DMap.foldrWithKey (\_ e vs -> freeVars e `Set.union` vs) (freeVars gET) (runVarModel v') Set.\\ (Set.fromList (DMap.keys (runVarModel v')) `Set.union` Set.fromList (DMap.keys (runVarModel v)))
            existsETP expr = foldr (\(Some var) e -> withExprConstraints var $ sExists var e) expr exceptthatparameters
            guard = sAnd $ Set.fromList
              [ gthis
              , sNot
              $ existsETP
              $ gET .&& varsToGuard v']

        -- per uncovered switch from this location: its gate parameters, and the condition to get to this location and then take that switch
        targetConds :: SymNode loc -> [([Some Variable], SymGuard)]
        targetConds (loc, (pathCond, pvar, n)) =
          [ (vars, pathCond .&& fst (symStep locVars n pvar tdest))
          | Switch src t tdest _ <- Set.toList tocover, src == loc
          , let SymInteract _ vars = indexParams n t ]

        -- pick values for the gates along the path, such that an uncovered switch can be taken at the end of it
        concretise :: (SymNode loc, [IOSymInteract i' o]) -> StateT StdGen IO (Maybe [act])
        concretise (node, path) = fmap (\valuation -> map (`valuationToGateValue` valuation) path)
          <$> firstJustM (\(targetVars, cond) -> solveGuardAny (pathVars ++ targetVars) cond) (targetConds node)
          where pathVars = concat [ vars | SymInteract _ vars <- path ]

    -- note: coverage is computed from the `m q` before the transition, which is passed in as the last argument.
    update :: (a, Set.Set (Switch loc i' o), Maybe [act], Int)
           -> AutIntrpr m loc q t tdest act
           -> IOGateValue i' o
           -> m q
           -> IO (Maybe (a, Set.Set (Switch loc i' o), Maybe [act], Int))
    update (g', tocover, plan, budget) intrpr' act mq =
      let newcover = switchesTaken intrpr' mq act
          newplan = case plan of
            Nothing -> Nothing
            Just [] -> Nothing
            Just (act':acts) -> if act == act'
              then Just acts -- successfully acted on our plan
              else Nothing -- failed to follow the plan: did the SUT choose an output we didn't hope for?
      in pure $ Just (g', tocover Set.\\ newcover, newplan, budget - 1)

-- | A vertex of the symbolic search for a path: a location, with the path condition to get there, the symbolic values of the
-- state variables once there, and the number of steps taken to get there.
type SymNode loc = (loc, (SymGuard, VarModel, Int))

-- self-rolled BFS that: works with monadic steps, distinguishes between vertices and edges, and returns the vertex it found together with
-- the path it took as a list of edges. Vertices count as visited only if the location matches, but more info is carried.
-- I haven't looked much into what else is on Hackage, maybe there's a much more elegant solution using something like Data.Graph
breadthFirstSearch :: (Monad m, Ord k) => (a -> k) -> Set.Set k -> [(a, [b])] -> (a -> m [(a,b)]) -> (a -> m Bool) -> Int -> m (Maybe (a, [b]))
breadthFirstSearch key visited frontier step predicate maxdepth
  | maxdepth <= 0 || null frontier = pure Nothing -- failed to find a path
  | otherwise = do
      new <- nubOrdOn (key . fst) -- we only keep one of each state, if there were multiple paths to get somewhere
          . concatMap (filter (not . (`Set.member` visited) . key . fst))
          <$> mapM
                (\(a,bs) -> map (\(a',b') -> (a', b':bs)) <$> step a)
                frontier
      let newVisited = Set.union (Set.fromList $ map (key . fst) new) visited
      findM (predicate . fst) new >>= \case
        Nothing -> breadthFirstSearch key newVisited new step predicate (maxdepth - 1)
        Just (a, path) -> pure $ Just (a, reverse path) -- the path was built up back to front

-- Like breadthFirstSearch, but more fine-grained. Where bFS represents visited nodes with 'k' (using Eq),
-- bFS2 keeps track of an 'a' per visited node. It requires a way to combine multiple visited 'a's,
-- and a way to substract the visited 'a' from a new node.
-- This current version (the way it's called above) is too slow:
-- each call to 'substract' adds complexity, and after just a few nested calls to substract z3 spins out of control on the resulting guard.
-- A potential change would be to check satisfiability on the substracted expr, but then put the non-substracted one in the new frontier.
-- Another future change, if guards seem solveable but there are too many calls to the solver, is to deal with duplication in the frontier:
-- currently, we only filter 'visited' out of the frontier, but don't combine or check for overlap within the frontier.
-- This seems like it could result in more complicated queries, so we should first address the issue of nested substract guards.
breadthFirstSearch2 :: (Monad m, Ord k) => (a -> k) -> x -> (a -> a -> x -> (x, a)) -> (a -> a -> a) -> Map.Map k a -> [(a, [b])] -> (a -> m [(a,b)]) -> (a -> m Bool) -> Int -> m (Maybe (a, [b]))
breadthFirstSearch2 key x visit substract visited frontier step predicate maxdepth
  | maxdepth <= 0 || null frontier = pure Nothing -- failed to find a path
  | otherwise = do
      new <- concat <$> mapM
            (\(a,bs) -> map (\(a',b') -> (a', b':bs)) <$> do
              preciseStep <- Debug.Trace.trace "step1" $ step (maybe a (substract a) $ visited Map.!? key a)
              if null preciseStep then Debug.Trace.trace "was empty" $ pure [] else case visited Map.!? key a of
                Nothing -> Debug.Trace.trace "was pure" $ pure preciseStep
                Just _ -> Debug.Trace.trace "step2" $ step a)
            frontier
      let (newx, newVisited) = foldr
            (\(a,_) (x', visited') -> case Map.lookup (key a) visited' of
              Nothing -> (x', Map.insert (key a) a visited')
              Just a' -> let (x'', a'') = visit a a' x' in (x'', Map.insert (key a) a'' visited'))
            (x, visited)
            new
      findM (predicate . fst) new >>= \case
        Nothing -> breadthFirstSearch2 key newx visit substract newVisited new step predicate (maxdepth - 1)
        Just (a, path) -> pure $ Just (a, reverse path) -- the path was built up back to front

renameVarModel :: VarModel -> (String -> String) -> String -> (String, DMap Variable Variable)
renameVarModel (VarModel m) next s = DMap.foldrWithKey step (s, mempty) m
  where
    step :: Variable a -> Expr a -> ([Char], DMap Variable Variable) -> ([Char], DMap Variable Variable)
    step v e x = let fv = freeVars e in foldr
      (\(Some var@(Variable nm tp)) (st, rename) ->
        if Maybe.isJust (DMap.lookup var rename)
        then (st,rename)
        else (next st, DMap.insert (Variable nm tp) (Variable ("renamed_" <> st) tp) rename))
      x
      (Set.insert (Some v) fv)
