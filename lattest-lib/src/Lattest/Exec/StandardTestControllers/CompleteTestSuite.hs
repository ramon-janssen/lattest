{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Lattest.Exec.StandardTestControllers.CompleteTestSuite (
accessSeqSelector,
adgTestSelector,
nCompleteSingleState,
runNCompleteTestSuite,
randomCoveringTestSelector,
randomCoveringTestSelectorFromSeed,
randomCoveringTestSelectorFromGen,
Switch,
allSwitches,
isInputSwitch,
switchesTaken
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
import Lattest.Model.Automaton(AutIntrpr(..),AutSyntax (..), After, asLoc, TransitionMapping (..), allLocations, STStdest(..), IntrpState(..), buildGateValuation, evalBool, implicitDestination)
import Lattest.Model.BoundedMonad(Det(..), asConjunction, FreeLattice, ordBind, ordReturn)
import Lattest.Model.StandardAutomata(ConcreteSuspAutIntrpr, accessSequences, interpretQuiescentConcrete, IOSTSIntrp)
import Lattest.Model.Symbolic.SolveSymPrim(substituteInGuard)

import Control.Monad (forM, (>=>))
import qualified Data.Map as Map
import Data.Dependent.Sum (DSum (..))
import qualified Data.Set as Set
import System.Random(StdGen, initStdGen, mkStdGen)
import Data.Maybe (fromMaybe)
import Data.Foldable (toList)
import Data.Either (fromRight)
import Lattest.Model.Symbolic.Expr (Variable (..), Val, Constant (..))
import Data.Dependent.Map (DMap)
import Data.Some (Some(..))
import Data.Type.Equality ((:~:)(..))
import Data.GADT.Compare (GEq(..))
import qualified Data.Dependent.Map as DMap

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
        testControllerState = (Map.!) accSeqs targetState,
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
nCompleteSingleState model seed nrSteps delta targetState observer = do
    return $ accessSeqSelector model targetState
        `andThen` randomTestSelectorFromSeed seed `untilCondition` stopAfterSteps nrSteps
            `andThen` adgTestSelector model delta `observingOnly` observer

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
     (After m loc q t tdest act, Ord i', Ord o, Ord q, Ord loc
     , tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> IO (TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o), [act], m q) i)
randomCoveringTestSelector intrpr mtocover = randomCoveringTestSelectorFromGen intrpr mtocover <$> initStdGen

-- | As 'randomCoveringTestSelector', starting with the given random seed.
randomCoveringTestSelectorFromSeed
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Ord i', Ord o, Ord q, Ord loc
     , tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> Int
  -> TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o), [act], m q) i
randomCoveringTestSelectorFromSeed intrpr mtocover seed = randomCoveringTestSelectorFromGen intrpr mtocover (mkStdGen seed)

randomCoveringTestSelectorFromGen
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Ord i', Ord o, Ord loc, Ord q,
     tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (Switch loc i' o))
  -> StdGen
  -> TestSelector m loc q t tdest act (StdGen, Set.Set (Switch loc i' o), [act], m q) i
randomCoveringTestSelectorFromGen intrpr mtocover g = selector (g, fromMaybe (allSwitches intrpr) mtocover, [], stateConf intrpr) select update
  where
    select :: (StdGen, Set.Set (Switch loc i' o), [act], m q)
           -> AutIntrpr m loc q t tdest act
           -> m q
           -> IO (Maybe (i, (StdGen, Set.Set (Switch loc i' o), [act], m q)))
    select (g', tocover, trace, _) intrpr' mq = do
      -- as in randomDataTestSelectorFromGen, except we try to take new transitions
      (maybeGateValue, g'') <- solveRandomInput @FreeLattice g' maybeNewInAct intrpr'
      case maybeGateValue of
        Just value -> pure $ Just (value, (g'',tocover,trace, mq))
        Nothing -> do
          (maybeGateValue', g''') <- solveRandomInput g'' maybeFromIOAct intrpr'
          return $ case maybeGateValue' of
            Just value -> Just (value, (g''',tocover,trace, mq))
            Nothing -> Nothing
      where
        maybeFromIOAct (SymInteract io xs) = case io of
          In i -> Just $ SymInteract i xs
          Out _ -> Nothing
        maybeNewInAct = maybeFromIOAct >=> \(SymInteract i vs) -> case asConjunction mq of
          -- The state has disjunction, so we're not covering any new transitions anyway.
          -- Just take a random transition.
          Left _ -> Just (SymInteract i vs)
          -- The actual filtering:
          Right qs -> if any (\q -> any (\(Switch loc act _tdest _dest) -> loc == asLoc q && act == SymInteract (In i) vs) tocover) qs
            then Just (SymInteract i vs)
            else Nothing

    -- note: the intrpr we get here is _after_ the transition, but we need the `m q` before the transition
    -- to compute coverage. That's why we keep track of it in the quadruple.
    update :: (a, Set.Set (Switch loc i' o), [IOGateValue i' o], m q)
           -> AutIntrpr m loc q t tdest act
           -> IOGateValue i' o
           -> b
           -> IO (Maybe (a, Set.Set (Switch loc i' o), [IOGateValue i' o], m q))
    update (g', tocover, trace, mq) intrpr' act _ =
      let newcover = switchesTaken intrpr' mq act
      in pure $ Just (g', tocover Set.\\ newcover, trace ++ [act], stateConf intrpr')

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

data InputCoverageKey i tp = ICK i SymGuard (Variable tp)
newtype InputCoverageValue tp = ICV (Set.Set (Val tp))
type InputCoverageReport i = DMap (InputCoverageKey i) InputCoverageValue
observeInputCoverage :: {- IOSTSIntrp m loc i o -> -} TestObserver m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o) (InputCoverageReport i) (InputCoverageReport i)
observeInputCoverage = observer mempty update pure
  where
    update icr _ (GateValue (Out _) _) _ = pure icr
    update icr intrpr (GateValue (In gate) vals) _ = pure $ foldr (\(v :=> c) icr' -> DMap.insertWith _ (ICK gate v) (ICV $ Set.singleton $ _ c) icr') icr taggedvals
      where
        taggedvals = zipWith
          (\(Some c@(Constant tp1 _)) (Some v@(Variable _ tp2)) -> case geq tp1 tp2 of
              Nothing -> error "type mismatch"
              Just Refl -> c :=> v)
          vals
          foo
        alph = alphabet $ syntacticAutomaton intrpr
        foo = case Set.toList $ flip Set.filter alph \case
          SymInteract (Out _) _ -> False
          SymInteract (In i) _ -> i == gate of
            [SymInteract _ vs] -> vs
            _ -> error $ "zero or more than one inputs in the alphabet match " <> show gate

-- {- |
--     Create a 'TestObserver'.
-- -}
-- observer :: s -> (s -> AutIntrpr m loc q t tdest act -> act -> m q -> IO s) -> (s -> IO r) -> TestObserver m loc q t tdest act s r
-- observer state upd finish = TestController {
--     testControllerState = state,
--     selectTest = \s _ _ -> return $ Left ((), s), -- no state change, continue testing
--     updateTestController = \s aut act q -> Left <$> upd s aut act q,
--     handleTestClose = finish
--     }
--
-- type STSIntrp m loc g = AutIntrpr m loc (IntrpState loc) (SymInteract g) STStdest (GateValue g)
