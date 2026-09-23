{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Lattest.Exec.StandardTestControllers.CompleteTestSuite (
accessSeqSelector,
adgTestSelector,
nCompleteSingleState,
runNCompleteTestSuite,
randomCoveringTestSelector,
randomCoveringTestSelectorFromGen
)
where
import Lattest.Adapter.Adapter(Adapter,close)
import Lattest.Adapter.StandardAdapters(withQuiescenceMillis)
import Lattest.Exec.ADG.Aut(adgAutFromAutomaton)
import Lattest.Exec.ADG.DistGraph(computeAdaptiveDistGraph)
import Lattest.Exec.ADG.SplitGraph(Evidence(..))
import Lattest.Exec.StandardTestControllers(andThen,randomTestSelectorFromSeed,untilCondition,stopAfterSteps,observingOnly,printActions,traceObserver,andObserving,stateObserver, TestSelector, selector, solveRandomInput)
import Lattest.Exec.Testing(TestController(..), runTester,Verdict)
import Lattest.Model.Alphabet(IOAct(..), IOSuspAct, Suspended(..), asSuspended, SymInteract (..), IOSymInteract, IOGateValue, GateValue)
import Lattest.Model.Automaton(AutIntrpr(..),AutSyntax (..), after, After, asLoc, TransitionMapping (..), allLocations, STStdest, IntrpState)
import Lattest.Model.BoundedMonad(Det(..), BoundedConfiguration (..), asConjunction, FreeLattice)
import Lattest.Model.StandardAutomata(ConcreteSuspAutIntrpr, accessSequences, interpretQuiescentConcrete)

import Control.Monad (forM, (>=>))
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Random(StdGen, initStdGen)
import Data.Maybe (fromMaybe)

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

{- |
    Compute the set of transitions covered by a trace.
    Currently hardcoded to m ~ FreeLattice.
    The m ~ Det case is easier, will probably just need to make a typeclass to support it.

    For disjunctions: currently giving an easy lower bound (Just only count transitions that don't originate from a disjunction).
    Giving the largest lower bound is hard: Ideally, you want to 'backpropagate' information on which transitions were covered.

    E.g: from A \/ B, take transition 'x' (A->C,B->D) to C \/ D, then take transition 'y' which is forbidden from C but allowed from D
    We currently don't report any of these as covered, but would report the next transition from D as covered.
    It should be easy to report [(D, y)], though making this compositional (across arbitrary conjunction of disjunctions) might be annoying.
    It seems hard but sound to report [(B,x),(D,y)]: the second transition gave information about the first one.
 -}
covered :: (Ord q, Ord loc, After FreeLattice loc q t tdest act, Ord act, Show t, Show act)
        => AutIntrpr FreeLattice loc q t tdest act
        -> [act]
        -> Set.Set (loc, t)
covered _ [] = mempty
covered intrpr (act:trace)
  | isForbidden (stateConf intrpr) = mempty
  | isUnderspecified (stateConf intrpr) = mempty
  | Left _ <- asConjunction (stateConf intrpr) = covered (after intrpr act) trace -- conservative lower bound
  | Right conj <- asConjunction (stateConf intrpr) = let
      aft = after intrpr act
      in case asTransition (alphabet (syntacticAutomaton intrpr)) act of
        Just t -> Set.union (Set.map ((, t) . asLoc) conj ) $ covered aft trace
        Nothing -> error $ "asTransition failed in `covered`: act outside of alphabet? Act: " <> show act <> ", alphabet: " <> show (alphabet (syntacticAutomaton intrpr))

-- | All transitions syntactically present: for computing the target of coverage checking
fullCoverageTarget :: (Ord loc, After FreeLattice loc q t tdest act)
        => AutIntrpr FreeLattice loc q t tdest act
        -> Set.Set (loc, t)
fullCoverageTarget intrpr = let
  syn = syntacticAutomaton intrpr
  locs = allLocations syn
  in Set.unions $ Set.map (\l -> Set.fromList $ map (l,) $ Map.keys $ transRel syn l) locs

-- The most basic version: randomly pick an uncovered input, if any, and otherwise just random
-- If a 'to cover' set is not provided, it gets initialized to the set of every transition
-- Using 'observeControllerState', the set of uncovered transitions can be passed on to the next test.
randomCoveringTestSelector
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Ord act, Ord i', Ord o, Ord q, Ord loc, Show t, Show act
     , tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (loc, t))
  -> IO (TestSelector m loc q t tdest act (StdGen, Set.Set (loc, t), [act], m q) i)
randomCoveringTestSelector intrpr mtocover = randomCoveringTestSelectorFromGen intrpr mtocover <$> initStdGen

randomCoveringTestSelectorFromGen
  :: forall m loc q t tdest act i' o i.
     (After m loc q t tdest act, Ord act, Ord i', Ord o, Ord q, Ord loc, Show t, Show act
     , tdest ~ STStdest, m ~ FreeLattice, t ~ IOSymInteract i' o, q ~ IntrpState loc, act ~ IOGateValue i' o, i ~ GateValue i') -- hardcoding to STS
  => AutIntrpr m loc q t tdest act
  -> Maybe (Set.Set (loc, t))
  -> StdGen
  -> TestSelector m loc q t tdest act (StdGen, Set.Set (loc, t), [act], m q) i
randomCoveringTestSelectorFromGen intrpr mtocover g = selector (g, fromMaybe (fullCoverageTarget intrpr) mtocover, [], stateConf intrpr) select update
  where
    select (g', tocover, trace, _) intrpr' mq = do
      -- as in randomDataTestSelectorFromGen, except we try to take new transitions
      (maybeGateValue, g'') <- solveRandomInput @FreeLattice g' maybeNewInAct intrpr'
      case maybeGateValue of
        Just value -> pure $ Just (value, (g'',tocover,trace, mq))
        Nothing -> do
          (maybeGateValue', g''') <- solveRandomInput g'' maybeNewInAct intrpr'
          return $ case maybeGateValue' of
            Just value -> Just (value, (g''',tocover,trace, mq))
            Nothing -> Nothing
      where
        maybeFromIOAct (SymInteract io xs) = case io of
          In i -> Just $ SymInteract i xs
          Out _ -> Nothing
        maybeNewInAct = maybeFromIOAct >=> \(SymInteract i xs) -> case asConjunction mq of
          -- The state has disjunction, so we're not covering any new transitions anyway.
          -- Just take a random transition.
          Left _ -> Just $ SymInteract i xs
          -- The actual filtering:
          Right qs -> if any (\q -> (asLoc q, SymInteract (In i) xs) `Set.member` tocover) qs
            then Just $ SymInteract i xs
            else Nothing

    -- note: the intrpr we get here is _after_ the transition, but we need the `m q` before the transition
    -- to compute coverage. That's why we keep track of it in the quadruple.
    update (g', tocover, trace, mq) intrpr' act _ = let newcover = covered (intrpr' {stateConf = mq}) [act]
      in pure $ Just (g', tocover Set.\\ newcover, trace ++ [act], stateConf intrpr')

