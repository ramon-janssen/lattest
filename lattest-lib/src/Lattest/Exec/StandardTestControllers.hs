{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
    This module contains building blocks for constructing out-of-the-box 'TestController's.
    
    'TestController's have multiple duties during testing:
    
    * selecting test inputs,
    * deciding whether to continue testing,
    * returning testing results (other than 'Pass' or 'Fail'), and
    * potentially performing side effects during testing.
    
    The building blocks in this module allow composing 'TestController's in a modular way, by combining various choices for these responsibilities.
    Every building block carries its own state. For example, to stop testing after a fixed number of steps, a state in the form of a counter is
    needed, whereas returning the observed trace as test result requires recording the observed trace as state.
-}

module Lattest.Exec.StandardTestControllers (
-- * Test Selectors
selector,
TestSelector,
randomTestSelector,
randomTestSelectorFromSeed,
randomTestSelectorFromGen,
accessSeqSelector,
adgTestSelector,
nCompleteSingleState,
runNCompleteTestSuite,
andThen,
-- * Stop Conditions
StopCondition,
stopCondition,
untilCondition,
stopAfterSteps,
-- * Test Observers
TestObserver,
observer,
andObservingWith,
andObserving,
observingOnly,
traceObserver,
stateObserver,
inconclusiveStateObserver,
-- * Test Side Effects
TestSideEffect,
withSideEffect,
testSideEffect,
printActions,
printState
)
where
import Lattest.Adapter.Adapter(close)
import Lattest.Adapter.StandardAdapters(Adapter,connectJSONSocketAdapterAcceptingInputs,withQuiescenceMillis)
import Lattest.Exec.ADG.Aut(adgAutFromAutomaton)
import Lattest.Exec.ADG.DistGraphConstruction(computeAdaptiveDistGraphPure)
import Lattest.Exec.ADG.SplitGraph(Evidence(..))
import Lattest.Exec.Testing(TestController(..), runTester,Verdict)
import Lattest.Model.Alphabet(TestChoice, IOAct(..), IOSuspAct, Suspended(..), asSuspended, actToChoice, isInput)
import Lattest.Model.Automaton(AutIntrpr(..), StepSemantics, TransitionSemantics, FiniteMenu, specifiedMenu, stateConf, SyntaxDestStates,AutSyntax,syntacticAutomaton)
import Lattest.Model.StandardAutomata(ConcreteSuspAutIntrpr(..), accessSequences, ConcreteAutIntrpr, interpretQuiescentConcrete)
import Lattest.Model.BoundedMonad(isConclusive, BoundedConfiguration,Det(..))
import Lattest.Util.Utils(takeRandom, takeJusts)

import Control.DeepSeq(NFData)
import Data.Either(isLeft)
import Data.Either.Combinators(leftToMaybe, maybeToLeft)
import Data.Foldable(toList, forM_)
import Control.Monad (forM)
import qualified Data.Map as Map (keys, (!))
import qualified Data.Set as Set (size, elemAt, fromList, union, empty, Set, singleton)
import System.Random(RandomGen, StdGen, initStdGen, mkStdGen, uniformR)

{- |
    'Testselector's are test controllers that are only concerned with selecting inputs for testing. They do not return any testing results.
-}
type TestSelector m loc q t tdest act s i = TestController m loc q t tdest act s i ()

{- |
    Create a 'TestSelector'. Requires one function to select an input, also updating the state, and one function to update the state when observing
    an action.
-}
selector :: TestChoice i act =>
    state ->
    (state -> AutIntrpr m loc q t tdest act -> m q -> IO (Maybe (i, state))) ->
    (state -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (Maybe state)) ->
    TestSelector m loc q t tdest act state i
selector state sel upd = TestController {
    testControllerState = state,
    selectTest = \s aut mq -> maybeToLeft () <$> sel s aut mq,
    updateTestController = \s aut act mq -> maybeToLeft () <$> upd s aut act mq,
    handleTestClose = const $ return ()
    }

-- TODO introduce a combinator that adds the 'selector' behaviour to an arbitrary TestController. This is not needed if the selector is always 
-- taken as a basis to combine with stop conditions / test observers, but it would be more flexible to allow turning a composition around.

{- |
    A 'TestSelector' that picks inputs uniformly pseudo-randomly from the outgoing transitions from the current state configuration.
-}
randomTestSelector :: (StepSemantics m loc q t tdest act, FiniteMenu t act, Foldable m, TestChoice i act)
    => IO (TestSelector m loc q t tdest act StdGen i)
randomTestSelector = initStdGen >>= return . randomTestSelectorFromGen

{- |
    A 'TestSelector' that picks inputs uniformly pseudo-randomly from the outgoing transitions from the current state configuration, starting with
    the given random seed.
-}
randomTestSelectorFromSeed :: (StepSemantics m loc q t tdest act, FiniteMenu t act, Foldable m, TestChoice i act)
    => Int -> TestSelector m loc q t tdest act StdGen i
randomTestSelectorFromSeed i = randomTestSelectorFromGen $ mkStdGen i

{- |
    A 'TestSelector' that picks inputs uniformly pseudo-randomly from the outgoing transitions from the current state configuration, based on the
    given random generator.
-}
randomTestSelectorFromGen :: (StepSemantics m loc q t tdest act, FiniteMenu t act, Foldable m, TestChoice i act, RandomGen g)
    => g -> TestSelector m loc q t tdest act g i
randomTestSelectorFromGen g = selector g randomSelectTest (\s _ _ _ -> return $ Just s)
    where
    randomSelectTest g aut _ =
        let ins = takeJusts $ actToChoice <$> specifiedMenu aut
        in if null ins
            then error "random test selector found an empty menu"
            else return $ Just $ takeRandom g ins

--Result Bool is True when access sequence has been followed and false when the SUT deviated
-- accessSeqSelector :: (Ord q, Eq i, Eq o) => ConcreteSuspAutIntrpr Det q i o -> q -> q -> TestController Det q q (IOAct i o) () (IOAct i o) [IOAct i o] (Maybe (IOAct i o)) Bool
accessSeqSelector :: (Ord q, Eq i, Eq o, Show i, Show o) => ConcreteSuspAutIntrpr Det q i o -> q -> TestController Det q q (IOAct i o) () (IOSuspAct i o) [IOAct i o] (Maybe i) Bool
accessSeqSelector aut targetLoc =
    let initLoc = case stateConf aut of
            Det q -> q
            _ -> error "Access sequence: model must be in a specified initial state"
        accSeqs = accessSequences aut initLoc
    in TestController {
        testControllerState = (Map.!) accSeqs targetLoc,
        selectTest = accSeqSelectTest,
        updateTestController = accSeqUpdateTest,
        handleTestClose = \testState -> return $ case testState of [] ->  True; _ -> False
    }
    where
    accSeqSelectTest [] specIntrpState _ = return $ Right True
    accSeqSelectTest (l:ls) specIntrpState _ = return $ case l of
        In i -> Left (Just i, (l:ls))
        _ -> Left (Nothing, (l:ls))
    accSeqUpdateTest [] specIntrpState label _ = return $ Right True
    accSeqUpdateTest (l:ls) specIntrpState label _ = return $ if (asSuspended l) == label then Left ls else Right False



adgTestSelector :: (Ord q, Ord l, Eq l, NFData q, NFData l, Show l) => ConcreteSuspAutIntrpr Det q l l -> l ->  TestController Det q q (IOAct l l) () (IOSuspAct l l) (Evidence l) (Maybe l) (Set.Set q)
adgTestSelector aut delta =
    let adgaut = case adgAutFromAutomaton aut delta of
                    Just a -> a
                    Nothing ->  error "could not transform Lattest auomaton into ADG automaton"
        adg = computeAdaptiveDistGraphPure adgaut False False True
    in TestController {
        testControllerState = adg,
        selectTest = adgSelectTest,
        updateTestController = adgUpdateTest,
        handleTestClose = \testState -> return Set.empty
    }
    where
    adgSelectTest testState specIntrpState _ =
        return $ case testState of
            Nil -> Right Set.empty
            Prefix l next -> Left (Just l, testState)
            Plus _ -> Left (Nothing,testState)

    adgUpdateTest testState specIntrpState ioact _ =
       return $ case testState of
            Nil -> Right Set.empty
            Prefix l next -> if ioact == In l then Left next else error "Error: expected to have selected an input but seeing some ioact"
            Plus ls ->
                let nextList = concat $ fmap getNextState ls
                in case nextList of
                    [next] -> Left next
                    _ -> error "ADG error: expected to have observed one output or quiescence"
                where
                getNextState ev = case ev of
                    Nil -> []
                    Prefix l next -> if l == delta
                                        then if ioact == Out Quiescence then [next] else []
                                     else if ioact == Out (OutSusp l) then [next] else []
                    Plus ls -> concat $ fmap getNextState ls

-- nCompleteSingleState :: ConcreteSuspAutIntrpr Det q l l -> Int -> Int -> l -> q -> TestController Det q q (IOAct l l) () (IOSuspAct l lo) (Maybe (Det q)) () (Maybe (Det q))
nCompleteSingleState model seed nrSteps delta targetState observer = do
    return $ accessSeqSelector model targetState
        `andThen` randomTestSelectorFromSeed seed `untilCondition` stopAfterSteps nrSteps
            `andThen` adgTestSelector model delta `observingOnly` observer

-- runNCompleteTestSuite :: (Monad (TestController Det q q (IOAct l l) () (IOSuspAct l l) () (Maybe l))) => IO (Adapter act l) -> ConcreteSuspAutIntrpr Det q l l -> Int -> o -> [(q,Int)] -> IO (q, Verdict, Maybe (Det q))
runNCompleteTestSuite adapter spec nrSteps delta targetStatesAndSeeds = do
        results <- forM targetStatesAndSeeds $ \(targetState,seed) -> do
            putStrLn $ "connecting..."
            adap <- adapter
            imp <- withQuiescenceMillis 200 adap
            let model = interpretQuiescentConcrete spec
            putStrLn $ "starting test..."
            putStrLn $ "accessing state: " ++ (show targetState)
            (verdict,result) <- runTester model (testSelector model seed targetState) imp
            close adap
            return (targetState, verdict, result)
        return results
    where testSelector model seed targetState = nCompleteSingleState model seed nrSteps delta targetState $ printActions `observingOnly` traceObserver `andObserving` stateObserver

andThen :: (TestChoice i act) => TestController m loc q t tdest act state1 i r1 -> TestController m loc q t tdest act state2 i r2 -> TestController m loc q t tdest act (Either state1 state2) i r2
andThen tester1 tester2 =
    TestController {
        testControllerState = (Left $ testControllerState tester1),
        selectTest = andThenSelect,
        updateTestController = andThenUpdate,
        handleTestClose = \state -> case state of
            (Left s) -> handleTestClose tester2 (testControllerState tester2)
            (Right s) -> handleTestClose tester2 s
    }
    where
        andThenSelect testState specState mq = case testState of
            (Left s) -> do
                res <- selectTest tester1 s specState mq
                res2 <- selectTest tester2 (testControllerState tester2) specState mq
                return $ case res of
                    Left (i1,s1) -> Left (i1, Left s1)
                    Right r1 -> case res2 of
                        Left (i2,s2) -> Left (i2, Right s2)
                        Right r2 -> Right r2
            (Right s) -> do
                res2 <- selectTest tester2 s specState mq
                return $ case res2 of
                    Left (i2,s2) -> Left (i2, Right s2)
                    Right r2 -> Right r2

        andThenUpdate testState specState ioact mq = case testState of
            Left s -> do
                res1 <- updateTestController tester1 s specState ioact mq
                return $ case res1 of
                    Left s1 ->  Left $ Left s1
                    Right r1 -> Left $ Right $ testControllerState tester2
            Right s -> do
                res2 <- updateTestController tester2 s specState ioact mq
                return $ case res2 of
                    Left s2 ->  Left $ Right s2
                    Right r2 -> Right r2



{- |
    'StopCondition's are test controllers that are only concerned with deciding whether to continue testing after observing an action. They do not
    select inputs or return any testing results.
-}
type StopCondition m loc q t tdest act s = TestController m loc q t tdest act s () ()

{- |
    Create a state-based stop condition, starting in the given initial state. The provided function should provide either 'Just' a new state to continue
    testing, or 'Nothing' to stop testing.
-}
stopCondition :: s -> (s -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (Maybe s)) -> StopCondition m loc q t tdest act s
stopCondition state upd = TestController {
    testControllerState = state,
    selectTest = \s _ _  -> return $ Left ((), s), -- no state change, continue testing
    updateTestController = \s aut act q -> do
        maybeS' <- upd s aut act q
        case maybeS' of
            Just s' -> return $ Left s'
            Nothing -> return $ Right (),
    handleTestClose = const $ return ()
    }

{- |
    Apply a stop condition: run the (first) test controller until it returns a result, or until the stop condition is reached. The selected inputs and returned result come from the test controller.
-}
untilCondition :: TestController m loc q t tdest act state1 i1 r1 -> TestController m loc q t tdest act state2 i2 r2 -> TestController m loc q t tdest act (state1,state2) i1 r1
untilCondition controller condition = TestController {
    testControllerState = (testControllerState controller, testControllerState condition),
    selectTest = \s aut mq -> do
        next <- selectTest controller (fst s) aut mq
        return $ case next of
            Left (i,s') -> Left (i,(s',snd s))
            Right r -> Right r,
    updateTestController = \s aut act q -> do
        stateOrResult <- updateTestController controller (fst s) aut act q
        maybeCondState <- updateStopCondition condition (snd s) aut act q
        case stateOrResult of
            Left state -> case maybeCondState of
                Just condState -> return $ Left (state, condState)
                Nothing -> Right <$> handleTestClose controller state
            Right result -> return $ Right result,
    handleTestClose = \s -> handleTestClose controller (fst s)
    }
    where
    updateStopCondition :: TestController m loc q t tdest act state i r -> state -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (Maybe state)
    updateStopCondition condition state aut act q = updateTestController condition state aut act q >>= return . leftToMaybe


{- |
    Observe a fixed number of actions, and then stop testing.
    
    Note: since stop conditions only decide whether to stop testing after observing an action, the minimum number of actions to observe is 1.
-}
stopAfterSteps :: Int -> StopCondition m loc q t tdest act Int
stopAfterSteps n = stopCondition n (\n' _ _ _ -> return $ if n' <= 1 then Nothing else Just (n'-1))

{- |
    'TestObserver's are only concerned with returning a result after testing. They do not select inputs or decide whether to continue testing.
-}
type TestObserver m loc q t tdest act s r = TestController m loc q t tdest act s () r

{- |
    Create a 'TestObserver'.
-}
observer :: s -> (s -> AutIntrpr m loc q t tdest act -> act -> m q -> IO s) -> (s -> IO r) -> TestObserver m loc q t tdest act s r
observer state upd finish = TestController {
    testControllerState = state,
    selectTest = \s _ _ -> return $ Left ((), s), -- no state change, continue testing
    updateTestController = \s aut act q -> Left <$> upd s aut act q,
    handleTestClose = finish
    }

{- |
    Apply an observer: Use the (former) test controller, but also returning the result of the (latter) observer. Combine the two results using the given function.
-}
andObservingWith :: TestController m loc q t tdest act state1 i1 r1 -> (r1 -> r2 -> r) -> TestController m loc q t tdest act state2 i2 r2 -> TestController m loc q t tdest act (state1,state2) i1 r
andObservingWith controller f obs = TestController {
    testControllerState = (testControllerState controller, testControllerState obs),
    selectTest = \s aut mq -> do
        next <- selectTest controller (fst s) aut mq
        case next of
            Left (i,s') -> return $ Left (i,(s',snd s))
            Right r1 -> do
                r2 <- handleTestClose obs (snd s)
                return $ Right $ f r1 r2,
    updateTestController = \s aut act q -> do
        stateOrResult1 <- updateTestController controller (fst s) aut act q
        stateOrResult2 <- updateTestController obs (snd s) aut act q
        case stateOrResult1 of
            Left s1 -> case stateOrResult2 of
                Left s2 -> return $ Left (s1, s2)
                Right r2 -> do
                    r1 <- handleTestClose controller s1
                    return $ Right $ f r1 r2
            Right r1 -> case stateOrResult2 of
                Left s2 -> do
                    r2 <- handleTestClose obs s2
                    return $ Right $ f r1 r2
                Right r2 -> return $ Right $ f r1 r2,
    handleTestClose = \(s1,s2) -> do
        r1 <- handleTestClose controller s1
        r2 <- handleTestClose obs s2
        return $ f r1 r2
    }

{- |
    Apply an observer: use the (former) test controller, but also returning the result of the (latter) observer in a tuple.
-}
andObserving :: TestController m loc q t tdest act state1 i1 r1 -> TestController m loc q t tdest act state2 i2 r2 -> TestController m loc q t tdest act (state1,state2) i1 (r1,r2)
andObserving controller = andObservingWith controller (,)

{- |
    Apply an observer: use the (former) test controller, but only return the result of the (latter) observer.
-}
observingOnly :: TestController m loc q t tdest act state1 i1 r1 -> TestController m loc q t tdest act state2 i2 r2 -> TestController m loc q t tdest act (state1,state2) i1 r2
observingOnly controller = andObservingWith controller (\r1 r2 -> r2)

{- |
    A 'TestObserver' that returns the trace of all observed actions
-}
traceObserver :: TestObserver m loc q t tdest act [act] [act]
traceObserver = observer [] (\trace _ act _ -> return $ act : trace) (pure . reverse)

-- FIXME get rid of the Maybe
{- |
    A 'TestObserver' that returns the last state configuration of the specification model. This may be a conclusive state. For example,
    during a failed test, this observer returns 'forbidden'.
-}
stateObserver :: TestObserver m loc q t tdest act (Maybe (m q)) (Maybe (m q))
stateObserver = observer Nothing (\_ aut _ _ -> return $ Just (stateConf aut)) return

{- |
    A 'TestObserver' that returns the last inconclusive state configuration of the specification model. For example, during a failing test,
    this observer returns the last state before the failure.
    
-}
inconclusiveStateObserver :: BoundedConfiguration m => TestObserver m loc q t tdest act (Maybe (m q)) (Maybe (m q))
inconclusiveStateObserver = observer Nothing makeSelection return
    where
    makeSelection _ aut _ mq =
        let mq' = stateConf aut
        in return $ Just $ if isConclusive mq' then mq else mq'

{- |
    'TestSideEffect's perform side effects during testing, but have no impact on the testing itself, nor on the result.
-}
type TestSideEffect m loc q t tdest act s = TestController m loc q t tdest act s () ()

{- |
    Apply a side effect: Use the (former) test controller, but also perform the side effect of the (latter) observer.
-}
withSideEffect :: TestController m loc q t tdest act state1 i1 r1 -> TestController m loc q t tdest act state2 i2 r2 -> TestController m loc q t tdest act (state1,state2) i1 r1
withSideEffect controller sideEffect = andObservingWith controller const sideEffect


{- |
    Create a 'TestSideEffect'. The provided function returns the new state in an 'IO' monad that can also perform the side effects.
-}
testSideEffect :: s -> (s -> AutIntrpr m loc q t tdest act -> act -> m q -> IO s) -> TestSideEffect m loc q t tdest act s
testSideEffect s f = observer s f (const $ pure ())

{- |
    Print observed to stdin actions during testing.
-}
printActions :: Show act => TestSideEffect m loc q t tdest act ()
printActions = testSideEffect () (\_ _ act _ -> putStrLn $ show act)

{- |
    Print the state configuration of the specification during testing.
-}
printState :: Show (m q) => TestSideEffect m loc q t tdest act ()
printState = testSideEffect () (\_ _ _ mq -> putStrLn $ show mq)
