{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

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

import Lattest.Exec.Testing(TestController(..))
import Lattest.Model.Alphabet(TestChoice, IOAct(..), IOSuspAct, Suspended(..), asSuspended, actToChoice)
import Lattest.Model.Automaton(AutIntrpr(..), StepSemantics, TransitionSemantics, FiniteMenu, specifiedMenu, stateConf)
import Lattest.Model.BoundedMonad(isConclusive, BoundedConfiguration)
import Lattest.Util.Utils(takeRandom, takeJusts)

import Data.Either(isLeft)
import Data.Either.Combinators(leftToMaybe, maybeToLeft)
import Data.Foldable(toList)
import qualified Data.Map as Map (keys)
import qualified Data.Set as Set (size, elemAt, fromList, union)
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

{-
TODO open an SMT connection. Snippet from TxsCore:
let cfg    = IOC.config envc
                   smtLog = Config.smtLog cfg
                   -- An error will be thrown if the selected solver is not in
                   -- the list of available solvers. The sanity of the
                   -- configuration is checked outside this function, however
                   -- nothing prevents a client of this function from injecting
                   -- a wrong configuration. A nicer error handling requires
                   -- some refactoring of the TorXakis core to take this into
                   -- account.
                   smtProc = fromJust (Config.getProc cfg)
               smtEnv         <- lift $ SMT.createSMTEnv smtProc smtLog
               (info,smtEnv') <- lift $ runStateT SMT.openSolver smtEnv
               (_,smtEnv'')   <- lift $ runStateT (SMT.addDefinitions (SMTData.EnvDefs (TxsDefs.sortDefs tdefs) (TxsDefs.cstrDefs tdefs) (Set.foldr Map.delete (TxsDefs.funcDefs tdefs) (allENDECfuncs tdefs)))) smtEnv'
-}
