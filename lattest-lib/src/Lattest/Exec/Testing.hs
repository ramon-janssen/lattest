{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{- |
    This module contains the main functions and data structures to run experiments against (external) systems, specifically testing
    experiments.

    For an experiment, we assume that we have an 'Adapter', which serves as an interface to send inputs to a system under test,
    and observe actions shown by that system. The experiment is controlled by an 'ActionController'. Specifically for a testing
    experiment, we can create an 'ActionController' from a specification model that dictates which observations are allowed and
    forbidden, and a 'TestController' that steers the testing.

    To get started with testing experiments quickly, use the 'runTester' function, and to get the required ingredients, see the following modules:

    * "Lattest.Adapter.StandardAdapters" to create adapters,
    * "Lattest.Exec.StandardTestControllers" to create test controllers, and
    * "Lattest.Model.StandardAutomata" to create specification models.
-}

module Lattest.Exec.Testing (
-- * Generic Experiments
-- | Can be used to let an action controller communicate with a system under test, resulting in some arbitrary result.
ActionController(..),
runExperiment,
-- * Testing Experiments
{- |
    Specific form of experiments, in which an automaton specification model describes the intended behaviour that the system under
    test should adhere to, and the test controller sends inputs to observe whether the system under test actually conforms to that
    specification model.
    
    This is also known as /Model based testing/, see e.g.
    
    * [/Jan Tretmans/, Model based testing with labelled transition systems (Formal Methods and Testing), 2008](https://repository.ubn.ru.nl/bitstream/handle/2066/72680/72680.pdf)
-}
TestController(..),
makeTester,
RunTester(..),
runLTSTester,
runSTSTester,
Verdict(..),
InconclusiveReason(..)
)
where

import Lattest.Model.Alphabet(TestChoice, IOAct, IOSymInteract)
import Lattest.Model.Automaton ( StepSemantics,StepSemantics, AutIntrpr, After, IOAfter, ioAfter, stateConf, AutomatonException, STStdest, sanityCheckLTS,sanityCheckSTS, Act, Q, Tdest, T, Foo, TCI)
import Lattest.Model.BoundedMonad(isConclusive, isForbidden)
import Lattest.Adapter.Adapter(Adapter(..), send, tryObserve)


import Control.Exception(catch,evaluate)

--import Control.DeepSeq(force)
import Lattest.Streams.Synchronized (Streamed(..))
import Data.Kind (Constraint, Type)

-- | The controller of an experiment.
data ActionController act i r state = ActionController {
    -- | Any state that the controller needs for its decision making duties.
    controllerState :: state,
     -- | Select an input and compute the new state, /or/ decide to stop the experiment and return a result.
    select :: state -> IO (Either (i, state) r),
    -- | Provided an observed action, compute the new state /or/ stop the experiment and return a result.
    update :: state -> act -> IO (Either state r),
    -- | Handle the end of the action stream, i.e. the other end closing, ending the experiment.
    handleClose :: state -> IO r
    }

-- | The verdict resulting from a testing experiment: did the system under test pass the test?
data Verdict = Pass | Fail | Inconclusive InconclusiveReason deriving (Ord, Eq, Show)

-- | In case of an inconclusive verdict, details on why the test is inconclusive
data InconclusiveReason = AutomatonException AutomatonException | OutputNotInOfflineTest deriving (Ord, Eq, Show)

{- |
    The controller of a testing experiment. The tester may return a result at the end of a testing experiment. Note that it does
    /not/ need to return a verdict 'Pass' or 'Fail', this verdict is automatically inferred based on the specification model.
    Results can be used to record additional information that the tester is interested in, depending on the controller implementation.
    For example, the actions observed during a testing experiment, or whether certain coverage criteria were achieved during the experiment.
-}
data TestController m loc i o foo state r = TestController {
    -- | Any state that the controller needs for its decision making duties.
    testControllerState :: state,
    {- |
        Select a test based on test controller state, the specification (in its current state), and previous specification configuration.
        Either select a new controller state and a input, /or/ stop testing and return a result from the controller.
    -}
    selectTest :: (TestChoice (TCI foo i) (Act foo i o)) => state -> AutIntrpr m loc i o foo -> m (Q foo loc) -> IO (Either (TCI foo i, state) r),
    {- |
        Handle a transition. Passes the intrpr after the transition, and its state configuration before the transition.
    -}
    updateTestController :: state -> AutIntrpr m loc i o foo -> Act foo i o -> m (Q foo loc) -> IO (Either state r),
    -- | Handle the end of the action stream, i.e. the other end closing, ending the experiment.
    handleTestClose :: state -> IO r
    }

{- |
    From a test controller and a specification model, create an action controller. The test controller is used to decide which inputs
    are supplied to the system under test, and whether to continue or stop testing. The automaton specification model is used to infer whether
    observed actions are allowed or not, and to return a verdict in case of forbidden or underspecified observations.
-}
makeTester :: forall m loc q t tdest act i o foo state r. (IOAfter m loc foo i o tdest, StepSemantics m loc q t tdest act, TestChoice (TCI foo i) act, Foo foo q t tdest act loc i o) =>
    AutIntrpr m loc i o foo -> TestController m loc i o foo state r -> ActionController act (TCI foo i) (Verdict, r) (AutIntrpr m loc i o foo, TestController m loc i o foo state r)
makeTester initSpec initTestController = ActionController {
    controllerState = (initSpec, initTestController),
    select = makeSelect,
    update = makeUpdate,
    handleClose = makeHandleClose
    }
    where
        makeSelect :: (AutIntrpr m loc i o foo, TestController m loc i o foo state r)
                   -> IO (Either (TCI foo i, (AutIntrpr m loc i o foo, TestController m loc i o foo state r)) (Verdict, r))
        makeSelect (spec, testController) = do
            next <- selectTest testController (testControllerState testController) spec (stateConf spec)
            case next of
                Right r -> return $ Right (pToVerd $ stateConf spec, r)
                Left (i, state') -> return $ Left (i, (spec, testController { testControllerState = state' }))
        makeUpdate :: (AutIntrpr m loc i o foo, TestController m loc i o foo state r)
                   -> act
                   -> IO (Either (AutIntrpr m loc i o foo, TestController m loc i o foo state r) (Verdict, r))
        makeUpdate (spec, testController) act = do
            spec' <- ioAfter spec act
            confOrAutomatonException <- catchAutomatonException $ stateConf spec'
            case confOrAutomatonException of
                Left conf' -> do
                    let verdict = pToVerd conf'
                    next <- updateTestController testController (testControllerState testController) spec' act (stateConf spec)
                    case next of
                        Right r -> return $ Right (verdict, r)
                        Left state' -> if isConclusive conf' || verdict == Fail
                            then do
                                r <- handleTestClose testController state'
                                return $ Right (verdict, r)
                            else return $ Left (spec', testController { testControllerState = state' })
                Right e -> do
                    r <- handleTestClose testController (testControllerState testController)
                    return $ Right (Inconclusive $ AutomatonException e, r)
        makeHandleClose :: (AutIntrpr m loc i o foo, TestController m loc i o foo state r) -> IO (Verdict, r)
        makeHandleClose (spec, testController) = do
            r <- handleTestClose testController (testControllerState testController)
            return (pToVerd $ stateConf spec, r)
        pToVerd :: m x -> Verdict
        pToVerd p | isForbidden p = Fail
                  | otherwise     = Pass

catchAutomatonException :: a -> IO (Either a AutomatonException)
catchAutomatonException a = (Left <$> evaluate a) `catch` (return . Right)

{- |
    Run an experiment by interacting with the given adapter, controlled by the given action controller. The experiment
    stops when the action controller decides to. Returns the result returned by the action controller.
-}
runExperiment :: ActionController act i r state -> Adapter act i -> IO r
runExperiment controller adapter = do
    streamedAction <- tryObserve adapter
    stateOrResult <- case streamedAction of
        Available action -> handleUpdate action
        Unavailable -> handleSelect
        StreamClosed -> handleClosed
    case stateOrResult of
        Left state -> runExperiment (controller { controllerState = state }) adapter
        Right result -> return result
    where
    handleUpdate = update controller (controllerState controller)
    handleSelect = do
        selection <- select controller (controllerState controller)
        case selection of
            Left (inputCmd, state) -> do
                 -- TODO if an action is ready *after computing the input command* (because race condition between the adapter and controller), maybe don't send the input command.
                send inputCmd adapter
                return $ Left state
            Right result -> return $ Right result
    handleClosed = Right <$> handleClose controller (controllerState controller)


{- |
    This typeclass provides 'runTester', a way to conveniently run testing experiments.
    It has instances for STSs and LTSs.
-}
class RunTester tdest where
  -- | A constraint synonym for the constraints of 'runTester'.
  --   This allows each instance to have different constraints.
  -- TODO: remove i' (which is either i or Maybe i), let 'foo' handle that
  type RunnableTester (m :: Type -> Type) loc i o i' tdest foo :: Constraint

  {- |
      Running a tester requires:

      * a specification model in the form of an automaton, as defined in "Lattest.Model.Automaton"
      * a 'TestController', defined in this module itself, and
      * an adapter, as defined in "Lattest.Adapter.Adapter".

      Running a testing experiment is done by interacting with the given adapter, controlled by the given test controller. The experiment
      stops when the action controller decides to, or when an observation is made that is forbidden or underspecified according
      to the specification model. Returns the test verdict according to the specification model and the additional
      result returned by the test controller.
  -}
  runTester
    :: RunnableTester m loc i o i' tdest foo
    => AutIntrpr m loc i o foo
    -> TestController m loc i' o foo state r
    -> Adapter (Act foo i o) i'
    -> IO (Verdict, r)

instance RunTester () where
  type RunnableTester m loc i o i' () foo = (i ~ i', Tdest foo ~ (), T foo i o ~ IOAct i o, After m loc foo i o, TestChoice i' (Act foo i o), Ord loc, Ord (Q foo loc), Ord (m (Q foo loc)), Show i, Show o, Show loc, Show (T foo i o), Show (m ((),loc)), Foldable m, i' ~ TCI foo i)
  runTester intrpr
    | not (sanityCheckLTS intrpr) = error "check failed"
    | otherwise = runLTSTester intrpr

instance RunTester STStdest where
  type RunnableTester m loc i o i' STStdest foo = (i ~ i', Tdest foo ~ STStdest, T foo i o ~ IOSymInteract i o, IOAfter m loc foo i o (Tdest foo), StepSemantics m loc (Q foo loc) (T foo i o) STStdest (Act foo i o), Show loc, Show i, Show o, Show (m (STStdest, loc)), Ord loc, Foldable m, TestChoice i' (Act foo i o), i' ~ TCI foo i)
  runTester intrpr
    | not (sanityCheckSTS intrpr) = error "check failed"
    | otherwise = runSTSTester intrpr

{- |
    runTester specialized to LTS models, and without running the sanity checks.
-}
runLTSTester :: (After m loc foo i o, TestChoice i' (Act foo i o), Ord (Q foo loc), Ord (m (Q foo loc)), Tdest foo ~ (), i ~ i', TCI foo i ~ i') =>
    AutIntrpr m loc i o foo -> TestController m loc i' o foo state r -> Adapter (Act foo i o) i' -> IO (Verdict, r)
runLTSTester spec testSelection = runExperiment (makeTester spec testSelection)

{- |
    runTester specialized to STS models, and without running the sanity checks.
-}
runSTSTester :: (IOAfter m loc foo i o tdest, StepSemantics m loc q t STStdest act, TestChoice (TCI foo i) act, Tdest foo ~ STStdest, act ~ Act foo i o, t ~ T foo i o, q ~ Q foo loc) =>
    AutIntrpr m loc i o foo -> TestController m loc i o foo state r -> Adapter act (TCI foo i) -> IO (Verdict, r)
runSTSTester spec testSelection = runExperiment (makeTester spec testSelection)

