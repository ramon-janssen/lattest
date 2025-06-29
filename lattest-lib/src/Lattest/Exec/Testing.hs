{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

{- |
    This module contains the main functions and data structures to run experiments against (external) systems, specifically testing
    experiments.
    
    For an experiment, we assume that we have an 'Adapter', which serves as an interface to send inputs to a system under test,
    and observe actions shown by that system. The experiment is controlled by an 'ActionController'. Specifically for a testing
    experiment, we also assume that we have a specification model that dictates which observations are allowed and forbidden, and a test
    controller that steers the testing.
    
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
runTester,
Verdict(..)
)
where

import Lattest.Model.Alphabet(TestChoice, Refusable, isAccepted)
import Lattest.Model.Automaton(AutomatonSemantics, AutSem, after, stateConf)
import Lattest.Model.StateConfiguration(PermissionConfiguration, isConclusive, isForbidden)
import Lattest.Adapter.Adapter(Adapter(..), send, tryObserve)

import System.IO.Streams.Synchronized (Streamed(..))

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
data Verdict = Pass | Fail deriving (Ord, Eq, Show, Read)

{- |
    The controller of a testing experiment. The tester may return a result at the end of a testing experiment. Note that it does
    /not/ need to return a verdict 'Pass' or 'Fail', this verdict is automatically inferred based on the specification model.
    Results can be used to record additional information that the tester is interested in, depending on the controller implementation.
    For example, the actions observed during a testing experiment, or whether certain coverage criteria were achieved during the experiment.
-} 
data TestController m loc q t tloc act state i r = TestController {
    -- | Any state that the controller needs for its decision making duties.
    testControllerState :: state,
    {- |
        Select a test based on test controller state, the specification (in its current state), and previous specification configuration.
        Either select a new controller state and a input, /or/ stop testing and return a result from the controller.
    -}
    selectTest :: (TestChoice i act) => state -> AutSem m loc q t tloc act -> m q -> IO (Either (i, state) r),
    {- |
        Select a test based on test controller state, the specification (in its current state), an observed action, and previous specification
        configuration. Either select a new controller state, /or/ stop testing and return a result from the controller.
    -}
    updateTestController :: state -> AutSem m loc q t tloc act -> act -> m q -> IO (Either state r),
    -- | Handle the end of the action stream, i.e. the other end closing, ending the experiment.
    handleTestClose :: state -> IO r
    }

{- |
    From a test controller and a specification model, create an action controller. The test controller is used to decide which inputs
    are supplied to the system under test, and whether to continue or stop testing. The automaton specification model is used to infer whether
    observed actions are allowed or not, and to return a verdict in case of forbidden or underspecified observations.
-}
makeTester :: (AutomatonSemantics m loc q t tloc act, TestChoice i act, PermissionConfiguration m) =>
    AutSem m loc q t tloc act -> TestController m loc q t tloc act state i r -> ActionController act i (Verdict, r) (AutSem m loc q t tloc act, TestController m loc q t tloc act state i r)
makeTester initSpec initTestController = ActionController {
    controllerState = (initSpec, initTestController),
    select = makeSelect,
    update = makeUpdate,
    handleClose = makeHandleClose
    }
    where
        makeSelect :: (TestChoice i act, PermissionConfiguration m)
            => (AutSem m loc q t tloc act, TestController m loc q t tloc act state i r)
            -> IO (Either (i, (AutSem m loc q t tloc act, TestController m loc q t tloc act state i r)) (Verdict, r))
        makeSelect (spec, testController) = do
            next <- selectTest testController (testControllerState testController) spec (stateConf spec)
            case next of
                Right r -> return $ Right (pToVerd $ stateConf spec, r)
                Left (i, state') -> return $ Left (i, (spec, testController { testControllerState = state' }))
--            return $ case next of
--                Right r -> Right (pToVerd $ stateConf spec, r)
--                Left (i, state') -> Left (i, (spec, testController { testControllerState = state' }))
        makeUpdate :: (AutomatonSemantics m loc q t tloc act, PermissionConfiguration m, Refusable act) =>
            (AutSem m loc q t tloc act, TestController m loc q t tloc act state i r) -> act -> IO (Either (AutSem m loc q t tloc act, TestController m loc q t tloc act state i r) (Verdict, r))
        makeUpdate (spec, testController) act = do
            let spec' = spec `after` act
            let verdict = actToVerd (stateConf spec') act
            next <- updateTestController testController (testControllerState testController) spec' act (stateConf spec)
            case next of
                Right r -> return $ Right (verdict, r)
                Left state' -> if isConclusive (stateConf spec') || verdict == Fail
                    then do
                        r <- handleTestClose testController state'
                        return $ Right (verdict, r)
                    else return $ Left (spec', testController { testControllerState = state' })
        makeHandleClose :: (PermissionConfiguration m) => (AutSem m loc q t tloc act, TestController m loc q t tloc act state i r) -> IO (Verdict, r)
        makeHandleClose (spec, testController) = do
            r <- handleTestClose testController (testControllerState testController)
            return (pToVerd $ stateConf spec, r) 
        pToVerd :: (PermissionConfiguration m) => (m x) -> Verdict
        pToVerd p | isForbidden p = Fail
                  | otherwise     = Pass
        actToVerd :: (PermissionConfiguration m, Refusable act) => (m x) -> act -> Verdict
        actToVerd p act = case pToVerd p of -- this is effectively just && between two verdicts, one from the observed action and one from the state configuration
            Fail -> Fail
            Pass -> if  (isAccepted act) then Pass else Fail 

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
    handleUpdate act = (update controller) (controllerState controller) act
    handleSelect = do
        selection <- (select controller) (controllerState controller)
        case selection of
            Left (inputCmd, state) -> do
                 -- TODO if an action is ready *after computing the input command* (because race condition between the adapter and controller), maybe don't send the input command.
                send inputCmd adapter
                return $ Left state
            Right result -> return $ Right result
    handleClosed = Right <$> handleClose controller (controllerState controller)

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
runTester :: (AutomatonSemantics m loc q t tloc act, TestChoice i act, PermissionConfiguration m) =>
    AutSem m loc q t tloc act -> TestController m loc q t tloc act state i r -> Adapter act i -> IO (Verdict, r)
runTester spec testSelection adapter = runExperiment (makeTester spec testSelection) adapter

--runStepper :: (Automaton aut c act) => aut -> ActionController (Path aut c act) act r state  -> IO r
--runStepper spec controller = runExperiment controller (simulateSpec spec)






