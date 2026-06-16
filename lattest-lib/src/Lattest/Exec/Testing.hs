{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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
makeSMTTester,
runTester,
runSMTTester,
Verdict(..),
InconclusiveReason(..),
offlineTester,
offlineTreeToTrace
)
where

import Lattest.Model.Alphabet(TestChoice, IOAct (..), isOutput, fromOutput)
import Lattest.Model.Automaton(StepSemantics, StepSemantics, AutIntrpr, After, IOAfter, ioAfter, stateConf, AutomatonException, FiniteMenu, indefiniteMenu)
import Lattest.Model.BoundedMonad(BoundedConfiguration, isConclusive, isForbidden)
import Lattest.Adapter.Adapter(Adapter(..), send, tryObserve)
import Lattest.SMT.SMTData(SMTRef)


import Control.Exception(catch,evaluate)

--import Control.DeepSeq(force)
import System.IO.Streams.Synchronized (Streamed(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (forM)
import Data.Bifunctor (first)

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
newtype InconclusiveReason = AutomatonException AutomatonException deriving (Ord, Eq, Show)

{- |
    The controller of a testing experiment. The tester may return a result at the end of a testing experiment. Note that it does
    /not/ need to return a verdict 'Pass' or 'Fail', this verdict is automatically inferred based on the specification model.
    Results can be used to record additional information that the tester is interested in, depending on the controller implementation.
    For example, the actions observed during a testing experiment, or whether certain coverage criteria were achieved during the experiment.
-}
data TestController m loc q t tdest act state i r = TestController {
    -- | Any state that the controller needs for its decision making duties.
    testControllerState :: state,
    {- |
        Select a test based on test controller state, the specification (in its current state), and previous specification configuration.
        Either select a new controller state and a input, /or/ stop testing and return a result from the controller.
    -}
    selectTest :: (TestChoice i act) => state -> AutIntrpr m loc q t tdest act -> m q -> IO (Either (i, state) r),
    {- |
        Select a test based on test controller state, the specification (in its current state), an observed action, and previous specification
        configuration. Either select a new controller state, /or/ stop testing and return a result from the controller.
    -}
    updateTestController :: state -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (Either state r),
    -- | Handle the end of the action stream, i.e. the other end closing, ending the experiment.
    handleTestClose :: state -> IO r
    }

{- |
    From a test controller and a specification model, create an action controller. The test controller is used to decide which inputs
    are supplied to the system under test, and whether to continue or stop testing. The automaton specification model is used to infer whether
    observed actions are allowed or not, and to return a verdict in case of forbidden or underspecified observations.
-}
makeTester :: (After m loc q t tdest act, TestChoice i act, Ord q, Ord (m q)) =>
    AutIntrpr m loc q t tdest act -> TestController m loc q t tdest act state i r -> ActionController act i (Verdict, r) (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r)
makeTester = makeTester' ()

--makeSMTTester :: (IOStepSemantics m loc q t tdest act SmtEnv, TestChoice i act, BoundedConfiguration m, BooleanConfiguration m, Foldable m, Ord q, Ord loc, Ord tdest) =>
makeSMTTester :: (IOAfter m loc q t tdest act SMTRef, StepSemantics m loc q t tdest act, TestChoice i act) =>
    SMTRef -> AutIntrpr m loc q t tdest act -> TestController m loc q t tdest act state i r -> ActionController act i (Verdict, r) (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r)
makeSMTTester = makeTester'

makeTester' :: (IOAfter m loc q t tdest act ioState, StepSemantics m loc q t tdest act, TestChoice i act) =>
    ioState -> AutIntrpr m loc q t tdest act -> TestController m loc q t tdest act state i r -> ActionController act i (Verdict, r) (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r)
makeTester' ioState initSpec initTestController = ActionController {
    controllerState = (initSpec, initTestController),
    select = makeSelect,
    update = makeUpdate ioState,
    handleClose = makeHandleClose
    }
    where
        makeSelect :: (TestChoice i act, BoundedConfiguration m)
            => (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r)
            -> IO (Either (i, (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r)) (Verdict, r))
        makeSelect (spec, testController) = do
            next <- selectTest testController (testControllerState testController) spec (stateConf spec)
            case next of
                Right r -> return $ Right (pToVerd $ stateConf spec, r)
                Left (i, state') -> return $ Left (i, (spec, testController { testControllerState = state' }))
--            return $ case next of
--                Right r -> Right (pToVerd $ stateConf spec, r)
--                Left (i, state') -> Left (i, (spec, testController { testControllerState = state' }))
        makeUpdate :: (IOAfter m loc q t tdest act ioState, StepSemantics m loc q t tdest act) =>
            ioState -> (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r) -> act -> IO (Either (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r) (Verdict, r))
        makeUpdate ioState' (spec, testController) act = do
            spec' <- ioAfter ioState' spec act
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
        makeHandleClose :: (BoundedConfiguration m) => (AutIntrpr m loc q t tdest act, TestController m loc q t tdest act state i r) -> IO (Verdict, r)
        makeHandleClose (spec, testController) = do
            r <- handleTestClose testController (testControllerState testController)
            return (pToVerd $ stateConf spec, r)
        pToVerd :: (BoundedConfiguration m) => m x -> Verdict
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
    Running a tester requires:
    
    * a specification model in the form of an automaton, as defined in "Lattest.Model.Automaton"
    * a 'TestController', defined in this module itself, and
    * an adapter, as defined in "Lattest.Adapter.Adapter".

    Running a testing experiment is done by interacting with the given adapter, controlled by the given test controller. The experiment
    stops when the action controller decides to, or when an observation is made that is forbidden or underspecified according
    to the specification model. Returns the test verdict according to the specification model and the additional
    result returned by the test controller.
-}
runTester :: (After m loc q t tdest act, TestChoice i act, Ord q, Ord (m q)) =>
    AutIntrpr m loc q t tdest act -> TestController m loc q t tdest act state i r -> Adapter act i -> IO (Verdict, r)
runTester spec testSelection = runExperiment (makeTester spec testSelection)

runSMTTester :: (IOAfter m loc q t tdest act SMTRef, StepSemantics m loc q t tdest act, TestChoice i act) =>
    SMTRef -> AutIntrpr m loc q t tdest act -> TestController m loc q t tdest act state i r -> Adapter act i -> IO (Verdict, r)
runSMTTester ioState spec testSelection = runExperiment (makeSMTTester ioState spec testSelection)

--runStepper :: (Automaton aut c act) => aut -> ActionController (Path aut c act) act r state  -> IO r
--runStepper spec controller = runExperiment controller (simulateSpec spec)


{- |
    Offline test generation: Instead of connecting to a system and running the tests live,
    generate a decision tree that can later be used to test a system.
    On 'Nothing', inputs are only generated from states with no outputs.
    On 'Just Quiescence', inputs are also generated from other states after observing quiescence.
-}
offlineTester
  :: forall m loc q t tdest i o state r
   . (After m loc q t tdest (IOAct i o), Ord o, Ord q, Ord (m q), Foldable m, Ord i, FiniteMenu t (IOAct i o))
  => AutIntrpr m loc q t tdest (IOAct i o)
  -> TestController m loc q t tdest (IOAct i o) state i r
  -> Maybe o
  -> IO (OfflineTree o i (Verdict, r))
offlineTester spec testSelection quiescence = go (makeTester spec testSelection)
  where
    go :: ActionController (IOAct i o) i (Verdict, r) ( AutIntrpr      m loc q t tdest (IOAct i o)
                                                      , TestController m loc q t tdest (IOAct i o) state i r)
       -> IO (OfflineTree o i (Verdict, r))
    go controller = do
      let indefiniteAct = indefiniteMenu $ fst $ controllerState controller
      let outOptions = map fromOutput . filter isOutput $ indefiniteAct
      case outOptions of
        [] | null indefiniteAct
           -> error "no inputs and no outputs, continuing (like runTester does) would crash in the testcontroller"

        -- no inputs and only quiescent output, we observe it once and terminate this branch of the tree
        [q] | Just q == quiescence
            , all isOutput indefiniteAct
            -> CaseSplit . Map.singleton q . Leaf <$> do
                res <- update controller (controllerState controller) (Out q)
                case res of
                  Left state -> handleClose controller state
                  Right r -> return r

        -- no outputs or only quiescence, so we perform an input request
        [q] | Just q == quiescence
            -> handleInput controller
        []  -> handleInput controller

        -- real output(s) possible, we choose not to make any input requests and just listen
        _ -> CaseSplit . Map.fromList <$> forM outOptions
              (\o -> (o,) <$> handleUpdate controller (Out o))

    handleInput controller = do
      selection <- select controller (controllerState controller)
      case selection of
        Left (i, state) -> do
          InputRequest i <$> handleUpdate (controller {controllerState = state}) (In i)
        Right result -> do
          return $ Leaf result

    handleUpdate controller aut = do
      foo <- update controller (controllerState controller) aut
      case foo of
        Left state -> do
          go (controller { controllerState = state})
        Right result -> do
          return $ Leaf result

-- |A tree representing an offline test case.
-- Such a test makes concrete choices on the inputs
-- it gives the SUT, while accomodating for all
-- possible outputs the SUT can send.
-- Note: `o` can be `Suspended o'`, in which case `Quiescence`
-- may occur in `CaseSplit`.
data OfflineTree o i r where
  -- |The end of a possible test trace
  Leaf :: r
       -> OfflineTree o i r
  -- |The test sends input to the SUT
  InputRequest :: i
               -> OfflineTree o i r
               -> OfflineTree o i r
  -- |The test tries to get an output from the SUT.
  CaseSplit :: Map o (OfflineTree o i r)
            -> OfflineTree o i r

instance (Show r, Show i, Show o, Ord o) => Show (OfflineTree o i r) where
  show (Leaf r) = show r
  show (InputRequest i ot) = "?" <> show i <> ": \n" <> indentOfflineTree 2 (show ot)
  show (CaseSplit m) =
    "case <output> of\n"
    <> indentOfflineTree 2 (unlines
         (map (\(o,ot) -> "!" <> show o <> " -> \n" <> indentOfflineTree 2 (show ot)) $ Map.toList m))

-- Indent a prettyprinted tree with `i` spaces.
-- Uses init to get rid of the trailing newline.
-- Crashes on empty input.
indentOfflineTree :: Int -> String -> String
indentOfflineTree i = init . unlines . map (replicate i ' ' ++) . lines

-- |If the tree has no branching, convert it to a trace
offlineTreeToTrace :: OfflineTree o i r -> Maybe ([IOAct i o],r)
offlineTreeToTrace (Leaf r) = Just ([],r)
offlineTreeToTrace (InputRequest i ot) = first (In i:) <$> offlineTreeToTrace ot
offlineTreeToTrace (CaseSplit m) = case Map.toList m of
  [(o,ot)] -> first (Out o:) <$> offlineTreeToTrace ot
  _ -> Nothing

