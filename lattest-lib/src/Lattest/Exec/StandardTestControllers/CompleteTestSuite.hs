module Lattest.Exec.StandardTestControllers.CompleteTestSuite (
accessSeqSelector,
adgTestSelector,
nCompleteSingleState,
runNCompleteTestSuite,
)
where
import Lattest.Adapter.Adapter(Adapter,close)
import Lattest.Adapter.StandardAdapters(withQuiescenceMillis)
import Lattest.Exec.ADG.Aut(adgAutFromAutomaton)
import Lattest.Exec.ADG.DistGraph(computeAdaptiveDistGraph)
import Lattest.Exec.ADG.SplitGraph(Evidence(..))
import Lattest.Exec.StandardTestControllers(andThen,randomTestSelectorFromSeed,untilCondition,stopAfterSteps,observingOnly,printActions,traceObserver,andObserving,stateObserver)
import Lattest.Exec.Testing(TestController(..), runTester,Verdict)
import Lattest.Model.Alphabet(IOAct(..), IOSuspAct, Suspended(..), asSuspended)
import Lattest.Model.Automaton(AutIntrpr(..),AutSyntax)
import Lattest.Model.BoundedMonad(Det(..))
import Lattest.Model.StandardAutomata(ConcreteSuspAutIntrpr(..), accessSequences, interpretQuiescentConcrete)

import Control.Monad (forM)
import qualified Data.Map as Map ((!))
import qualified Data.Set as Set (empty, Set)
import System.Random(StdGen)

{- | A TestController that selects inputs that lead to the given targetState. If unexpected outputs are selected by the SUT the TestSelector still tries to provide the inputs of the access sequence, but this may result in reaching another state.
 Result Bool is True when access sequence has been followed and false when the SUT deviated
-}
accessSeqSelector :: (Ord q, Eq i, Eq o, Show i, Show o) => ConcreteSuspAutIntrpr Det q i o -> q -> TestController Det q q (IOAct i o) () (IOSuspAct i o) [IOAct i o] (Maybe i) Bool
accessSeqSelector aut targetState =
    let initState = case stateConf aut of
            Det q -> q
            _ -> error "Access sequence: model must be in a specified initial state"
        accSeqs = accessSequences aut initState
    in TestController {
        testControllerState = (Map.!) accSeqs targetState,
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

{- | A TestController that selects inputs according to the adaptive distinguishing sequence of the given automaton
-}
adgTestSelector :: (Ord q, Ord l, Eq l, Show l) => ConcreteSuspAutIntrpr Det q l l -> l ->  TestController Det q q (IOAct l l) () (IOSuspAct l l) (Evidence l) (Maybe l) (Set.Set q)
adgTestSelector aut delta =
    let adgaut = case adgAutFromAutomaton aut delta of
                    Just a -> a
                    Nothing ->  error "could not transform Lattest auomaton into ADG automaton"
        adg = computeAdaptiveDistGraph adgaut False False True
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

{- | A TestController that yields tests that tries to take an access sequence to the targetState and then executes the adaptive distinguishing sequence
-}
nCompleteSingleState :: (Ord q, Ord l, Show l) => ConcreteSuspAutIntrpr Det q l l -> Int -> Int -> l -> q
                                                    -> TestController Det q q (IOAct l l) () (IOSuspAct l l) (((), [IOSuspAct l l]), Maybe (Det q)) i20 ([IOSuspAct l l], Maybe (Det q))
                                                    -> IO (TestController Det q q (IOAct l l) () (IOSuspAct l l) (Either (Either [IOAct l l] StdGen, Int) (Evidence l), (((), [IOSuspAct l l]), Maybe (Det q))) (Maybe l) ([IOSuspAct l l], Maybe (Det q)))
nCompleteSingleState model seed nrSteps delta targetState observer = do
    return $ accessSeqSelector model targetState
        `andThen` randomTestSelectorFromSeed seed `untilCondition` stopAfterSteps nrSteps
            `andThen` adgTestSelector model delta `observingOnly` observer

{- | Runs tests from nCompleteSingleState for each given targetState and seed
-}
runNCompleteTestSuite :: (Ord q, Ord l, Show q, Show l) => IO (Adapter (IOAct l l) l) -> AutSyntax Det q (IOAct l l) () -> Int -> l -> [(q, Int)] -> IO [(q, Verdict, ([IOSuspAct l l], Maybe (Det q)))]
runNCompleteTestSuite adapter spec nrSteps delta targetStatesAndSeeds = do
        results <- forM targetStatesAndSeeds $ \(targetState,seed) -> do
            putStrLn "connecting..."
            adap <- adapter
            imp <- withQuiescenceMillis 200 adap
            let model = interpretQuiescentConcrete spec
            putStrLn "starting test..."
            putStrLn $ "accessing state: " ++ (show targetState)
            selector <- testSelector model seed targetState
            (verdict,(observed, maybeMq)) <- runTester model selector imp
            close adap
            return (targetState, verdict, (observed, maybeMq))
        return results
    where testSelector model seed targetState = nCompleteSingleState model seed nrSteps delta targetState $ printActions `observingOnly` traceObserver `andObserving` stateObserver