{-# LANGUAGE DeriveGeneric #-}
module Lib
    ( runNCompleteTestSuiteExample
    ) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Adapter.StandardAdapters(Adapter,connectJSONSocketAdapterAcceptingInputs,withQuiescenceMillis)
import Lattest.Model.StandardAutomata
import Lattest.Model.Automaton(reachable)
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, Verdict(Pass))
import Lattest.Exec.StandardTestControllers
import Control.DeepSeq(NFData)
import GHC.Generics (Generic)
import Control.Monad (forM_)
import qualified Data.Set as Set

data State = PickEither | PickEitherIn | Picked2 | Picked1 | Confirm1 | Confirmed1 | Confirm2 | Confirmed2 deriving (Eq, Ord, Show, Generic)
instance NFData State

Just trans = detConcTransFromRel
    [   (PickEither, In 0, PickEitherIn),
        (PickEither, Out 1, Picked1),
        (PickEither, Out 2, Picked2),
        (PickEitherIn, Out 1, Confirm1),
        (PickEitherIn, Out 2, Confirm2),
        (Picked1, In 0, Confirm1),
        (Picked2, In 0, Confirm2),
        (Confirm1, Out 1, Confirmed1),
        (Confirm2, Out 2, Confirmed2),
        (Confirmed1, In (-1), PickEither),
        (Confirmed2, In (-2), PickEither)
    ]
alphabet = ioAlphabet [0, -1, -2] [1, 2]
initialConfiguration = pure PickEither

spec = automaton initialConfiguration alphabet trans

nrSteps = 10
seed = 456
delta = 4
-- testSelector = \model -> nCompleteSingleState model targetState seed nrSteps delta targetState $ printActions `observingOnly` traceObserver `andObserving` stateObserver
-- accessSeqSelector model PickEither targetState `andThen` (randomTestSelectorFromSeed seed `untilCondition` stopAfterSteps nrSteps)  `andThen` adgTestSelector model 4 `observingOnly` printActions `observingOnly` traceObserver `andObserving` stateObserver


runNCompleteTestSuiteExample :: IO ()
runNCompleteTestSuiteExample = do
    let targetStates = Set.toList (reachable spec)
    let seeds = [seed + n | n <- [1..(length targetStates)]]
    results <- runNCompleteTestSuite adapter spec nrSteps delta (zip targetStates seeds)
    
    forM_ results $ \(state, verdict, (observed, maybeMq)) -> do
        putStrLn $ "state: " ++ show state
        putStrLn $ "verdict: " ++ show verdict
        putStrLn $ "observed: " ++ show observed
        putStrLn $ "final state: " ++ show maybeMq
    where adapter = connectJSONSocketAdapterAcceptingInputs  :: IO (Adapter (IOAct Int Int) Int) -- the adapter connects, with explicit typing because it should know how to parse incoming data
