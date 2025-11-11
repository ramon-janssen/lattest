{-# LANGUAGE DeriveGeneric #-}
module Lib
    ( someFunc
    ) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Adapter.StandardAdapters(Adapter,connectJSONSocketAdapterAcceptingInputs,withQuiescenceMillis)
import Lattest.Model.StandardAutomata
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, Verdict(Pass))
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.StandardTestControllers(accessSeqSelector)
--import Network.Socket(withSocketsDo)
import Control.DeepSeq(NFData)
import GHC.Generics (Generic)

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
        (Confirmed1, In 1, PickEither),
        (Confirmed2, In 2, PickEither)
    ]
alphabet = ioAlphabet [0, 1, 2] [1, 2]
initialConfiguration = pure PickEither

spec = automaton initialConfiguration alphabet trans

nrSteps = 3
seed = 456
testSelector = \model ->  accessSeqSelector model PickEither Confirmed2 `andThen` (randomTestSelectorFromSeed seed `untilCondition` stopAfterSteps nrSteps)  `andThen` adgTestSelector model 4 `observingOnly` printActions `observingOnly` traceObserver `andObserving` stateObserver

-- randomTestSelectorFromSeed 456 `untilCondition` stopAfterSteps nrSteps `observingOnly` printActions `observingOnly` traceObserver `andObserving` stateObserver

someFunc :: IO () -- FIXME give this function a sensible name
someFunc = do
    putStrLn $ "connecting..."
    adap <- connectJSONSocketAdapterAcceptingInputs :: IO (Adapter (IOAct Int Int) Int) -- the adapter connects, with explicit typing because it should know how to parse incoming data
    imp <- withQuiescenceMillis 200 adap
    let model = interpretQuiescentConcrete spec
    putStrLn $ "starting test..."
    (verdict, (observed, maybeMq)) <- runTester model (testSelector model) imp
    putStrLn $ "verdict: " ++ show verdict
    putStrLn $ "observed: " ++ show observed
    putStrLn $ "final state: " ++ show maybeMq
