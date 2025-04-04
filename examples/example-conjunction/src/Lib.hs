{-# LANGUAGE DeriveGeneric #-}
module Lib
    ( someFunc
    ) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Adapter.StandardAdapters(Adapter,connectJSONSocketAdapterAcceptingInputs,withTimeoutMillis)
import Lattest.Model.StandardAutomata(automaton, ioAlphabet, alternatingConcTransFromMRel,semanticsQuiescentConcrete, atom, top, bot, (\/), (/\),)
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(TestController(..), Verdict(..), runTester)
import Data.Aeson(FromJSON, ToJSON)
import GHC.Generics (Generic)

data GState = Q0G | Q1G | Q2G | Q3G | Q4G | Q5G | Q6G | Q7G | Q8G | Q9G | Q10G deriving (Eq, Ord, Show)
q0G = atom Q0G
q1G = atom Q1G
q2G = atom Q2G
q3G = atom Q3G
q4G = atom Q4G
q5G = atom Q5G
q6G = atom Q6G
q7G = atom Q7G
q8G = atom Q8G
q9G = atom Q9G
q10G = atom Q10G
data GIn = On | A | B | Take deriving (Eq, Ord, Show, Generic)
instance FromJSON GIn
instance ToJSON GIn
data GOut = C | T | CM | TM deriving (Eq, Ord, Show, Generic)
instance FromJSON GOut
instance ToJSON GOut

tG =alternatingConcTransFromMRel
    [   (Q0G, In On, q1G /\ q3G /\ q5G /\ q8G),
        (Q1G, In A, q2G),
        (Q3G, In B, q4G),
        (Q5G, In B, q6G \/ q7G),
        (Q8G, In A, q9G),
        (Q8G, In B, q9G),
        (Q10G, In Take, q1G /\ q3G /\ q5G /\ q8G),
        (Q2G, Out C, top),
        (Q4G, Out T, top),
        (Q4G, Out TM, top),
        (Q6G, Out CM, top),
        (Q7G, Out TM, top),
        (Q2G, Out C, top),
        (Q9G, Out C, q10G),
        (Q9G, Out T, q10G),
        (Q9G, Out CM, q10G),
        (Q9G, Out TM, q10G)
    ]
menuG = ioAlphabet [On, A, B,Take] [C, T, CM, TM]
sG = automaton q0G menuG tG

nrSteps = 50
testSelector = randomTestSelectorFromSeed 456 `untilCondition` stopAfterSteps nrSteps `withSideEffect` printState `withSideEffect` printActions `observingOnly` traceObserver `andObserving` stateObserver

someFunc :: IO ()
--someFunc = withSocketsDo $ do
someFunc = do
    putStrLn $ "connecting..."
    adap <- connectJSONSocketAdapterAcceptingInputs :: IO (Adapter (IOAct GIn GOut) GIn) -- the adapter connects, with explicit typing because it should know how to parse incoming data
    imp <- withTimeoutMillis 200 adap
    let model = semanticsQuiescentConcrete sG
    putStrLn $ "starting test..."
    (verdict, (observed, maybeMq)) <- runTester model testSelector imp
    putStrLn $ "verdict: " ++ show verdict
    putStrLn $ "observed: " ++ show observed
    putStrLn $ "final state: " ++ show maybeMq
