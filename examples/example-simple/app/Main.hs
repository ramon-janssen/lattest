{-# LANGUAGE FlexibleContexts #-}
module Main (main) where

import Data.Set (Set)
import Lattest.Adapter.Adapter (Adapter)
import Lattest.Adapter.StandardAdapters (pureMealyAdapter)
import Lattest.Exec.StandardTestControllers (andObserving, observingOnly, randomTestSelectorFromSeed, stateObserver, stopAfterSteps, traceObserver, untilCondition)
import Lattest.Exec.Testing (runTester, offlineTester, offlineTreeToTrace, TestController)
import Lattest.Model.Alphabet (IOAct (..), Suspended (..))
import Lattest.Model.StandardAutomata (automaton, detConcTransFromRel, interpretConcrete, ioAlphabet, interpretQuiescentConcrete)
import Data.Maybe (fromJust)
import Lattest.Model.BoundedMonad (Det)
import Data.Map (Map)
import Lattest.Model.Automaton (AutSyntax, TransitionSemantics, FiniteMenu)
import System.Random (StdGen)

-- Machine that turns itself off

------ model definition -----------
data State = On | Off
  deriving (Ord, Eq, Show)

data Input = TurnOn deriving (Ord, Eq, Show)
data Output = TurnOff deriving (Ord, Eq, Show, Enum, Bounded)

alphabet :: Set (IOAct Input Output)
alphabet = ioAlphabet [TurnOn] [TurnOff]

trans :: State -> Map (IOAct Input Output) (Det ((), State))
trans = fromJust $ detConcTransFromRel [(Off, In TurnOn, On), (On, Out TurnOff, Off)]

initial :: Det State
initial = pure Off

spec :: AutSyntax   Det State (IOAct Input Output) ()
spec = automaton initial alphabet trans

------ end model definition -------

------ SUT implementations ------

sutPure :: IO (Adapter (IOAct Input Output) Input)
sutPure = pureMealyAdapter step giveoutput ()
  where
    -- The step function never changes the state, because the machine immediately turns itself off
    step () TurnOn = ()
    giveoutput () TurnOn = [In TurnOn, Out TurnOff]

------ end SUT -----

nrSteps :: Int
nrSteps = 5

-- Giving it this type lets it be used both with and without quiescence
-- the alternative is just duplicating the code, because type inference
-- isn't smart enough to infer this type
testSelector :: ( TransitionSemantics State State (IOAct Input Output) () (IOAct Input o)
                , FiniteMenu (IOAct Input Output) (IOAct Input o)
                , Ord o
                )
             => TestController Det State State (IOAct Input Output) () (IOAct Input o) (((StdGen, Int), [IOAct Input o]), Maybe (Det State)) Input ([IOAct Input o], Maybe (Det State))
testSelector = randomTestSelectorFromSeed 456
  `untilCondition` stopAfterSteps nrSteps
  `observingOnly` traceObserver
  `andObserving` stateObserver

main :: IO ()
main = do
  putStrLn "mealy version"
  (verdict, (observed, maybeMq)) <- sutPure >>= runTester (interpretConcrete spec) testSelector
  putStrLn $ "verdict: " ++ show verdict
  putStrLn $ "observed: " ++ show observed
  putStrLn $ "final state: " ++ show maybeMq

  putStrLn "Offline test gen:"
  tests <- offlineTester (interpretQuiescentConcrete spec) testSelector
  putStrLn "Tests:"
  print tests
  putStrLn "Trace:"
  print $ offlineTreeToTrace tests

