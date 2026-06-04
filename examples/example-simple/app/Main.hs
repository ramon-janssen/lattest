module Main (main) where

import Data.Set (Set)
import Lattest.Adapter.Adapter (Adapter)
import Lattest.Adapter.StandardAdapters (pureMealyAdapter)
import Lattest.Exec.StandardTestControllers (andObserving, observingOnly, printActions, randomTestSelectorFromSeed, stateObserver, stopAfterSteps, traceObserver, untilCondition)
import Lattest.Exec.Testing (runTester, TestController)
import Lattest.Model.Alphabet (IOAct (..))
import Lattest.Model.StandardAutomata (automaton, detConcTransFromRel, interpretConcrete, ioAlphabet)
import Data.Maybe (fromJust)
import Lattest.Model.BoundedMonad (Det)
import Data.Map (Map)
import Lattest.Model.Automaton (AutSyntax)
import System.Random (StdGen)

-- Machine that turns itself off

------ model definition -----------
data State = On | Off
  deriving (Ord, Eq, Show)

alphabet :: Set (IOAct String String)
alphabet = ioAlphabet ["TurnOn"] ["TurnOff"]

trans :: State -> Map (IOAct String String) (Det ((), State))
trans = fromJust $ detConcTransFromRel [(Off, In "TurnOn", On), (On, Out "TurnOff", Off)]

initial :: Det State
initial = pure Off

spec :: AutSyntax   Det State (IOAct String String) ()
spec = automaton initial alphabet trans

------ end model definition -------

------ SUT implementations ------

-- TODO: this would be nicer without the `Out` in giveoutput,
-- as `sutPure :: IO (Adapter String String)`.
-- why can't I get runTester to typecheck with that?
sutPure :: IO (Adapter (IOAct String String) String)
sutPure = pureMealyAdapter step giveoutput Off
  where
    -- The step function never changes the state, because the machine immediately turns itself off
    step Off "TurnOn" = Off
    step _ _ = error "not defined"
    giveoutput On "TurnOn" = [Out "TurnOff"]
    giveoutput _ _ = []

-- TODO: non-pure version, i.e. a thread that actually changes the state, waits a bit, then turns itself off and emits "turnoff"

------ end SUT -----

nrSteps :: Int
nrSteps = 50

-- TODO: copied this from example-template, might not need all these observers in a simple example
testSelector :: TestController Det State State (IOAct String String) () (IOAct String String) ((((StdGen, Int), ()), [IOAct String String]), Maybe (Det State)) String ([IOAct String String], Maybe (Det State))
testSelector = randomTestSelectorFromSeed 456 `untilCondition` stopAfterSteps nrSteps `observingOnly` printActions `observingOnly` traceObserver `andObserving` stateObserver

main :: IO ()
main = do
  putStrLn "mealy version"
  (verdict, (observed, maybeMq)) <- sutPure >>= runTester (interpretConcrete spec) testSelector
  putStrLn $ "verdict: " ++ show verdict
  putStrLn $ "observed: " ++ show observed
  putStrLn $ "final state: " ++ show maybeMq

