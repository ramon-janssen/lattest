module Lib
    ( run
    ) where

import qualified Lattest.Model.Automaton as Aut
import qualified Lattest.Model.Alphabet as Alph
import           Lattest.Model.Alphabet(IOAct(In, Out))
import           Lattest.Model.Symbolic.Expr
import           Lattest.Model.Symbolic.SolveSTS
import qualified Lattest.SMT as SMT
import qualified Data.Set as Set
import Lattest.Adapter.StandardAdapters
import Lattest.Exec.StandardTestControllers
import Lattest.Exec.Testing(TestController(..), Verdict(..), runSMTTester, Verdict(Pass))
import Lattest.Model.Alphabet(IOAct(In, Out))
import Lattest.Model.BoundedMonad(Det)
import Lattest.Model.StandardAutomata
import Lattest.Model.Symbolic.Expr
import Lattest.SMT
import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Lattest.Model.Alphabet as Alph
import qualified Lattest.Model.Automaton as Aut

pvar = Variable "p" FloatType
xvar = Variable "x" FloatType

stsExample :: IOSTS Det Double String String
stsExample =
    let p = sVar pvar
        x = sVar xvar
        water = Alph.SymInteract (In "water") [Some pvar]
        ok = Alph.SymInteract (Out "ok") [Some pvar]
        coffee = Alph.SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = return 0
        switches = \q -> case q of
            0 -> Map.fromList [(water, pure (Aut.stsTLoc waterGuard waterAssign, 1)),
                                (coffee, pure (Aut.stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, pure (Aut.stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches

stsExampleInitAssign = Valuation $ DMap.singleton xvar (Val 0)

model = interpretSTSQuiescent stsExample stsExampleInitAssign
model' = interpretSTS stsExample stsExampleInitAssign

run :: IO ()
run = do
    let controller = randomDataTestSelectorFromSeed 456 `untilCondition` stopAfterSteps 10
    offlinetests <- offlineTests model' controller
    print offlinetests
    print $ toTrace model' offlinetests

    putStrLn $ "connecting to SUT..."
    let quiesenceMillis = 300
    let delayMillis = 100
     -- the adapter connects, with explicit typing because it should know how to parse incoming data
    adap <- connectJSONSocketAdapterAcceptingInputs >>= withQuiescenceMillis quiesenceMillis >>= withInputDelayMillis delayMillis >>= asSymbolicSuspAdapter
                 :: IO (Adapter (Alph.IOSuspGateValue String String) (Maybe (Alph.GateValue String)))

    putStrLn $ "starting test..."
    let nrSteps = 50
        probabilityOfWaitForOutput = 0.0
        randomSeed = 456
        testSelector = randomDataOrWaitForOutputTestSelectorFromSeed randomSeed probabilityOfWaitForOutput `untilCondition` stopAfterSteps nrSteps
                        `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    (verdict, (observed, maybeMq)) <- runSMTTester model testSelector adap

    putStrLn $ "verdict: " ++ show verdict
    putStrLn $ "observed: " ++ show observed
    putStrLn $ "final state: " ++ show maybeMq
