module Lib
    ( run
    ) where

import qualified Lattest.Model.Automaton as Aut
import qualified Lattest.Model.Alphabet as Alph
import           Lattest.Model.Alphabet(IOAct(In, Out))
import           Lattest.Model.Symbolic.Expr
import qualified Lattest.SMT as SMT
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Dependent.Map as DMap
import qualified Data.Maybe as Maybe
import           Lattest.Adapter.StandardAdapters
import           Lattest.Model.StandardAutomata
import           Lattest.Exec.Testing(TestController(..), Verdict(..), runSMTTester, Verdict(Pass))
import           Lattest.Exec.StandardTestControllers
import           Lattest.Model.BoundedMonad(Det)
import Lattest.SMT (Some(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (List(..))

pvar = Variable "p" IntType
-- xvar = Variable "x" IntType
xsvar = Variable "xs" (ListType IntType)


stsExample :: IOSTS Det Int String String
stsExample =
    let p = sVar pvar
        -- x = sVar xvar
        xs = sVar xsvar
        water = Alph.SymInteract (In "water") [Some pvar]
        ok = Alph.SymInteract (Out "ok") [Some pvar]
        coffee = Alph.SymInteract (Out "coffee") []
        waterGuard = p .== 1
        waterAssign = assignment [xsvar =: p `sCons` xs]
        okGuard = sLength xs .== p
        coffeeGuard = sLength xs .>= 15
        initConf = return 0
        switches = \q -> case q of
            0 -> Map.fromList [(water, pure (Aut.stsTLoc waterGuard waterAssign, 1)),
                                (coffee, pure (Aut.stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, pure (Aut.stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches

stsExampleInitAssign = Valuation $ DMap.singleton xsvar $ Val $ List []

model = interpretSTSQuiescent stsExample stsExampleInitAssign

run :: IO ()
run = do
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
