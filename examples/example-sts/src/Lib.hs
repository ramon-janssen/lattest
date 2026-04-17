module Lib
    ( run
    ) where

import qualified Lattest.Model.Automaton as Aut
import qualified Lattest.Model.Alphabet as Alph
import           Lattest.Model.Alphabet(IOAct(In, Out))
import           Lattest.Model.Symbolic.Expr
import qualified Lattest.SMT.Config as Config
import qualified Lattest.SMT.SMT as SMT
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import           Lattest.Adapter.StandardAdapters
import           Lattest.Model.StandardAutomata
import           Lattest.Exec.Testing(TestController(..), Verdict(..), runTester, Verdict(Pass))
import           Lattest.Exec.StandardTestControllers
--import           Network.Socket(withSocketsDo)


pvar = (Variable "p" IntType)
xvar = (Variable "x" IntType)

stsExample :: IOSTS FreeLattice Integer String String
stsExample =
    let p = sVar pvar
        x = sVar xvar
        water = Alph.SymInteract (In "water") [pvar]
        ok = Alph.SymInteract (Out "ok") [pvar]
        coffee = Alph.SymInteract (Out "coffee") []
        waterGuard = 1 .<= p .&& p .<= 10
        waterAssign = assignment [xvar =: x .+ p]
        okGuard = x .== p
        coffeeGuard = x .>= 15
        initConf = return 0 -- return $ Aut.IntrpState 0 stsExampleInitAssign :: FreeLattice (Aut.IntrpState Integer)
        switches = \q -> case q of
            0 -> Map.fromList [(water, pure (Aut.stsTLoc waterGuard waterAssign, 1)),
                                (coffee, pure (Aut.stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok, pure (Aut.stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty
    in automaton initConf (Set.fromList [water,ok,coffee]) switches

stsExampleInitAssign = fromConstantsMap $ Map.singleton xvar (Cint 0)

model = interpretSTSQuiescent stsExample stsExampleInitAssign

run :: IO ()
run = do
    let cfg = Config.changeLog Config.defaultConfig False 
        smtLog = Config.smtLog cfg
        smtProc = Maybe.fromJust (Config.getProc cfg)
    putStrLn $ "starting SMT solver..."
    smtRef <- SMT.createSMTRef smtProc smtLog

    putStrLn $ "connecting to SUT..."
    let quiesenceMillis = 200
     -- the adapter connects, with explicit typing because it should know how to parse incoming data
    adap <- connectJSONSocketAdapterSTSwithQuiescence quiesenceMillis :: IO (Adapter (Alph.IOSuspGateValue String String) (Maybe (Alph.GateValue String)))
    
    putStrLn $ "starting test..."
    let nrSteps = 50
        probabilityOfWaitForOutput = 0.0
        randomSeed = 456
        testSelector = randomDataOrWaitForOutputTestSelectorFromSeed smtRef randomSeed probabilityOfWaitForOutput `untilCondition` stopAfterSteps nrSteps
                        `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    (verdict, (observed, maybeMq)) <- runTester model testSelector adap
    
    putStrLn $ "verdict: " ++ show verdict
    putStrLn $ "observed: " ++ show observed
    putStrLn $ "final state: " ++ show maybeMq
