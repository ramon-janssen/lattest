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

data State = PickEither | PickEitherIn | Picked2 | Picked1 | Confirm1 | Confirmed1 | Confirm2 | Confirmed2 deriving (Eq, Ord, Show)

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
        switches = nonDetConcTransFromMRel
            [   (0, water, pure (Aut.stsTLoc waterGuard waterAssign, 1) /\ pure (Aut.stsTLoc waterGuard waterAssign, 2)),
                (1, ok, pure (Aut.stsTLoc waterGuard waterAssign, 1) \/ pure (Aut.stsTLoc waterGuard waterAssign, 1)),
                (2, coffee, pure (Aut.stsTLoc waterGuard waterAssign, 1))
            ]
        {-switches = \q -> case q of
            0 -> Map.fromList [(water,NonDet $ Set.singleton (stsTLoc waterGuard waterAssign, 1)),
                                (coffee,NonDet $ Set.singleton (stsTLoc coffeeGuard noAssignment, 2))]
            1 -> Map.fromList [(ok,NonDet $ Set.singleton (stsTLoc okGuard noAssignment, 0))]
            2 -> Map.empty-}
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
    adap <- connectJSONSocketAdapterSTSwithQuiescence quiesenceMillis :: IO (Adapter (Alph.IOSuspGateValue Integer Integer) (Maybe (Alph.GateValue Integer)))
    
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
