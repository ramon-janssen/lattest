{-# LANGUAGE OverloadedStrings #-}
module Test.Lattest.Model.STSTest (testSTSHappyFlow,testErrorThrowingGates,testSTSUnHappyFlow,testPrintSTS)
where

import Prelude hiding (take)
import Test.HUnit
import qualified Data.Set as Set

import Lattest.Model.Automaton(after, afters, stateConf,automaton,interpret,IntrpState(..),Valuation,prettyPrintIntrp,stsTLoc)
import Lattest.Model.StandardAutomata(interpretSTS,STSIntrp)
import Lattest.Model.Alphabet(IOAct(..), isOutput, IOSuspAct, Suspended(..), asSuspended, δ, SymInteract(..),Gate(..),Variable(..),Type(..),Value(..),GateValue(..),SymExpr(..), assignment, noAssignment)
import Lattest.Model.StateConfiguration((/\), (\/), FreeLattice, atom, top, bot, NonDet(..),underspecified,forbidden)
import qualified Data.Map as Map (empty, fromList,singleton)
import Grisette(identifier,(.<=),(.==),(.>),SymBool,SymInteger,Symbol,con,ssym,(.&&))
import qualified Control.Exception as Exception


stsExample :: STSIntrp NonDet Integer String String
stsExample =
    let pvar = (Variable "p" IntType)
        xvar = (Variable "x" IntType)
        psym = ssym "p"
        xsym = ssym "x" :: SymInteger
        water = SymInteract (InputGate "water") [pvar]
        ok = SymInteract (OutputGate "ok") [pvar]
        coffee = SymInteract (OutputGate "coffee") []
        waterGuard = 1 .<= psym .&& psym .<= 10
        waterAssign = assignment [(xvar,IntExpr $ xsym + psym)]
        okGuard = xsym .== psym
        coffeeGuard = xsym .> 15
        initConf = NonDet [0] :: NonDet Integer
        switches = \q -> case q of
            0 -> Map.fromList [(water,NonDet [(stsTLoc waterGuard waterAssign, 1)]),
                                (coffee,NonDet [(stsTLoc coffeeGuard noAssignment, 2)])]
            1 -> Map.fromList [(ok,NonDet [(stsTLoc okGuard noAssignment, 0)])]
            2 -> Map.empty
        initAssign l = IntrpState l (Map.singleton xvar (IntVal 0))
        sts = automaton initConf (Set.fromList [water,ok,coffee]) switches
    in interpretSTS sts initAssign


getSTSIntrpState :: Integer ->  Integer -> NonDet (IntrpState Integer)
getSTSIntrpState loc val = NonDet [IntrpState loc $ Map.singleton (Variable "x" IntType) (IntVal val)]

testSTSHappyFlow :: Test
testSTSHappyFlow = TestCase $ do
    assertEqual "\ninitial state " (getSTSIntrpState 0 0) (stateConf stsExample)
    let intrp2 = after stsExample (GateValue (InputGate "water") [IntVal 7])
    assertEqual "after water 7: " (getSTSIntrpState 1 7) (stateConf intrp2)
    let intrp3 = after intrp2 (GateValue (OutputGate "ok") [IntVal 7])
    assertEqual "after ok 7: " (getSTSIntrpState 0 7) (stateConf intrp3)
    let intrp4 = after intrp3 (GateValue (InputGate "water") [IntVal 9])
    assertEqual "after water 9: " (getSTSIntrpState 1 16) (stateConf intrp4)
    let intrp5 = after intrp4 (GateValue (OutputGate "ok") [IntVal 16])
    assertEqual "after ok 16: " (getSTSIntrpState 0 16) (stateConf intrp5)
    let intrp6 = after intrp5 (GateValue (OutputGate "coffee") [])
    assertEqual "after coffee: " (getSTSIntrpState 2 16) (stateConf intrp6)
    return()

testErrorThrowingGates :: Test
testErrorThrowingGates = TestCase $ do
    let intrp1 = after stsExample (GateValue (OutputGate "water") [IntVal 7])
    assertThrowsError "gate not in STS alphabet" (stateConf $ intrp1)
    let intrp2 = after stsExample (GateValue (InputGate "water") [])
    assertThrowsError "nr of values unequal to nr of parameters" (stateConf $ intrp2)
    let intrp3 = after stsExample (GateValue (InputGate "water") [BoolVal True])
    assertThrowsError "type of variable and value do not match" (stateConf $ intrp3)

testSTSUnHappyFlow :: Test
testSTSUnHappyFlow = TestCase $ do
    let intrp3 = after stsExample (GateValue (OutputGate "ok") [IntVal 0]) -- output not enabled
    assertEqual "after ok: " forbidden (stateConf intrp3)
    let intrp4 = after stsExample (GateValue (InputGate "water") [IntVal 11]) -- value for input does not satisfy guard
    assertEqual "after water 11: " underspecified (stateConf intrp4)
    let intrp5 = after stsExample (GateValue (OutputGate "coffee") []) -- value of variable does not satisfy guard
    assertEqual "after coffee: " forbidden (stateConf intrp5)

assertThrowsError :: String -> a -> IO ()
assertThrowsError expectedError someVal = do
    actualError <- Exception.handle handler $ do
        Exception.evaluate someVal
        return Nothing -- no exception thrown, so no error message
    assertEqual "expected error: " (Just expectedError) actualError
    where
        handler :: Exception.ErrorCall -> IO (Maybe String)
        handler ex = return $ Just $ show ex

testPrintSTS :: Test
testPrintSTS = TestCase $ do
    assertEqual "print of STS does not match " printSTS $ prettyPrintIntrp stsExample
    where
    {-
    current state configuration: [IntrpState 0 (fromList [(x:Int,IntVal 0)])]
    initial location configuration: [0]
    locations: 0, 1, 2
    transitions:
    0 ――In "water" [p:Int]⟶ [([[(&& (<= 1 p) (<= -10 (- p)))]] {x:Int:=(+ x p)},1)]
    0 ――Out "coffee" []⟶ [([[(< 15 x)]] {},2)]
    0 ――Out "ok" [p:Int]⟶ []
    1 ――In "water" [p:Int]⟶ []
    1 ――Out "coffee" []⟶ []
    1 ――Out "ok" [p:Int]⟶ [([[(= x p)]] {},0)]
    2 ――In "water" [p:Int]⟶ []
    2 ――Out "coffee" []⟶ []
    2 ――Out "ok" [p:Int]⟶ []
    -}
    printSTS = "current state configuration: [IntrpState 0 (fromList [(x:Int,IntVal 0)])]\ninitial location configuration: [0]\nlocations: 0, 1, 2\ntransitions:\n0 \8213\8213In \"water\" [p:Int]\10230 [([[(&& (<= 1 p) (<= -10 (- p)))]] {x:Int:=(+ x p)},1)]\n0 \8213\8213Out \"coffee\" []\10230 [([[(< 15 x)]] {},2)]\n0 \8213\8213Out \"ok\" [p:Int]\10230 []\n1 \8213\8213In \"water\" [p:Int]\10230 []\n1 \8213\8213Out \"coffee\" []\10230 []\n1 \8213\8213Out \"ok\" [p:Int]\10230 [([[(= x p)]] {},0)]\n2 \8213\8213In \"water\" [p:Int]\10230 []\n2 \8213\8213Out \"coffee\" []\10230 []\n2 \8213\8213Out \"ok\" [p:Int]\10230 []"
