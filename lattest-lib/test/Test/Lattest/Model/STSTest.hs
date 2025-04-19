{-# LANGUAGE OverloadedStrings #-}
module Test.Lattest.Model.STSTest (testSTSHappyFlow,testErrorThrowingGates,testSTSUnHappyFlow)
where

import Prelude hiding (take)
import Test.HUnit
import qualified Data.Set as Set

import Lattest.Model.Automaton(after, afters, stateConf,automaton,semantics)
import Lattest.Model.StandardAutomata(semanticsSTS,STSIntrp,IntrpState(..),Valuation, SymInteract(..),Gate(..),Variable(..),Type(..),Value(..),GateValue(..),SymExpr(..))
import Lattest.Model.Alphabet(IOAct(..), isOutput, TimeoutIO, Timeout(..), asTimeout, δ)
import Lattest.Model.StateConfiguration((/\), (\/), FDL, atom, top, bot, NonDetState(..),underspecified,forbidden)
import qualified Data.Map as Map (empty, fromList,singleton)
import Grisette(identifier,(.<=),(.==),(.>),SymBool,SymInteger,Symbol,con,ssym,(.&&))
import qualified Control.Exception as Exception


stsExample :: STSIntrp NonDetState Integer String String
stsExample =
    let pvar = (Variable "p" IntType)
        xvar = (Variable "x" IntType)
        psym = ssym "p"
        xsym = ssym "x" :: SymInteger
        water = SymInteract (InputGate "water") [pvar]
        ok = SymInteract (OutputGate "ok") [pvar]
        coffee = SymInteract (OutputGate "coffee") []
        waterGuard = 1 .<= psym .&& psym .<= 10
        waterAssign = Map.fromList [(xvar,IntExpr $ xsym + psym)]
        okGuard = xsym .== psym
        coffeeGuard = xsym .> 15
        locConf = NonDet [0] :: NonDetState Integer
        switches = \q -> case q of
            0 -> Map.fromList [(water,NonDet [((waterGuard,waterAssign), 1)]),
                                (coffee,NonDet [((coffeeGuard,Map.empty), 2)])]
            1 -> Map.fromList [(ok,NonDet [((okGuard,Map.empty), 0)])]
            2 -> Map.empty
        initAssign l = IntrpState l (Map.singleton xvar (IntVal 0))
        sts = automaton locConf (Set.fromList [water,ok,coffee]) switches
    in semanticsSTS sts initAssign


getSTSIntrpState :: Integer ->  Integer -> NonDetState (IntrpState Integer)
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
