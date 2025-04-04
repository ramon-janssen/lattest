{-# LANGUAGE OverloadedStrings #-}
module Test.Lattest.Model.STSTest (testSTSExample)
where

import Prelude hiding (take)
import Test.HUnit
import qualified Data.Set as Set

import Lattest.Model.Automaton(after, afters, stateConf,automaton,semantics,IntrpState(..),Valuation)
import Lattest.Model.StandardAutomata(semanticsSTS)
import Lattest.Model.Alphabet(IOAct(..), isOutput, TimeoutIO, Timeout(..), asTimeout, δ, SymInteract(..),Gate(..),Variable(..),Type(..),Value(..),GateValue(..),SymExpr(..))
import Lattest.Model.StateConfiguration((/\), (\/), FDL, atom, top, bot, NonDetState(..))
import qualified Data.Map as Map (empty, fromList,singleton)
import Grisette(identifier,(.<=),(.==),(.>),SymBool,SymInteger,Symbol,con,ssym,(.&&))


testSTSExample :: Test
testSTSExample = TestCase $ do
    let pvar = (Variable "p" IntType) -- ssym "p"
        xvar = (Variable "x" IntType) -- ssym "x"
        psym = ssym "p"
        xsym = ssym "x" :: SymInteger
        water = SymInteract (InputGate "water") [pvar]
        ok = SymInteract (OutputGate "ok") [pvar]
        coffee = SymInteract (OutputGate "coffee") []
        waterGuard = 1 .<= psym .&& psym .<= 10
        waterAssign = Map.fromList [(xvar,IntExpr $ xsym + psym)]
        okGuard = xsym .== psym
        coffeeGuard = xsym .> 15
        l0 = 0 :: Integer
        l1 = 1 :: Integer
        l2 = 2 :: Integer
        locConf = NonDet [l0]
        switches = \q -> case q of
            l0 -> Map.fromList [(water,NonDet [((waterGuard,waterAssign), l1)]),
                                (ok,NonDet [((okGuard,Map.empty), l0)])]
            l1 -> Map.fromList [ (coffee,NonDet [((coffeeGuard,Map.empty), l2)])]
            l2 -> Map.empty
        initAssign l = IntrpState l (Map.singleton xvar (IntVal 0))
        sts = automaton locConf (Set.fromList [water,ok,coffee]) switches
        intrp = semanticsSTS sts initAssign
    putStrLn $ show $ stateConf intrp
    let intrp2 = after intrp (GateValue (InputGate "water") [IntVal 7])
    putStrLn $ show $ stateConf intrp2
    return ()