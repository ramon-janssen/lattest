{-# LANGUAGE OverloadedStrings #-}
module Test.Lattest.Model.STSTest ()
where

import Prelude hiding (take)
import Test.HUnit

import Lattest.Model.Automaton(after, afters, stateConf,automaton)
import Lattest.Model.StandardAutomata(aiaWithAlphabet, semanticsConcrete, semanticsQuiescentConcrete)
import Lattest.Model.Alphabet(IOAct(..), isOutput, TimeoutIO, Timeout(..), asTimeout, δ, SymInteract(..),Gate(..))
import Lattest.Model.StateConfiguration((/\), (\/), FDL, atom, top, bot, NonDetState(..))
import qualified Data.Map as Map (empty, fromList)
import Grisette(identifier,(.<=),(.==),(.>),SymBool,SymInteger,Symbol,con,ssym,(.&&))


testSTSExample :: Test
testSTSExample = TestCase $ do
    let p = ssym "p"
        x = ssym "x"
        c1 = con 1 :: SymInteger
        c10 = con 10 :: SymInteger
        c15 = con 15 :: SymInteger
        water = SymInteract (InputGate "water") ["p"]
        ok = SymInteract (OutputGate "ok") ["p"]
        coffee = SymInteract (OutputGate "coffee") []
        waterGuard = c1 .<= p .&& p .<= c10
        waterAssign = Map.fromList [("x",x + p)]
        okGuard = x .== p
        coffeeGuard = x .> c15
        l0 = 0 :: Integer
        l1 = 1 :: Integer
        l2 = 2 :: Integer
        locConf = NonDet [l0]
        switches = \q -> case q of
            l0 -> Map.fromList [(water,NonDet [((waterGuard,waterAssign), l1)]),
                                (ok,NonDet [((okGuard,Map.empty), l0)])]
            l1 -> Map.fromList [ (coffee,NonDet [((coffeeGuard,Map.empty), l2)])]
            l2 -> Map.empty
        sts = automaton locConf switches
    return ()