{-# LANGUAGE DeriveGeneric #-}
module Test.Lattest.Model.StandardAutomata (
IF(..),
OF(..),
sf,
IG(..),
OG(..),
sg,
testSpecF,
testSpecG,
testSpecGQuiescent
)
where

import Prelude hiding (take)
import Test.HUnit

import Lattest.Model.Automaton(after, afters, stateConf)
import Lattest.Model.StandardAutomata(aiaWithAlphabet, semanticsConcrete, semanticsQuiescentConcrete)
import Lattest.Model.Alphabet(IOAct(..), isOutput, TimeoutIO, Timeout(..), asTimeout, δ)
import Lattest.Model.StateConfiguration((/\), (\/), FDL, atom, top, bot)
import qualified Data.Map as Map (toList, insert, fromList)

data IF = A | B deriving (Show, Eq, Ord)
data OF = X | Y deriving (Show, Eq, Ord)
data StateF = Q0f | Q1f | Q2f deriving (Show, Eq, Ord)
x = Out X
y = Out Y
af = In A
bf = In B
q0f = atom Q0f
q1f = atom Q1f
q2f = atom Q2f
menuf = [af, bf, x, y]
tf Q0f = Map.fromList [(af, q0f /\ (q1f \/ q2f)), (x, q0f), (y, q0f)]
tf Q1f = Map.fromList [(x, top)]
tf Q2f = Map.fromList [(bf, q0f), (y, q2f)]
sf = aiaWithAlphabet q0f menuf tf

testSpecF :: Test
testSpecF = TestCase $ do
    let rf = semanticsConcrete sf
    assertEqual "sf after ?A !X" q0f (stateConf $ rf `after` af `after` x)
    assertEqual "sf after ?A !Y" (q0f /\ q2f) (stateConf $ rf `after` af `after` y)
    assertEqual "sf after ?A !A" (q0f /\ (q1f \/ q2f)) (stateConf $ rf `after` af `after` af)
    assertEqual "sf after ?A !B" top (stateConf $ rf `after` af `after` bf)

data IG = A2 | B2 | On | Take deriving (Eq, Ord)
data OG = C | T | CM | TM deriving (Eq, Ord)
data StateG = Q0g | Q1g | Q2g | Q3g | Q4g | Q5g | Q6g | Q7g | Q8g | Q9g | Q10g deriving (Show, Eq, Ord)

c = Out C
t = Out T
cm = Out CM
tm = Out TM
ag = In A2
bg = In B2
on = In On
take = In Take
menug = [c, t, cm, tm, ag, bg, on, take]

q0g = atom Q0g
q1g = atom Q1g
q2g = atom Q2g
q3g = atom Q3g
q4g = atom Q4g
q5g = atom Q5g
q6g = atom Q6g
q7g = atom Q7g
q8g = atom Q8g
q9g = atom Q9g
q10g = atom Q10g

tg Q0g = Map.fromList [(on, q1g /\ q3g /\ q5g /\ q8g)]
tg Q1g = Map.fromList [(ag, q2g)]
tg Q2g = Map.fromList [(c, top)]
tg Q3g = Map.fromList [(bg, q4g)]
tg Q4g = Map.fromList [(t, top), (tm, top)]
tg Q5g = Map.fromList [(bg, q6g \/ q7g)]
tg Q6g = Map.fromList [(cm, top)]
tg Q7g = Map.fromList [(tm, top)]
tg Q8g = Map.fromList [(ag, q9g), (bg, q9g)]
tg Q9g = Map.fromList [(c, q10g), (t, q10g), (cm, q10g), (tm, q10g)]
tg Q10g = Map.fromList [(take, q1g /\ q3g /\ q5g /\ q8g)]
sg = aiaWithAlphabet q0g menug tg

testSpecG :: Test
testSpecG = TestCase $ do
    let rg = semanticsConcrete sg
    assertEqual "sg after ?On ?B !T" bot (stateConf $ rg `after` on `after` bg `after` t)
    assertEqual "sg after ?On ?B !TM" q10g (stateConf $ rg `after` on `after` bg `after` tm)

testSpecGQuiescent :: Test
testSpecGQuiescent = TestCase $ do
    let rg = semanticsQuiescentConcrete sg
    assertEqual "Δ(sg) after δ ?On δ ?B !T" bot (stateConf $ rg `afters` [δ, asTimeout on, δ, asTimeout bg, asTimeout t])
    assertEqual "Δ(sg) after δ ?On δ ?B δ" bot (stateConf $ rg `afters` [δ, asTimeout on, δ, asTimeout bg, δ])
    assertEqual "Δ(sg) after δ ?On δ ?B !TM" q10g (stateConf $ rg `afters` [δ, asTimeout on, δ, asTimeout bg, asTimeout tm])
    assertEqual "Δ(sg) after δ ?On δ ?B δ" bot (stateConf $ rg `afters` [δ, asTimeout on, δ, asTimeout bg, δ])
