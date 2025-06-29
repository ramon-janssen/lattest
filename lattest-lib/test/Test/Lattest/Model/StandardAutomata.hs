{-# LANGUAGE DeriveGeneric #-}
module Test.Lattest.Model.StandardAutomata (
IF(..),
OF(..),
sf,
IG(..),
OG(..),
sg,
testSpecF,
testPrintSpecF,
testSpecG,
testSpecGQuiescent
)
where

import Prelude hiding (take)
import Test.HUnit

import Lattest.Model.Automaton(after, afters, stateConf, automaton, prettyPrint)
import Lattest.Model.StandardAutomata(semanticsConcrete, semanticsQuiescentConcrete, nonDetConcTransFromMRel)
import Lattest.Model.Alphabet(IOAct(..), isOutput, IOSuspAct, Timeout(..), asTimeout, δ)
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
tf = nonDetConcTransFromMRel
    [(Q0f, af, q0f /\ (q1f \/ q2f))
    ,(Q0f, x, q0f)
    ,(Q0f, y, q0f)
    ,(Q1f, x, top)
    ,(Q2f, bf, q0f)
    ,(Q2f, y, q2f)
    ]
sf = automaton q0f menuf tf

testSpecF :: Test
testSpecF = TestCase $ do
    let rf = semanticsConcrete sf
    assertEqual "sf after ?A !X" q0f (stateConf $ rf `after` af `after` x)
    assertEqual "sf after ?A !Y" (q0f /\ q2f) (stateConf $ rf `after` af `after` y)
    assertEqual "sf after ?A !A" (q0f /\ (q1f \/ q2f)) (stateConf $ rf `after` af `after` af)
    assertEqual "sf after ?A !B" top (stateConf $ rf `after` af `after` bf)

testPrintSpecF :: Test
testPrintSpecF = TestCase $ do
    {-
    initial location configuration: Q0f
    locations: Q0f, Q1f, Q2f
    transitions:
    Q0f ――?A⟶ (((),Q0f) ∧ (((),Q1f) ∨ ((),Q2f)))
    Q0f ――?B⟶ ⊤
    Q0f ――!X⟶ ((),Q0f)
    Q0f ――!Y⟶ ((),Q0f)
    Q1f ――?A⟶ ⊤
    Q1f ――?B⟶ ⊤
    Q1f ――!X⟶ ⊤
    Q1f ――!Y⟶ ⊥
    Q2f ――?A⟶ ⊤
    Q2f ――?B⟶ ((),Q0f)
    Q2f ――!X⟶ ⊥
    Q2f ――!Y⟶ ((),Q2f)
    -}
    assertEqual "print of sf does not match" printF $ prettyPrint sf
    where
    printF =
        "initial location configuration: Q0f\nlocations: Q0f, Q1f, Q2f\ntransitions:\nQ0f \8213\8213?A\10230 (((),Q0f) \8743 (((),Q1f) \8744 ((),Q2f)))\nQ0f \8213\8213?B\10230 \8868\nQ0f \8213\8213!X\10230 ((),Q0f)\nQ0f \8213\8213!Y\10230 ((),Q0f)\nQ1f \8213\8213?A\10230 \8868\nQ1f \8213\8213?B\10230 \8868\nQ1f \8213\8213!X\10230 \8868\nQ1f \8213\8213!Y\10230 \8869\nQ2f \8213\8213?A\10230 \8868\nQ2f \8213\8213?B\10230 ((),Q0f)\nQ2f \8213\8213!X\10230 \8869\nQ2f \8213\8213!Y\10230 ((),Q2f)"


data IG = A2 | B2 | On | Take deriving (Show, Eq, Ord)
data OG = C | T | CM | TM deriving (Show, Eq, Ord)
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

tg = nonDetConcTransFromMRel
    [(Q0g, on, q1g /\ q3g /\ q5g /\ q8g)
    ,(Q1g, ag, q2g)
    ,(Q2g, c,  top)
    ,(Q3g, bg, q4g)
    ,(Q4g, t,  top)
    ,(Q4g, tm, top)
    ,(Q5g, bg, q6g \/ q7g)
    ,(Q6g, cm, top)
    ,(Q7g, tm, top)
    ,(Q8g, ag, q9g)
    ,(Q8g, bg, q9g)
    ,(Q9g, c,  q10g)
    ,(Q9g, t,  q10g)
    ,(Q9g, cm, q10g)
    ,(Q9g, tm, q10g)
    ,(Q10g, take, q1g /\ q3g /\ q5g /\ q8g)
    ]
sg = automaton q0g menug tg

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

