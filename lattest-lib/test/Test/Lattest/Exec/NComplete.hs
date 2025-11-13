module Test.Lattest.Exec.NComplete(testADG,testAccSeq)
where

import Test.HUnit
import qualified Data.Map as Map (Map,lookup)

import Lattest.Exec.ADG.Aut(adgAutFromAutomaton)
import Lattest.Exec.ADG.DistGraphConstruction(computeAdaptiveDistGraphPure)
import Lattest.Exec.ADG.SplitGraph(Evidence(..))
import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Model.BoundedMonad(Det(..))
import Lattest.Model.StandardAutomata(accessSequences, detConcTransFromRel,ioAlphabet,automaton,interpretQuiescentConcrete, accessSequences)

Just trans = detConcTransFromRel
    [   (1, In "a", 3),
        (1, Out "x", 1),
        (1, Out "y", 1),
        (2, In "a", 4),
        (2, Out "x", 4),
        (3, Out "x", 4),
        (4, Out "y", 2)
    ] :: Maybe (Integer -> Map.Map (IOAct String String) (Det ((), Integer)))
alphabet = ioAlphabet ["a"] ["x", "y"]
initialConfiguration = pure 1
spec = automaton initialConfiguration alphabet trans
model = interpretQuiescentConcrete spec

testADG :: Test
testADG = TestCase $ do
    let adgaut = case adgAutFromAutomaton model "delta" of
            Just a -> a
            Nothing ->  error "could not transform Lattest auomaton into ADG automaton"
        adg = computeAdaptiveDistGraphPure adgaut False True True
    assertEqual "ADG of ADG-journal automaton: " adg
        $ Plus [Prefix "x" $ Plus [Prefix "x" Nil,
                                 Prefix "y" $ Prefix "a" $ Plus [Prefix "x" Nil, Prefix "y" Nil]],
               Prefix "y" $ Prefix "a" $ Plus [Prefix "x" Nil, Prefix "y" Nil]]

testAccSeq :: Test
testAccSeq = TestCase $ do
    let accMap = accessSequences model 1
    assertEqual "empty seq for loc 1" (Just []) $ Map.lookup 1 accMap
    assertEqual "axy expected for loc 2" (Just $ [In "a", Out "x", Out "y"]) $ Map.lookup 2 accMap
    assertEqual "a expected for loc 3" (Just $ [In "a"]) $ Map.lookup 3 accMap
    assertEqual "ax expected for loc 4" (Just $ [In "a", Out "x"]) $ Map.lookup 4 accMap