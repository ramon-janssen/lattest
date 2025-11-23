{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.Lattest.Util.ModelParsingUtils (
testReadAutFile
)
where

import Prelude hiding (take)
import Test.HUnit
import qualified Data.Set as Set

import Lattest.Util.ModelParsingUtils(readAutFile)
import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Model.BoundedMonad(FreeLattice(..))
import Algebra.Lattice.Free(Free)

expectedTransitions :: [(String, IOAct String String, String)]
expectedTransitions = 
    [ ("Idle",         In "coin_i",          "CoinInserted")
    , ("CoinInserted", In "select_coffee_i", "Brewing")
    , ("Brewing",      Out "ready_o",        "Ready")
    , ("Ready",        In "take_cup_i",      "Idle")
    ]

testReadAutFile :: Test
testReadAutFile = TestCase $ do
    let filePath = "./test/Test/Lattest/Util/dummy.aut"
        expectedInAlphabet = Set.fromList ["take_cup_i", "select_coffee_i", "coin_i"]
        expectedOutAlphabet = Set.fromList ["ready_o"]
        expectedStates = Set.fromList ["Idle", "Brewing", "CoinInserted", "Ready"]
        expectedInitState = "Idle"

    (inputAlphabet, outputAlphabet, states, initialState, Just transitions) <- readAutFile "" (Just filePath)

    assertEqual "IAlphabet" expectedInAlphabet (Set.fromList inputAlphabet)
    assertEqual "OAlphabet" expectedOutAlphabet (Set.fromList outputAlphabet)
    assertEqual "Expected states" expectedStates states
    assertEqual "Initial state" "Idle" initialState
    assertEqual "Transitions" expectedTransitions transitions


