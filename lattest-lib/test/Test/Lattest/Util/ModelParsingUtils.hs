{-# LANGUAGE DeriveGeneric #-}
module Test.Lattest.Util.ModelParsingUtils (
testReadAutFile
)
where

import Prelude hiding (take)
import Test.HUnit
import qualified Data.Set as Set

import Lattest.Util.ModelParsingUtils(readAutFile)
import Lattest.Model.Alphabet(IOAct(..))

expectedTransitions :: [(String, IOAct String String, String)]
expectedTransitions = 
    [ ("Idle",         In "coin_i",          "CoinInserted")
    , ("CoinInserted", In "select_coffee_i", "Brewing")
    , ("Brewing",      Out "ready_o",        "Ready")
    , ("Ready",        In "take_cup_i",      "Idle")
    ]

testReadAutFile :: Test
testReadAutFile = TestCase $ do
    let filePath = "./dummy.aut"
        expectedInAlphabet = ["take_cup_i", "select_coffee_i", "coin_i"]
        expectedOutAlphabet = ["ready_o"]
        expectedStates = Set.fromList ["Idle", "Brewing", "CoinInserted", "Ready"]
        expectedInitState = "Idle"

    (inputAlphabet, outputAlphabet, states, initialState, Just transitions) <- readAutFile filePath

    assertEqual "IAlphabet" expectedInAlphabet inputAlphabet
    assertEqual "OAlphabet" expectedOutAlphabet outputAlphabet
    assertEqual "Expected states" expectedStates states
    assertEqual "Initial state" "Idle" initialState
    assertEqual "Transitions" expectedTransitions transitions
