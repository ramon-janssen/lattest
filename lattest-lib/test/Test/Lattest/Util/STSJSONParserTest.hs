module Test.Lattest.Util.STSJSONParserTest
    ( testSTSJSONParserNominal
    , testSTSJSONParserUnknownType
    , testSTSJSONParserAssignmentTypeMismatch
    , testSTSJSONParserGuardTypeMismatch
    , testSTSJSONParserGateIdDup
    , testSTSJSONParserUnsupportedGuardOperand
    , testSTSJSONParserUnsupportedAssignmentOperand
    , testSTSJSONParserMissingSwitches
    , testSTSJSONParserMissingGates
    , stsJSONParserTests
    ) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Text.RawString.QQ as QQ
import Test.HUnit
import Lattest.Model.Alphabet(IOAct(..), SymInteract(..))
import Lattest.Model.Automaton(alphabet, prettyPrintIntrp)
import Lattest.Model.StandardAutomata(interpretSTS)
import Lattest.Model.Symbolic.Expr(Constant(..), Type(..), Variable(..), fromConstantsMap)
import Lattest.Util.STSJSONParser(stsFromJSONFile)
import qualified Lattest.Util.IOUtils as QQ
import qualified Control.Monad as QQ

testDir :: FilePath
testDir = "./test/Test/Lattest/Util/STSJSONExamples/"

-- Check that the error string contains the expected substring.
assertErrorContains :: String -> String -> Either String a -> Assertion
assertErrorContains label errsubstr (Right _)  =
    assertFailure (label ++ ": expected an error containing '" ++ errsubstr ++ "', but parsing succeeded")
assertErrorContains label errsubstr (Left err) =
    assertBool
        (label ++ ": expected error to contain '" ++ errsubstr ++ "', got: " ++ err)
        (errsubstr `isInfixOf` err)


{-
Evaluate nominal case with:
- a variety of variable types (Int, String, Bool)
- (some) shortnames for gates
- multiple assignments in a single switch
- multiple switches with the same gate but different guards and assignments
-}
testSTSJSONParserNominal :: Test
testSTSJSONParserNominal = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "nominal_all_types.json")
    case result of
        Left err -> assertFailure ("expected successful parse, got: " ++ err)
        Right (sts, valuation) -> do
            assertEqual "initial valuation"
                (fromConstantsMap $ Map.fromList
                    [ (Variable "counter" IntType,    Cint    5    )
                    , (Variable "label"   StringType, Cstring ""   )
                    , (Variable "active"  BoolType,   Cbool   False)
                    ])
                valuation
            assertEqual "alphabet"
                (Set.fromList
                    [ SymInteract (In  "register")  [Variable "label_p"   StringType]
                    , SymInteract (In  "update")    [Variable "counter_p" IntType   ]
                    , SymInteract (Out "O1")        []
                    , SymInteract (Out "confirm")   [Variable "counter_p" IntType   ]
                    ])
                (alphabet sts)
            assertBool failureMessage (expected == actual)
                where
                intrpsts = interpretSTS sts valuation
                actual   = "\n" ++ prettyPrintIntrp intrpsts ++ "\n"
                failureMessage = "print of STS does not match, expected:" ++ expected ++ "but received:" ++ actual
                expected = "lala"


----- Non-nominal cases -----

-- Variable type "dummyType" is not recognised as a type.
testSTSJSONParserUnknownType :: Test
testSTSJSONParserUnknownType = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "unknown_type.json")
    assertErrorContains "unknown type" "unknown variable type: dummyType" result

-- Variable "label" has type String but the assignment expression is an integer literal.
testSTSJSONParserAssignmentTypeMismatch :: Test
testSTSJSONParserAssignmentTypeMismatch = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "assignment_type_mismatch.json")
    assertErrorContains "Test assignment type mismatch" "not a string expression" result

-- Guard compares integer with string using ==
testSTSJSONParserGuardTypeMismatch :: Test
testSTSJSONParserGuardTypeMismatch = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "guard_type_mismatch.json")
    assertErrorContains "Test guard type mismatch" "not a string expression" result

-- Switch refers to an undefined gate
testSTSJSONParserGateIdDup :: Test
testSTSJSONParserGateIdDup = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "gate_id_dup.json")
    assertErrorContains "Test gate id inconsistency" "unknown gate" result

-- Guard expression uses operator "??" which is not handled by toBoolExpr.
testSTSJSONParserUnsupportedGuardOperand :: Test
testSTSJSONParserUnsupportedGuardOperand = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "unsupported_guard_operand.json")
    assertErrorContains "Test unsupported guard operand" "not a boolean expression" result

-- Assignment expression uses an unsupported operator
testSTSJSONParserUnsupportedAssignmentOperand :: Test
testSTSJSONParserUnsupportedAssignmentOperand = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "unsupported_assignment_operand.json")
    assertErrorContains "Test unsupported assignment operand" "not an integer expression" result

-- The mandatory "switches" field is absent from the JSON.
testSTSJSONParserMissingSwitches :: Test
testSTSJSONParserMissingSwitches = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "missing_switches.json")
    assertErrorContains "Test missing switches" "switches" result
    assertErrorContains "Test missing switches" "not found" result

-- A used input gate is absent from the JSON.
testSTSJSONParserMissingGates :: Test
testSTSJSONParserMissingGates = TestCase $ do
    result <- stsFromJSONFile (testDir ++ "missing_gates.json")
    assertErrorContains "Test missing inputGates" "unknown gate 'I1' in switch" result

stsJSONParserTests :: [Test]
stsJSONParserTests =
    [ testSTSJSONParserNominal
    , testSTSJSONParserUnknownType
    , testSTSJSONParserAssignmentTypeMismatch
    , testSTSJSONParserGuardTypeMismatch
    , testSTSJSONParserGateIdDup
    , testSTSJSONParserUnsupportedGuardOperand
    , testSTSJSONParserUnsupportedAssignmentOperand
    , testSTSJSONParserMissingSwitches
    , testSTSJSONParserMissingGates
    ]
