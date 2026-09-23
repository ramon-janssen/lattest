{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Lattest.Util.STSJSONWriterTest
    ( testSTSJSONWriterComposedConjunction
    , stsJSONWriterTests
    ) where

import Test.HUnit
import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Some (Some (..))
import System.Directory (removeFile)

import Lattest.Model.Alphabet (IOAct (..), SymInteract (..))
import Lattest.Model.Automaton (automaton, stsTLoc)
import Lattest.Model.BoundedMonad (FreeLattice, ordReturn)
import Lattest.Model.StandardAutomata (IOSTS, conjunctionAll)
import Lattest.Model.Symbolic.Expr
import Lattest.Util.STSJSONWriter (stsToJSONFile)

testDir :: FilePath
testDir = "./test/Test/Lattest/Util/STSJSONWriterExamples/"

assertWrittenJSONMatches :: (Ord loc, Show loc) => FilePath     -- expected output path, relative to 'testDir'
                          -> String                             -- STS id
                          -> IOSTS FreeLattice loc String String
                          -> Map.Map (Expr Bool) String
                          -> Map.Map VarModel String
                          -> Valuation
                          -> Assertion
assertWrittenJSONMatches expectedFile sid sts guardmap assmap valuation = do
    let actualFile = testDir ++ "tmp_" ++ expectedFile
    stsToJSONFile actualFile sid sts guardmap assmap valuation
    actualBytes <- BSL.readFile actualFile
    removeFile actualFile
    expectedBytes <- BSL.readFile (testDir ++ expectedFile)
    case (JSON.eitherDecode actualBytes, JSON.eitherDecode expectedBytes) of
        (Right (actual :: JSON.Value), Right (expected :: JSON.Value)) ->
            assertEqual expectedFile expected actual
        (Left err, _) -> assertFailure (expectedFile ++ ": failed to decode written JSON: " ++ err)
        (_, Left err) -> assertFailure (expectedFile ++ ": failed to decode expected JSON fixture: " ++ err)

pvar = Variable "p" IntType
xvar = Variable "x" IntType
yvar = Variable "y" BoolType
labelVar = Variable "label" (ListType CharType)
pairVar = Variable "pair" (TupleType IntType (ListType CharType))
itemsVar = Variable "items" (ListType IntType)
gYTrue = y .== sConst True
gYFalse = y .== sConst False
assignDupX = xvar =: (sVar xvar .+ sConst (1 :: Integer))
assignFlipY = yvar =: sNot y
setPair = pairVar =: sPair (sVar xvar) (sVar labelVar)
p = sVar pvar :: Expr Integer
x = sVar xvar :: Expr Integer
y = sVar yvar :: Expr Bool
outGuardA = 1 .<= p .&& p .<= 2
outGuardB = 2 .<= p .&& p .<= 3

stsGuardedA :: IOSTS FreeLattice Integer String String
stsGuardedA =
    let step = SymInteract (In "step") [Some pvar]
        stepA = SymInteract (In "stepA") []
        outA = SymInteract (Out "outA") []
        outC = SymInteract (Out "outC") [Some pvar]
        pingGate = SymInteract (Out "ping") [Some itemsVar]

        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc gYTrue (assignment [assignFlipY, assignDupX, setPair]), 1)), (stepA, ordReturn (stsTLoc sTrue (assignment [assignDupX]), 3))]
            1 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.fromList [(outC, ordReturn (stsTLoc outGuardA (assignment [assignFlipY]), 0))]
            3 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, stepA, outA, outC, pingGate]) switches

stsGuardedB :: IOSTS FreeLattice Integer String String
stsGuardedB =
    let step = SymInteract (In "step") [Some pvar]
        stepB = SymInteract (In "stepB") []
        outA = SymInteract (Out "outA") []
        outC = SymInteract (Out "outC") [Some pvar]

        initConf = ordReturn 0
        switches q = case q of
            0 -> Map.fromList [(step, ordReturn (stsTLoc gYFalse (assignment [assignFlipY, assignDupX]), 1)), (stepB, ordReturn (stsTLoc sTrue (assignment [assignDupX]), 3))]
            1 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            2 -> Map.fromList [(outC, ordReturn (stsTLoc outGuardB (assignment [assignFlipY]), 0))]
            3 -> Map.fromList [(outA, ordReturn (stsTLoc sTrue noAssignment, 2))]
            _ -> Map.empty
    in automaton initConf (Set.fromList [step, stepB, outA, outC]) switches

testSTSJSONWriterComposedConjunction :: Test
testSTSJSONWriterComposedConjunction = TestCase $
    let sts = conjunctionAll [("A", stsGuardedA), ("B", stsGuardedB)]
        guardmap = Map.fromList [(outGuardA, "GA"), (gYFalse, "YTrue"), (outGuardB, "GB"), (gYTrue, "YFalse"), (sTrue, "True")]
        assmap = Map.fromList
            [ (assignment [assignFlipY], "Flip"), (assignment [assignDupX], "Dup"), (assignment [setPair], "Pair")
            ]
        valuation = Valuation
            $ DMap.insert xvar (Val (5 :: Integer))
            $ DMap.insert yvar (Val True)
            $ DMap.insert itemsVar (Val [1, 2, 3 :: Integer])
            $ DMap.insert pairVar (Val (3 :: Integer, "hi"))
            mempty
    in assertWrittenJSONMatches
        "composed_conjunction_expected.json"
        "composed" sts guardmap assmap valuation

stsJSONWriterTests :: [Test]
stsJSONWriterTests =
    [ testSTSJSONWriterComposedConjunction
    ]
