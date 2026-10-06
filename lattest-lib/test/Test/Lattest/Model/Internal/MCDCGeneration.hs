module Test.Lattest.Model.Internal.MCDCGeneration (
    mcdcGenerationTests
    ) where

import Test.HUnit

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Lattest.Model.Internal.MCDCGeneration (Expr (..), atoms, mcdcRows, validate)

mcdcGenerationTests :: [Test]
mcdcGenerationTests =
    -- Exact rows. A row is the values of the atoms in alphabetical order, then the value of the expression.
    [ rowsCase "A && B" (a `And` b)
        [ ("TT", True)
        , ("FT", False)
        , ("TF", False)
        ]
    , rowsCase "A && (B || C)" (a `And` (b `Or` c))
        [ ("TTF", True)
        , ("FTF", False)
        , ("TFF", False)
        , ("TFT", True)
        ]
    , rowsCase "((A && B) || (C || D)) && ((E || F) && G))" (((a `And` b) `Or` (c `Or` d)) `And` ((e `Or` f) `And` g))
        [ ("FTFFTFT",False),
        ("FTFTTFT",True),
        ("FTTFTFT",True),
        ("TFFFTFT",False),
        ("TTFFFFT",False),
        ("TTFFFTT",True),
        ("TTFFTFF",False),
        ("TTFFTFT",True)
        ]

    -- Valid suite only: N+1 rows, and an independence pair for each atom. Use this if more than one row set is correct.
    , validCase "(A || B) && (C || D)" ((a `Or` b) `And` (c `Or` d))
    , validCase "not (A && not B) || C" (Not (a `And` Not b) `Or` c)
    , validCase "23 atoms"
        (     Not (a `And` b)
        `And` (     (c `And` Not d `And` Not e)
               `Or` (Not f `And` g `And` Not h)
               `Or` (Not i `And` Not j `And` Not k))
        `And` (     (l `And` m `And` (n `Or` o) `And` p)
               `Or` (q `And` (r `Or` s) `And` Not t)
               `Or` (u `And` (v `Or` w))))

    -- Rejected: an atom occurs more than once.
    , notSingularCase "A && (B || A)" (a `And` (b `Or` a))
    ]
    where
    a = Atom 'A'; b = Atom 'B'; c = Atom 'C'; d = Atom 'D'; e = Atom 'E'; f = Atom 'F'
    g = Atom 'G'; h = Atom 'H'; i = Atom 'I'; j = Atom 'J'; k = Atom 'K'; l = Atom 'L'
    m = Atom 'M'; n = Atom 'N'; o = Atom 'O'; p = Atom 'P'; q = Atom 'Q'; r = Atom 'R'
    s = Atom 'S'; t = Atom 'T'; u = Atom 'U'; v = Atom 'V'; w = Atom 'W'

-- | 'mcdcRows' gives exactly the expected rows, in any order.
rowsCase :: String -> Expr Char -> [(String, Bool)] -> Test
rowsCase name expr expected = TestLabel name $ TestCase $ case mcdcRows expr of
    Left err -> assertFailure $ name ++ ": " ++ err
    Right rows -> assertEqual (name ++ ": rows") (Set.fromList expected) (Set.fromList [ (showRow row, value) | (row, value) <- rows ])
    where
    showRow row = [ if value then 'T' else 'F' | value <- Map.elems row ] -- 'Map.elems' is in key order

-- | 'mcdcRows' gives a minimal unique-cause MC/DC suite.
validCase :: String -> Expr Char -> Test
validCase name expr = TestLabel name $ TestCase $ case mcdcRows expr of
    Left err -> assertFailure $ name ++ ": " ++ err
    Right rows -> do
        assertEqual (name ++ ": number of rows") (length (atoms expr) + 1) (length rows)
        assertBool (name ++ ": not a unique-cause MC/DC suite: " ++ show rows) (validate expr (map fst rows))

-- | 'mcdcRows' rejects the expression.
notSingularCase :: String -> Expr Char -> Test
notSingularCase name expr = TestLabel name $ TestCase $ case mcdcRows expr of
    Left _ -> return ()
    Right rows -> assertFailure $ name ++ ": expected an error, but received: " ++ show rows
