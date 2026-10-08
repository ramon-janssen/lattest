{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Lattest.Util.ReportUtils
    ( writeResults
    , flushResults
    , initResultsFile
    , TestResult(..)
    , prettyTrace
    , appendTestTrace
    ) where

import Data.Csv (ToRecord(..), record, toField, encode)
import Data.Maybe (fromMaybe)
import Data.Foldable (toList)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Sequence as Seq
import Control.Monad (void)
import Data.Some (Some)

import Lattest.Model.Alphabet (GateValue(..), IOSymInteract, IOAct(..), IOGateValue)
import Lattest.Model.Automaton (IntrpState, STStdest, AutIntrpr, IOAfter, StepSemantics)
import qualified Lattest.Model.BoundedMonad as BM
import Lattest.Model.Symbolic.Expr (Constant)
import Lattest.Model.Symbolic.SolveSTS (OfflineTests, OnlyOrInconclusive, toTrace)


data TestResult = TestResult
    { testNumber :: Int
    , verdict    :: String
    , trace      :: String
    }

defaultHeader :: (String, String, String)
defaultHeader = ("test_number", "verdict", "trace")

{-|
    Initialize a CSV file for test results with an optional header. If no header is
    provided, a default one will be used.
-}
initResultsFile :: FilePath -> Maybe (String, String, String) -> IO ()
initResultsFile csvPath mHeader =
    BS.writeFile csvPath (BL.toStrict (encode [fromMaybe defaultHeader mHeader]))

instance ToRecord TestResult where
    toRecord (TestResult n v t) = record [toField n, toField v, toField t]

{-| 
    Append a list of 'TestResult' rows to a CSV file, with optional buffering given by 'threshold'.
     - If 'threshold' is 0, results are written immediately.
     - If 'threshold' > 0, results are buffered until the buffer length reaches the threshold, at which
     point they are written to the file.
    Returns the updated (reverseBuffer, bufferLength) pair.
    Note: this function assumes the CSV file already exists.
-}
writeResults
    :: FilePath
    -> [TestResult]
    -> Seq.Seq TestResult
    -> Int
    -> IO (Seq.Seq TestResult)
writeResults csvPath newResults buf threshold = do
    let newBuf    = buf Seq.>< Seq.fromList newResults
        newBufLen = Seq.length newBuf
    if threshold == 0 || newBufLen >= threshold
        then do
            BS.appendFile csvPath (BL.toStrict (encode (toList newBuf)))
            return Seq.empty
        else
            return newBuf

{-| 
    Flush remaining 'TestResult' rows to a CSV file.
    Note: this function assumes the CSV file already exists.
-}
flushResults :: FilePath -> Seq.Seq TestResult -> IO ()
flushResults csvPath revBuf =
    void $ writeResults csvPath [] revBuf 0

{-|
    Wrap the output values of a trace in a GateValue, so that they are pretty printed like the inputs (e.g. enums as their index).
-}
prettyTrace :: [IOAct (GateValue i) (o, OnlyOrInconclusive, [Some Constant], st)] -> [IOAct (GateValue i) (GateValue o, OnlyOrInconclusive, st)]
prettyTrace = map prettyOut
  where
    prettyOut (In i) = In i
    prettyOut (Out (o, ooi, cs, st)) = Out (GateValue o cs, ooi, st)

{-|
    Append the given offline test to the given file as its pretty printed trace and verdict.
-}
appendTestTrace :: (forall a. Ord a => Ord (m a), BM.BooleanConfiguration m, Ord i, Ord o, Foldable m, Ord loc, Ord (m (IntrpState loc)), IOAfter m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o), StepSemantics m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o), Show i, Show o, Show r, Show (m (IntrpState loc)))
    => FilePath
    -> AutIntrpr m loc (IntrpState loc) (IOSymInteract i o) STStdest (IOGateValue i o)
    -> OfflineTests i o r
    -> IO ()
appendTestTrace file intrpr test = appendFile file $ show (fmap (\(steps, r) -> (prettyTrace steps, r)) (toTrace intrpr test)) ++ "\n"
