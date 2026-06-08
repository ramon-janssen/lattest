module Lattest.Util.ReportUtils
    ( writeResults
    , flushResults
    , initResultsFile
    , TestResult(..)
    ) where

import Data.Csv (ToRecord(..), record, toField, encode)
import Data.Maybe (fromMaybe)
import Data.Foldable (toList)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Sequence as Seq


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
            return (Seq.empty)
        else
            return newBuf

{-| 
    Flush remaining 'TestResult' rows to a CSV file.
    Note: this function assumes the CSV file already exists.
-}
flushResults :: FilePath -> Seq.Seq TestResult -> IO ()
flushResults csvPath revBuf =
    writeResults csvPath [] (revBuf) 0 >> return ()