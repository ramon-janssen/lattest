module Lattest.Util.ReportUtils
    ( writeResults
    , flushResults
    , initResultsFile
    , TestResult(..)
    ) where

import Data.Csv (ToRecord(..), record, toField, encode)
import qualified Data.ByteString.Lazy as BL
import Data.Maybe (fromMaybe)

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
    BL.writeFile csvPath (encode [fromMaybe defaultHeader mHeader])

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
    -> [TestResult]
    -> Int
    -> Int
    -> IO ([TestResult], Int)
writeResults csvPath newResults revBuf bufLen threshold = do
    let newRevBuf = reverse newResults ++ revBuf
        newBufLen = bufLen + length newResults
    if threshold == 0 || newBufLen >= threshold
        then do
            BL.appendFile csvPath (encode (reverse newRevBuf))
            return ([], 0)
        else
            return (newRevBuf, newBufLen)

{-| 
    Flush remaining 'TestResult' rows to a CSV file.
    Note: this function assumes the CSV file already exists.
-}
flushResults :: FilePath -> [TestResult] -> IO ()
flushResults csvPath revBuf =
    writeResults csvPath [] revBuf (length revBuf) 0 >> return ()