{-# LANGUAGE DeriveGeneric #-}

import Test.Lattest.Adapter.StandardAdapters
import Test.Lattest.Exec.StandardTestControllers
import Test.Lattest.Exec.Testing
import Test.Lattest.Model.StandardAutomata
import Test.Lattest.Model.STSTest
import Test.System.IO.Streams.Synchronized(prop_consumeBufferedWith, testConsumeBufferedWith,testConsumeBufferedWith_short)

import Data.Functor(void)
import System.Timeout(timeout)
import Test.HUnit hiding (Path, path, assert)

import Data.Aeson(FromJSON,ToJSON,encode,decode,fromJSON)
import qualified Data.Aeson as Aeson(Result(..))
import Data.Aeson.Parser(jsonNoDup)
import Data.Bits.Utils(c2w8)
import Data.ByteString(ByteString)
import Data.ByteString.Lazy(toStrict,fromStrict,snoc)
import qualified Data.ByteString as BS(splitAt,length)
import qualified Data.List as List(splitAt)
import Data.Maybe(fromJust, isJust)
import Data.Monoid(mappend,mempty)
import qualified Data.Text as Text(pack, unpack)
import GHC.Conc(atomically, newTVar, readTVar, writeTVar)
import Test.QuickCheck
import Test.QuickCheck.Monadic (assert, assertWith, monadicIO, run, PropertyM)
import System.IO.Streams.Synchronized.Attoparsec(parserToInputStream) -- parserToInputStream :: C8.Parser (Maybe r) -> SInputStream ByteString -> IO (SInputStream r)
import qualified Data.Attoparsec.ByteString.Char8 as Parse
--import qualified Data.ByteString as UTF8(fromString,toString)
import qualified Data.ByteString.UTF8 as UTF8(fromString,toString)
import Control.Applicative((<|>))
import System.IO.Streams.Synchronized(makeTInputStream)
import qualified System.IO.Streams.Synchronized as Streams (read,map)
import System.IO.Streams.Synchronized (tryReadIO, Streamed(Available))
import System.IO(hPutStrLn,stderr)
import Control.Concurrent(threadDelay)

durationSeconds :: Int
durationSeconds = 2

main :: IO ()
main = do
    -- unit tests, for fully written out scenarios
    putStrLn ">>>>>>> HUNIT TEST <<<<<<<<<"
    void $ timeout (durationSeconds * 10000000) $ runTestTT tests
    -- property tests
    --putStrLn ">>>>>>> QUICKCHECK TEST <<<<<<<<<"
    --void $ runQuickCheckTests

runQuickCheckTests :: IO ()
runQuickCheckTests = do
    quickCheckWithTimeout (prop_jsonStream :: [(Int,Bool,Bool)] -> Property)
    quickCheckWithTimeout prop_consumeBufferedWith
    where
    quickCheckWithTimeout prop = quickCheck $ \testparam -> within (durationSeconds * 1000000) (prop testparam)

prop_jsonStream :: (Arbitrary a, FromJSON a, ToJSON a, Show a, Eq a) => [(a,Bool,Bool)] -> Property
prop_jsonStream testInput = monadicIO $ do
    -- first bool in list states that the bytes of the next elements should be appended to the bytes of this elements. If the element is the last one, then this boolean states that the second half is included, as opposed to being omitted entirely (if the element is streamed as half bytestring), or is ignored (if the element is streamed as single bytestring).
    -- second bool in the list state that the bytes of the element should be streamed as two half bytestrings, as opposed to a single bytestring
    -- final bool states whether the bytes of the last bool are incomplete
    -- FIXME this does not test whether checkReadyness which results in False can later be succeeded by True, and by a succesfull read
    (typedData, byteData) <- run $ createTestData testInput -- make an input stream from someData by serializing them as bytestrings reporesenting JSON, and potentially cutting off the bytestring half way
    is <- run $ makeReader byteData
    actionStream <- run $ parserToInputStream ((Parse.endOfInput >> pure Nothing) <|> (Just <$> (Parse.skipSpace *> jsonNoDup))) is
    actionStream' <- run $ Streams.map (fromResult . fromJSON) actionStream
    
    -- assert that the parsed objects are equal to the original objects, minus the cut-off
    --return Discard
    void $ checkObjs actionStream' typedData
    where
    checkObjs actionStream [] = return []
    checkObjs actionStream [x] = checkObj actionStream x >>= \y -> return [y]
    checkObjs actionStream (x:xs) = do
        y <- checkObj actionStream x
        ys <- checkObjs actionStream xs
        return (y:ys)
    checkObj actionStream obj = do
        received <- run $ tryReadIO actionStream
        --assert (isJust maybeReceived)
        assertWith (Available obj == received) ("checkObjs expected " ++ show obj ++ ", received " ++ show received)
        return $ fromAvailable received
    fromAvailable (Available o) = o
    createTestData [] = return ([], [])
    createTestData [(a,app,True)] = do
        let b = encode' a
        (h1, h2) <- splitAtRandom b
        return (if app then [a] else [], h1 : if app then [h2] else [])
    createTestData [(a,_,False)] = return ([a],[encode' a])
    createTestData ((a,app,half):rest) = do
        (as,bytes) <- createTestData rest
        let b = encode' a
        bytes'' <- if half
            then do
                (h1, h2) <- splitAtRandom b
                return $ if app
                    then let ([h2'],bytes') = List.splitAt 1 bytes
                        in h1:(h2 `mappend` h2'):bytes'
                    else h1:h2:bytes
            else return $ if app
                then let ([b'],bytes') = List.splitAt 1 bytes
                    in (b `mappend` b'):bytes'
                else b:bytes
        return (a:as,bytes'')
    splitAtRandom :: ByteString -> IO (ByteString,ByteString)
    splitAtRandom b = 
        if BS.length b > 1
            then do
                i <- generate $ chooseInt (1, BS.length b - 1)
                return $ BS.splitAt i b
            else discard
    encode' = toStrict . (flip snoc $ c2w8 '\n') . encode
    makeReader someData = do
        tSomeData <- atomically $ newTVar someData
        makeTInputStream (consume tSomeData) (return True)
        where
        consume tSomeData = do
            someData <- readTVar tSomeData
            case someData of
                [] -> return Nothing
                (x:xs) -> do
                    writeTVar tSomeData xs
                    return $ Just x
    fromResult (Aeson.Success s) = s
    fromResult (Aeson.Error e) = undefined e -- TODO handle error case

tests :: Test
tests = TestList [
    testConsumeBufferedWith,
    testConsumeBufferedWith_short,
    testJSONSocketAdapterByte,
    testAdapterAcceptingInput,
    testJSONSocketAdapterInt,
    testJSONSocketAdapterObject,
    testTraceHappy,
    testTraceFailsAtLastOutput,
    testTraceFailsBeforeLastOutput,
    testTraceIncompleteAtLastOutput,
    testTraceIncompleteBeforeLastOutput,
    testTraceFailsWithQuiescence,
    testSpecF,
    testPrintSpecF,
    testSpecG,
    testSpecGQuiescent,
    testRandomFCorrect,
    testRandomFIncorrectOutput,
    testRandomFIncorrectInput,
    testSTSHappyFlow,
    testErrorThrowingGates,
    testSTSUnHappyFlow
    ]











