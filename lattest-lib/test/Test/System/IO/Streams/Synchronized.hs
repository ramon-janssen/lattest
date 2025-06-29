module Test.System.IO.Streams.Synchronized (
prop_consumeBufferedWith,
testConsumeBufferedWith_short,
testConsumeBufferedWith,
prop_jsonStream
)
where

import Control.Applicative((<|>))
import Control.Concurrent.STM.TQueue(TQueue, newTQueueIO, writeTQueue, readTQueue, isEmptyTQueue)
import Control.Concurrent(threadDelay)
import Control.Arrow(first)
import Data.Aeson(FromJSON,ToJSON,encode,decode,fromJSON)
import qualified Data.Aeson as Aeson(Result(..))
import Data.Aeson.Parser(jsonNoDup)
import qualified Data.Attoparsec.ByteString.Char8 as Parse
import qualified Data.ByteString.UTF8 as UTF8(fromString,toString)
import Data.Bits.Utils(c2w8)
import Data.ByteString(ByteString)
import Data.ByteString.Lazy(toStrict,fromStrict,snoc)
import qualified Data.ByteString as BS(splitAt,length)
import Data.Functor(void)
import qualified Data.List as List(splitAt)
import Data.Maybe(fromJust, isJust)
import Data.Monoid(mappend,mempty)
import qualified Data.Text as Text(pack, unpack)
import GHC.Conc(atomically, newTVar, readTVar, writeTVar)
import System.IO(hPutStrLn,stderr)
import System.IO.Streams.Synchronized()
import System.IO.Streams.Synchronized (tryReadIO, Streamed(Available), consumeBufferedWith, makeTInputStream)
import qualified System.IO.Streams.Synchronized as Streams (hasInput,read,map)
import System.IO.Streams.Synchronized.Attoparsec(parserToInputStream)
import Test.HUnit
import Test.QuickCheck
import Test.QuickCheck.Monadic (assert, assertWith, monadicIO, run, PropertyM)
import Test.QuickCheck.Arbitrary(Arbitrary,arbitrary)
import Test.QuickCheck.Gen(elements)

data WaitTime = NoWT | ShortWT | LongWT deriving (Eq, Show, Ord)

instance Arbitrary WaitTime where
   arbitrary = elements [NoWT, ShortWT, LongWT]
   shrink NoWT = []
   shrink ShortWT = [NoWT]
   shrink LongWT = [NoWT, ShortWT]

waitTimeToMillis NoWT = 0
waitTimeToMillis ShortWT = 2
waitTimeToMillis LongWT = 20

prop_consumeBufferedWith :: ([[(Int, WaitTime)]], WaitTime) -> Property
prop_consumeBufferedWith = prop_consumeBufferedWith'

prop_consumeBufferedWith' :: (Arbitrary a, Eq a, Show a) => ([[(a, WaitTime)]], WaitTime) -> Property
prop_consumeBufferedWith' (testInput', lastWaitTime) = withMaxSuccess 15 $ monadicIO $ do
    let lastTestInput = (Nothing, lastWaitTime)
    let testInput = mapToLast (fmap (fmap (first Just)) testInput') (\x -> x ++ [lastTestInput]) [lastTestInput]
    queue <- run $ do
        queue' <- newTQueueIO :: IO (TQueue [Maybe a])
        sequence_ $ (atomically . writeTQueue queue' . fmap fst) <$> testInput -- write all lists to the queue, without wait times
        return queue'
    -- test the input stream created with consumeBufferedWith: for random lists of inputs, the stream should produce those original inputs, regardless of random waiting times in between reading
    is <- run $ consumeBufferedWith (readTQueue queue) (not <$> isEmptyTQueue queue)
    let (expected, waitTimes) = unzip $ concat testInput
    assertBufferedIS is expected waitTimes
    hasLast <- run $ atomically $ Streams.hasInput is
    assertWith hasLast "mbt test expected input, received no input at end of test"
    lastInput <- run $ atomically $ Streams.read is
    assertWith (lastInput == Nothing) ("expected Nothing, received " ++ show lastInput ++ " at end of test")
    where
    assertBufferedIS is es wts = assertBufferedIS' is es wts es
    assertBufferedIS' is [] [] es = return ()
    assertBufferedIS' is (e:es) (wt:wts) oes = do
        run $ threadDelay $ waitTimeToMillis wt * 1000
        hasNext <- run $ atomically $ Streams.hasInput is
        assertWith hasNext $ "mbt test expected " ++ show e ++ ", received no input in " ++ show oes
        next <- run $ atomically $ Streams.read is
        assertWith (e == next) ("expected " ++ show e ++ ", received " ++ show next ++ " in " ++ show oes)
        assertBufferedIS' is es wts oes
    mapToLast [] _ a = [a]
    mapToLast [last] f _ = [f last]
    mapToLast (a:as) f _ = (a:mapToLast as f (error "unused"))

testConsumeBufferedWith_short :: Test
testConsumeBufferedWith_short = TestCase $ do
    queue <- newTQueueIO :: IO (TQueue [Maybe a])
    is <- consumeBufferedWith (readTQueue queue) (not <$> isEmptyTQueue queue)
    sequence_ $ (atomically . writeTQueue queue) <$> [[Just "a"],[Nothing]]
    shouldBeA <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking a") (Just "a") shouldBeA
    shouldBeNothing <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking Nothing") (Nothing) shouldBeNothing

testConsumeBufferedWith :: Test
testConsumeBufferedWith = TestCase $ do
    queue <- newTQueueIO :: IO (TQueue [Maybe a])
    is <- consumeBufferedWith (readTQueue queue) (not <$> isEmptyTQueue queue)
    sequence_ $ (atomically . writeTQueue queue) <$> [[Just "a", Just "b"], [Just "c", Just "d"],[Just "e", Nothing]]
    shouldBeA <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking a") (Just "a") shouldBeA
    shouldBeB <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking b") (Just "b") shouldBeB
    shouldBeC <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking c") (Just "c") shouldBeC
    shouldBeD <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking d") (Just "d") shouldBeD
    shouldBeE <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking e") (Just "e") shouldBeE
    shouldBeNothing <- atomically $ Streams.read is
    assertEqual ("testConsumeBufferedWith checking Nothing") (Nothing) shouldBeNothing

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


