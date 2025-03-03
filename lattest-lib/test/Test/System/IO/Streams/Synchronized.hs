module Test.System.IO.Streams.Synchronized (
prop_consumeBufferedWith,
testConsumeBufferedWith_short,
testConsumeBufferedWith
)
where

import Test.QuickCheck
import Test.QuickCheck.Monadic (assert, assertWith, monadicIO, run, PropertyM)
import Control.Concurrent.STM.TQueue(TQueue, newTQueueIO, writeTQueue, readTQueue, isEmptyTQueue)
import Test.QuickCheck.Arbitrary(Arbitrary,arbitrary)
import Test.QuickCheck.Gen(elements)
import Control.Concurrent(threadDelay)
import qualified System.IO.Streams.Synchronized as Streams (hasInput,read,map)
import Control.Arrow(first)
import System.IO.Streams.Synchronized (consumeBufferedWith)
import System.IO(hPutStrLn,stderr)
import GHC.Conc(atomically)

import Test.HUnit



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
prop_consumeBufferedWith' (testInput', lastWaitTime) = withMaxSuccess 20 $ monadicIO $ do
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



