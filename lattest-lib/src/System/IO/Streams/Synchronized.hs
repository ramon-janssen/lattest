module System.IO.Streams.Synchronized (
TInputStream,
read,
readAll,
unRead,
hasInput,
fromInputStreamBuffered,
makeTInputStream,
fromBuffer,
fromTMVar,
duplicate,
map,
mapUnbuffered,
mergeBuffered,
mergeBufferedWith,
consumeBufferedWith,
Streamed(..),
tryRead,
tryReadIO,
tryReadIO'
)
where

import Prelude hiding (read, map)
import Control.Concurrent.STM(STM, orElse, retry)
import Control.Concurrent.STM.TQueue(TQueue, newTQueueIO, writeTQueue, readTQueue, isEmptyTQueue, unGetTQueue)
import Control.Concurrent.STM.TMVar(TMVar, newTMVarIO, takeTMVar, isEmptyTMVar)
import Control.Concurrent.STM.TVar(TVar, newTVarIO, readTVar, writeTVar)
import Control.Exception(throwIO, Exception)
import Control.Monad (void)
import Data.List(singleton)
import Data.Maybe(isJust)
import GHC.Conc (atomically, forkIO)
import System.IO.Streams (InputStream, OutputStream, makeInputStream, makeOutputStream, connect)
import qualified System.IO.Streams.Combinators as Streams (map)
import qualified System.IO.Streams as Streams (read, write, writeTo)
import Control.Monad.Extra((||^), (&&^))

data TInputStream a = TInputStream {
    tRead :: STM (Maybe a),
    tUnRead :: a -> STM (),
    tHasInput :: STM Bool -- whether this stream has a (Maybe a) available right now, *or* whether it is closed. Note: it may be tempting
                          -- to omit this field, and just check whether tRead retries, but that is ambiguous: tRead will retry either if
                          -- there is no input yet, *or* if someone is writing to the unknown TVars used to implement tRead. The first case
                          -- would not have an input, the second case would.
    }

read :: TInputStream a -> STM (Maybe a)
read = tRead

hasInput :: TInputStream a -> STM Bool
hasInput = tHasInput

-- read inputs from the stream until it has no more input
readAll :: TInputStream a -> STM [Maybe a]
readAll tis = reverse <$> readAll' []
    where
    readAll' acc = do
        readAttempt <- tryRead tis
        case readAttempt of
            StreamClosed -> return (Nothing:acc)
            Unavailable -> return acc
            Available next -> readAll' (Just next:acc)

unRead :: a -> TInputStream a -> STM ()
unRead = flip tUnRead

data Streamed a = Available a | Unavailable | StreamClosed deriving (Eq, Ord, Show, Read)

tryRead :: TInputStream a -> STM (Streamed a)
tryRead tis = do
    ready <- hasInput tis
    if ready
        then do
            minput <- read tis
            return $ case minput of
                Nothing -> StreamClosed
                Just input -> Available input
        else return Unavailable

tryReadIO :: TInputStream a -> IO (Streamed a)
tryReadIO = atomically . tryRead

data TInputStreamClosedException = TInputStreamClosedException deriving (Eq, Ord, Show)
instance Exception TInputStreamClosedException

tryReadIO' :: TInputStream a -> IO (Maybe a)
tryReadIO' tis = do
    streamed <- tryReadIO tis
    case streamed of
        Available a -> return $ Just a
        Unavailable -> return Nothing
        StreamClosed -> throwIO TInputStreamClosedException

makeTInputStream :: STM (Maybe a) -> STM Bool -> IO (TInputStream a)
makeTInputStream readInput hasInput' = do
    pushbackStack <- newTQueueIO
    withClosedState $ TInputStream {
        tRead = do
            hasPushback <- isNonEmptyTQueue pushbackStack
            if hasPushback
                then Just <$> readTQueue pushbackStack
                else readInput,
        tUnRead = unGetTQueue pushbackStack,
        tHasInput = (isNonEmptyTQueue pushbackStack) ||^ hasInput'
        }

withClosedState :: TInputStream a -> IO (TInputStream a)
withClosedState stream = do
    closeVar <- newTVarIO False
    return $ TInputStream {
        tRead = do
            closed <- readTVar closeVar
            if closed
                then return Nothing
                else do
                    mi <- tRead stream
                    case mi of
                        Just i -> return $ Just i
                        Nothing -> do
                            writeTVar closeVar True
                            return Nothing,
        tUnRead = tUnRead stream,
        tHasInput = do
            closed <- readTVar closeVar
            if closed
                then return True
                else tHasInput stream
        }

fromTMVar :: TMVar (Maybe a) -> IO (TInputStream a)
fromTMVar tmvar = makeTInputStream (takeTMVar tmvar) (not <$> isEmptyTMVar tmvar)

-- note: the buffer is also used to push back values. Thus, do not read this buffer from outside the resulting stream, as then this stream may
-- violate the principle that pushed back values are read again.
fromBuffer :: TQueue (Maybe a) -> IO (TInputStream a)
fromBuffer buffer = withClosedState $ TInputStream {
        tRead = readTQueue buffer,
        tUnRead = \a -> unGetTQueue buffer (Just a),
        tHasInput = isNonEmptyTQueue buffer
    }

-- a synchronized input stream that reads from the given input stream. A monitoring thread reads the given input stream and buffers the inputs on the background
-- TODO support a bound for the buffer
fromInputStreamBuffered :: InputStream a -> IO (TInputStream a)
fromInputStreamBuffered is = do
    buffer <- newTQueueIO
    bufferOS <- makeOutputStream $ atomically . writeTQueue buffer -- an intermediate output stream to write to the queue
    void $ forkIO $ connect is bufferOS -- move items from the original adapter into the buffer in a separate thread
    fromBuffer buffer

mapUnbuffered :: (a -> b) -> (b -> a) -> TInputStream a -> TInputStream b -- we need an inverse to push a's back to the original TInputStream of b's
mapUnbuffered f f' tis = TInputStream { -- FIXME either remove or wrap in withClosedState
    tRead = fmap (fmap f) $ read tis,
    tUnRead = tUnRead tis . f',
    tHasInput = tHasInput tis
    }

map :: (a -> b) -> TInputStream a -> IO (TInputStream b) 
map f tis = makeTInputStream (fmap f <$> read tis) (hasInput tis)

-- Take inputs from both given input streams. If both streams have an input available, the first stream takes precedence. The resulting stream closes 
-- if either given stream closes. The merge is buffered, so that the sequence of arrival of inputs in both streams is preserved, even if the resulting
-- stream is not read.
mergeBuffered :: TInputStream a -> TInputStream a -> IO (TInputStream a)
mergeBuffered = mergeBufferedWith $ \tis1 tis2 -> singleton <$> do
    ready1 <- hasInput tis1
    if ready1
        then read tis1
        else do
            ready2 <- hasInput tis2
            if ready2
                then read tis2
                else retry

-- Take inputs from both given input streams, using the given combinator function. The merge is buffered, so that the sequence of arrival of inputs in both streams is preserved,
-- even if the resulting stream is not read. The resulting stream closes if either given stream closes.
mergeBufferedWith :: (TInputStream a -> TInputStream a -> STM [Maybe a]) -> TInputStream a -> TInputStream a -> IO (TInputStream a)
mergeBufferedWith merge tis1 tis2 = consumeBufferedWith (merge tis1 tis2) (hasAnyInput tis1 tis2) -- FIXME if one stream closes, then no further inputs should be read from the other stream, and only Nothings should be returned instead

hasAnyInput :: TInputStream a -> TInputStream a -> STM Bool
hasAnyInput tis1 tis2 = hasInput tis1 ||^ hasInput tis2

-- Actively take inputs from the given list STM, via a separate thread. This ensures that ordering from the given list STM is preserved as much as possible,
-- in case of concurrent inputs. The resulting stream only reads via the separate thread if needed, and reads from the list STM directly if this is faster.
-- The resulting stream closes if the consumer closes. This function assumes that the given STMs close properly, i.e., no Just's are sent after a Nothing
consumeBufferedWith :: (STM [Maybe a]) -> STM Bool -> IO (TInputStream a)
consumeBufferedWith producer producerHasInput = do
    buffer <- newTQueueIO
    let writeToBuffer = writeTQueue buffer
    --bufferOS <- makeOutputStream $ \x -> putStrLn "Synchronized.merging" >> (atomically . writeTQueue buffer) x -- an intermediate output stream to write to the queue
    void $ forkIO $ bufferLoop writeToBuffer -- move items from the original streams into the buffer in a separate thread
    bufferIS <- fromBuffer buffer
    return $ bufferIS {
        tRead = pickOneAndMergeRest buffer writeToBuffer,
        tHasInput = hasInput bufferIS ||^ producerHasInput
        }
    where
    bufferLoop writeToBuffer = do
        continue <- atomically $ do
            produced <- producer
            writeSeqTo produced writeToBuffer
        if continue
            then bufferLoop writeToBuffer
            else return ()
    writeSeqTo [] _ = return True  -- TODO this is an OutputStream utils function, similar to Streams.write/writeTo, move to an appropriate module
    writeSeqTo (Nothing:_) writeToBuffer = do
        writeToBuffer Nothing
        return False
    writeSeqTo (Just a:as) writeToBuffer = do
        writeToBuffer (Just a)
        writeSeqTo as writeToBuffer
    pickOneAndMergeRest buffer writeToBuffer = do
        bufferHasInput <- not <$> isEmptyTQueue buffer
        produced <- if bufferHasInput
            then singleton <$> readTQueue buffer
            else producer
        case produced of
            [] -> retry
            (Just x:xs) -> do
                void $ writeSeqTo xs writeToBuffer
                return $ Just x
            (Nothing:_) -> do
                unGetTQueue buffer Nothing
                return Nothing

{-
-- TODO either remove or expose as nice util function, even though we don't seem to need this now
tconnect :: TInputStream a -> OutputStream a -> IO ()
tconnect tis os = tconnect'
    where
    tconnect' = do
        mA <- atomically $ read tis
        case mA of
            Nothing -> Streams.write Nothing os
            Just _ -> do
                Streams.write mA os
                tconnect'
-}

-- FIXME split to a separate module, conceptually there's nothing synchronized about this w.r.t. other OutputStreams
duplicate :: OutputStream a -> OutputStream a -> IO (OutputStream a)
duplicate out1 out2 = makeOutputStream $ \maybeVal -> do
    Streams.write maybeVal out1
    Streams.write maybeVal out2

isNonEmptyTQueue :: TQueue a -> STM Bool
isNonEmptyTQueue queue = not <$> isEmptyTQueue queue
