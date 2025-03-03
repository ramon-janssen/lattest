module Lattest.Adapter.Adapter (
-- * Definition
Adapter(..),
-- * Interaction 
send,
observe,
tryObserve,
-- * Transformations
map,
mapInputCommands,
mapActionsFromSut,
parseActionsFromSut
)
where

import Prelude hiding (map)

--import Lattest.Util.ReadynessInputStream (ReadynessInputStream(..), duplicate, forkEagerInputStream)
import Control.Monad (void)
import Control.Monad.Extra ((||^))
import Control.Concurrent.STM.TQueue(newTQueueIO, writeTQueue, readTQueue, isEmptyTQueue)
import Control.Concurrent.STM.TVar(TVar, newTVarIO, writeTVar, readTVar)
import Data.Attoparsec.ByteString(Parser)
import Data.ByteString(ByteString)
import Control.Monad.STM(atomically, retry, check)
import System.IO.Streams (InputStream, OutputStream, makeInputStream, makeOutputStream, connect)
import qualified System.IO.Streams as Streams (write, writeTo)
import qualified System.IO.Streams.Synchronized as Streams (read)
import System.IO.Streams.Synchronized(TInputStream, makeTInputStream, fromInputStreamBuffered, duplicate, tryReadIO, tryReadIO', fromBuffer, mergeBufferedWith, mapUnbuffered, fromTMVar, readAll, hasInput, Streamed)
import qualified System.IO.Streams.Synchronized as Streams (map)
import System.IO.Streams.Synchronized.Attoparsec (parserToInputStream)
import System.IO.Streams.Combinators(contramap)

-- | An adapter to a (usually external) system. Uses two channels for interaction: one to send input commands, and one to receive outputs.
data Adapter act i = Adapter {
    inputCommandsToSut :: OutputStream i, -- ^ Channel for sending input commands.
    actionsFromSut :: TInputStream act, -- ^ Channel for receiving outputs.
    
    -- TODO should calling close somehow also automatically send a Nothing to the inputCommandsToSut?
    close :: IO () -- ^ Close the (channels of this) adapter.
    }

{-instance AbstractAdapter BlockingAdapter where
    inputCommandsToSut = blockingInputCommandsToSut
    actionsFromSut = blockingActionsFromSut
    unblockedActionsFromSut adap = do
        unblockedActions <- forkEagerInputStream $ blockingActionsFromSut adap
        return $ Adapter {
            readyInputCommandsToSut = blockingInputCommandsToSut adap,
            readyActionsFromSut = unblockedActions,
            readyClose = close adap
        }
    close = blockingClose
-}

{-|
    Try to observe, without blocking, with three possible outcomes:

    * An observation is made,
    * no observation was ready, so no observation was made but another attempt may make an observation,
    * The stream has closed, and any further attempts will give the same result.
-}
tryObserve :: Adapter act i -> IO (Streamed act)
tryObserve = tryReadIO . actionsFromSut

tryObserve' :: Adapter act i -> IO (Maybe act)
tryObserve' = tryReadIO' . actionsFromSut

-- | Send an input to the adapter.
send :: i -> Adapter act i -> IO ()
send i adap = Streams.write (Just i) (inputCommandsToSut adap)

sendMaybe :: Maybe i -> Adapter act i -> IO ()
sendMaybe Nothing adap = close adap -- TODO does this close adaps too eagerly?
sendMaybe (Just i) adap = send i adap

{-|
    Observe in a blocking manner, with two possible outcomes:

    * An observation is made,
    * The stream has closed, and any further attempts will give the same result.
-}
observe :: Adapter act i -> IO (Maybe act) -- TODO get rid of the maybe
observe = atomically . Streams.read . actionsFromSut

--------------------
-- transformations --
---------------------

-- | Map a function over the inputs sent to the adapter.
mapInputCommands :: (i' -> i) -> Adapter act i -> IO (Adapter act i')
mapInputCommands f adapter = do
    inputCommandsToSut' <- contramap f $ inputCommandsToSut adapter
    return $ Adapter {
        inputCommandsToSut = inputCommandsToSut',
        actionsFromSut = actionsFromSut adapter,
        close = close adapter
        }

-- | Map a function over the outputs received from the adapter.
mapActionsFromSut :: (act -> act') -> Adapter act i -> IO (Adapter act' i)
mapActionsFromSut f adapter = do
    actionsFromSut' <- Streams.map f $ actionsFromSut adapter
    return $ Adapter {
        inputCommandsToSut = inputCommandsToSut adapter,
        actionsFromSut = actionsFromSut',
        close = close adapter
        }

-- | Map function over both the inputs sent to, and the outputs received from, the adapter.
map :: (i' -> i) -> (act -> act') -> Adapter act i -> IO (Adapter act' i')
map f1 f2 adapter = do
    inputCommandsToSut' <- contramap f1 $ inputCommandsToSut adapter
    actionsFromSut' <- Streams.map f2 $ actionsFromSut adapter
    return $ Adapter {
        inputCommandsToSut = inputCommandsToSut',
        actionsFromSut = actionsFromSut',
        close = close adapter
        }

-- | Transform a raw adapter which receives ByteStrings to an adapter which receives objects, parsing the bytestrings with the given parser.
parseActionsFromSut :: Parser act -> Adapter ByteString i -> IO (Adapter act i)
parseActionsFromSut parser adapter = do
    actionStream <- parserToInputStream (Just <$> parser) (actionsFromSut adapter)
    return $ adapter { actionsFromSut = actionStream }

