{- |
    This module contains building blocks for constructing out-of-the-box 'Adapter's.

    Note that adapters do not observe inputs by default. In other words, an input command
    from a test controller does not automatically lead to an input transition in the specification
    model. Use 'acceptingInputs' to observe all sent inputs, or 'acceptingInputsWithIncompletenessAsFailures'
    to also observe failures in processing inputs in the adapter. The latter is useful if the processing
    of inputs is defined partially, in which case some inputs cannot be sent to the adapter.
-}

-- TODO also expose a generic parsing transformation which takes a parser
module Lattest.Adapter.StandardAdapters (
-- * Type Definition
Adapter, -- re-export so that a user of the library who wants to set up a testing experiment doesn't need to import the Adapter module at all
-- * Ready-to-use Adapters
-- ** Pure adapters
-- | Adapters which are defined in haskell itself.
pureMealyAdapter,
pureAdapter,
-- ** Socket Adapters
-- *** Settings
SocketSettings(..),
baseSocketSettings,
-- *** Base Socket Adapters
connectSocketAdapter,
connectSocketAdapterWith,
-- *** Socket Adapters with JSON
connectJSONSocketAdapter,
connectJSONSocketAdapterWith,
connectJSONSocketAdapterAcceptingInputs,
connectJSONSocketAdapterAcceptingInputsWith,
-- * Transformations on Adapters
-- ** Encoding and Decoding
encodeUtf8,
decodeUtf8,
endecodeUtf8,
encodeJSONTestChoices,
parseJSONActionsFromSut,
-- ** Observing Inputs
acceptingInputs,
acceptingInputsWithIncompletenessAsFailures,
-- ** Observing Quiescences
withQuiescence,
withQuiescenceMillis
)
where

import Lattest.Adapter.Adapter(Adapter(..),parseActionsFromSut,mapTestChoices,mapActionsFromSut,send,observe)
import qualified Lattest.Adapter.Adapter as Adap(map)
import Lattest.Model.Alphabet(IOAct(Out), IOSuspAct, Suspended(Quiescence), asSuspended, fromSuspended)
import Lattest.Model.Alphabet(IOAct)
import Lattest.Util.IOUtils(ifM_, ifM)
import Control.Applicative((<|>))
import Control.Monad(forever)
import Control.Monad.Extra ((||^))
import Control.Concurrent.STM.TMVar(TMVar, newEmptyTMVarIO, tryReadTMVar, writeTMVar, readTMVar, isEmptyTMVar)
import Control.Concurrent.STM.TQueue(newTQueueIO, readTQueue, writeTQueue, isEmptyTQueue)
import Control.Concurrent.Thread.Delay(delay)
import Data.Aeson(FromJSON,ToJSON)
import Data.ByteString (ByteString)
import Data.Time.Clock(UTCTime,getCurrentTime,addUTCTime,diffUTCTime,NominalDiffTime,secondsToNominalDiffTime,nominalDiffTimeToSeconds)
import GHC.Conc(forkIO, newTVarIO, TVar, retry, atomically, writeTVar, readTVar)
import Network.Socket(HostName, PortNumber)
import qualified Network.Socket as Socket(gracefulClose)
import Network.Utils (niceSocketsDo, connectTCP)
import System.IO.Streams (makeOutputStream)
import qualified System.IO.Streams as Streams (write)
import System.IO.Streams.Network(socketToStreams)
import System.IO.Streams.Synchronized(fromInputStreamBuffered,makeTInputStream,hasInput)
import qualified System.IO.Streams.Synchronized as Streams (read)

import Data.Aeson(fromJSON,toJSON,encode,Result(Error, Success),FromJSON,ToJSON)
import Data.Aeson.Parser(jsonNoDup)
import qualified Data.Attoparsec.ByteString.Char8 as Parse
import Data.Bits.Utils(c2w8)
import Data.ByteString.Lazy(toStrict,snoc)
import Data.Maybe(isJust)
import Data.Text.Encoding.Error(lenientDecode)
import qualified Data.Text.Encoding as Encoding(decodeUtf8With, encodeUtf8)
import qualified Data.Text as Text(pack, unpack)
import System.IO.Streams (makeInputStream)
import Debug.Trace(trace) -- FIXME find a better alternative

import Lattest.Model.Alphabet(TestChoice, choiceToActs, IOAct(..), IOSuspAct, Suspended(..), SuspendedIF, isOutput, fromOutput, IFAct, InputAttempt(..))
import System.IO.Streams (InputStream, OutputStream, makeInputStream, makeOutputStream, connect)
import System.IO.Streams.Synchronized(TInputStream, makeTInputStream, fromInputStreamBuffered, duplicate, tryReadIO, tryReadIO', fromBuffer, mergeBufferedWith, mapUnbuffered, fromTMVar, readAll, hasInput, Streamed)
import qualified System.IO.Streams as Streams (write, writeTo)
import GHC.Conc (forkIO, STM)
import qualified Data.Map as Map (Map, filterWithKey, null, lookup, toList)
import Control.Exception(handle,Exception,PatternMatchFail, SomeException)
import System.Random(RandomGen)
import Control.Concurrent.STM.TMVar(newEmptyTMVarIO, putTMVar)
import Lattest.Util.Utils(flipCoin, takeRandom)
import Lattest.Util.IOUtils(whileM, statefulIO, statefulIO')
import Data.List(singleton)
import System.IO.Streams.Combinators(contramap)

-- | Take an adapter that sends raw 'ByteString's, and transform it to an adapter that sends 'String's encoded in utf-8.
encodeUtf8 :: Adapter act ByteString -> IO (Adapter act String)
encodeUtf8 = mapTestChoices $ Encoding.encodeUtf8 . Text.pack

-- | Take an adapter that receives raw 'ByteString's, and transform it to an adapter that receives 'String's decoded from utf-8.
decodeUtf8 :: Adapter ByteString i -> IO (Adapter String i)
decodeUtf8 = mapActionsFromSut $ Text.unpack . Encoding.decodeUtf8With lenientDecode

-- | Take an adapter that sends and receives raw 'ByteString's, and transform it to an adapter that sends and receives 'String's, encoded in utf-8 and decoded from utf-8.
endecodeUtf8 :: Adapter ByteString ByteString -> IO (Adapter String String)
endecodeUtf8 = Adap.map (Encoding.encodeUtf8 . Text.pack) (Text.unpack . Encoding.decodeUtf8With lenientDecode)

encodeJSON :: (ToJSON i) => i -> ByteString
encodeJSON = toStrict . (flip snoc $ c2w8 '\n') . encode -- encode as strict ByteString and append a newline as separator

-- | Take an adapter that sends raw 'ByteString's, and transform it to an adapter that sends any type encoded in JSON.
encodeJSONTestChoices :: (ToJSON i) => Adapter act ByteString -> IO (Adapter act i)
encodeJSONTestChoices = mapTestChoices encodeJSON

-- | Take an adapter that receives raw 'ByteString's, and transform it to an adapter that receives any type decoded from JSON.
parseJSONActionsFromSut :: (FromJSON act) => Adapter ByteString i -> IO (Adapter act i)
parseJSONActionsFromSut adap = do
    valueAdap <- parseActionsFromSut (Parse.skipSpace *> jsonNoDup) adap
    mapActionsFromSut (fromResult . fromJSON) valueAdap
    where
    fromResult (Success s) = s
    fromResult (Error e) = Debug.Trace.trace e $ undefined e -- TODO handle error case

-- transform an adapter to transfer input commands to observed actions
--
-- architecture:
-- input--combinedInputOS---fduplicate---adapInputOS---\
--                                \                     \
--                                |                      \
--                       loopbackInputOS                 |
--                                v                      v
--                       loopbackActionOS             +------+
--                       [loopbackBuffer]             | adap |
--                       loopbackActionIS             +------+
--                                |                      |
--                                v                      |
-- <--output--combinedActionIS--fmerge <--adapActionIS---/
loopbackAdapter ::
    Adapter o ic
    -> (OutputStream i -> OutputStream ic -> IO (OutputStream ic))
    -> (TInputStream (IOAct i o) -> TInputStream (IOAct i o) -> IO (TInputStream (IOAct i o)))
    -> IO (Adapter (IOAct i o) ic)
loopbackAdapter adap fduplicate fmerge = do
    loopbackBuffer <- newEmptyTMVarIO
    
    loopbackActionOS <- makeOutputStream $ atomically . putTMVar loopbackBuffer
    loopbackInputOS <- actionToInputOS loopbackActionOS -- map type i to type IOAct i o
    let adapInputOS = inputCommandsToSut adap
    combinedInputOS <- fduplicate loopbackInputOS adapInputOS
    
    loopbackActionIS <- fromTMVar loopbackBuffer
    let adapActionIS = outputToActionIS adap -- map type o to IOAct i o
    -- loopback first: in case of a quick response to an input, the merging thread may see the input and output at the same time.
    combinedActionIS <- fmerge loopbackActionIS adapActionIS -- the merge buffer lives in here implicitly
     
    return $ Adapter {
        inputCommandsToSut = combinedInputOS,
        actionsFromSut = combinedActionIS,
        close = close adap
        }

outputToActionIS adap = mapUnbuffered Out (error "acceptingInputs buffer from SUT does not support pushback") (actionsFromSut adap)
actionToInputOS actionOS = streamSequence actionOS >>= contramap choiceToActs
-- direct pushbacks to the streams below is not needed, the merge buffer will handle pushbacks instead
streamSequence :: OutputStream a -> IO (OutputStream [a])
streamSequence s = makeOutputStream $ doMaybeSequenceCmd $ Streams.writeTo s
doMaybeSequenceCmd :: (Maybe a -> IO ()) -> Maybe [a] -> IO ()
doMaybeSequenceCmd writeMaybeAct Nothing = writeMaybeAct Nothing
doMaybeSequenceCmd writeMaybeAct (Just xs) = sequence_ $ writeMaybeAct . Just <$> xs

{- |
    Transform a given Adapter to accept all inputs. In other words, every selected input command directly becomes an observed input action.
    Every observed output from the given Adapter becomes an output action.
-}
acceptingInputs :: Adapter o i -> IO (Adapter (IOAct i o) i)
acceptingInputs adap = loopbackAdapter adap duplicate (mergeBufferedWith mergeActions)
-- merging is done by reading an input, followed by all outputs that are then available. If no input is available, then read an output instead
mergeActions :: TInputStream (IOAct i o) -> TInputStream (IOAct i o) -> STM [Maybe (IOAct i o)]
mergeActions loopbackActionIS adapActionIS = do
    hasLoopbackAction <- hasInput loopbackActionIS
    if hasLoopbackAction
        then do
            inp <- Streams.read loopbackActionIS
            outs <- readAll adapActionIS
            return (inp:outs)
        else do
            hasAdapAction <- hasInput adapActionIS
            if hasAdapAction
                then singleton <$> Streams.read adapActionIS
                else retry

{- |
    Transform a given Adapter to accept all inputs, but if the given Adapter would call an undefined case in a partial function, then interpret this
    as an observed input failure. Any input command that does not call undefined cases of partial functions directly become observed input action.
    Every observed output from the given Adapter becomes an output action.

    Input failures are useful for Adapters written in pure haskell. Instead of only writing complete functions to process input commands, where unexpected
    input commands may e.g. lead to an error output, the adapter may also just process input commands with partial functions instead, avoiding some boilerplate code.
-}
acceptingInputsWithIncompletenessAsFailures :: Adapter o i -> IO (Adapter (IFAct i o) i)
acceptingInputsWithIncompletenessAsFailures adap = do
    blockAdapActionsTVar <- newTVarIO False -- during duplication, block observation of actions from the adapter
    loopbackAdapter adap (duplicateHandlingIncompleteness blockAdapActionsTVar) (mergeBufferedWith $ mergeActionsPaused blockAdapActionsTVar)
    where
    mergeActionsPaused :: TVar Bool -> TInputStream (IOAct i o) -> TInputStream (IOAct i o) -> STM [Maybe (IOAct i o)]
    mergeActionsPaused blockAdapActionsTVar loopbackActionIS adapActionIS = do
        blockAdapActions <- readTVar blockAdapActionsTVar
        if blockAdapActions
            then singleton <$> Streams.read loopbackActionIS -- adap actions are blocked, so observe just the loopback actions
            else mergeActions loopbackActionIS adapActionIS -- adap actions are not blocked, merge actions as normal
    duplicateHandlingIncompleteness :: TVar Bool -> OutputStream (InputAttempt i) -> OutputStream i -> IO (OutputStream i)
    duplicateHandlingIncompleteness isAdapOutputBlocked loopbackInputOS adapInputOS = makeOutputStream $ \mi -> do
        case mi of
            Nothing -> Streams.write Nothing loopbackInputOS >> Streams.write Nothing adapInputOS
            Just i -> do
                atomically $ writeTVar isAdapOutputBlocked True
                inputSucceeded <- attemptInputToAdap adapInputOS i
                let mInputAction = Just $ InputAttempt(i,inputSucceeded)
                Streams.write mInputAction loopbackInputOS
                atomically $ writeTVar isAdapOutputBlocked False
    attemptInputToAdap :: OutputStream i -> i -> IO Bool
    attemptInputToAdap adapInputOS i = handle (patternMatchHandler i) (Streams.write (Just i) adapInputOS >> return True)
    patternMatchHandler :: i -> PatternMatchFail -> IO Bool
    patternMatchHandler i _ = return False


-- | adapter which, after every input, directly sends the corresponding sequence of outputs
pureMealyAdapter :: (state -> i -> state) -> (state -> i -> [act]) -> state -> IO (Adapter act i)
-- FIXME this should also implicitly observe the accepted inputs, for which it probably needs to send either (IOAct i o) or (i/o) instead of an abstract act
pureMealyAdapter transitionFunction outputFunction initialState = do
    stateVar <- newTVarIO initialState
    outputQueue <- newTQueueIO
    is <- fromBuffer outputQueue
    os <- makeOutputStream $ \mi -> do
        case mi of
            Nothing -> do
                atomically $ writeTQueue outputQueue Nothing
            Just i -> do
                os <- transduce stateVar i
                atomically $ sequence_ (writeTQueue outputQueue . Just <$> os)
    return $ Adapter {
        inputCommandsToSut = os,
        actionsFromSut = is,
        close = return ()
    }
    where
    transduce stateVar i = atomically $ do
        q <- readTVar stateVar
        writeTVar stateVar (transitionFunction q i)
        return $ outputFunction q i

{-|
    Adapter which, after every action, has the given probability of producing non-deterministically one of the corresponding (non-timeout) output transitions if any is available.
    After receiving a Nothing input, an output will be produced, which may be a timeout.
-}
pureAdapter :: (Ord i, Ord o, RandomGen g) => g -> Double -> (state -> Map.Map (IOAct i o) state) -> state -> IO (Adapter (SuspendedIF i o) (Maybe i))
pureAdapter g p transitionFunction initialState = do
    let ((g',q), outs) = randomOutputTransitions transitionFunction g initialState False -- immediately take some outputs at the start
    statefulAdapter <- (statefulIO' (processInput transitionFunction) (g', q))
    queue <- newTQueueIO
    atomically $ sequence_ (writeTQueue queue . Just <$> outs)
    inputStream <- fromBuffer queue
    outputStream <- makeOutputStream $ \mi -> do
        case mi of
            Nothing -> do
                atomically $ writeTQueue queue Nothing
            Just i -> do
                os <- statefulAdapter i
                atomically $ sequence_ (writeTQueue queue . Just <$> os)
    return $ Adapter {
        inputCommandsToSut = outputStream,
        actionsFromSut = inputStream,
        close = return ()
    }
    where 
        --processInput :: (Ord i, Ord o, RandomGen g) => (q -> Map.Map (IOAct i o) q) -> (g, q) -> Maybe i -> ((g, q), [Suspended o])
        processInput t (g, q) Nothing = randomOutputTransitions t g q True
        processInput t (g, q) (Just i) = case Map.lookup (In i) (t q) of
            Just q' -> prependInput (InputAttempt(i, True)) $ randomOutputTransitions t g q' False
            Nothing -> ((g, q), [In $ InputAttempt(i, False)])
        --randomOutputTransitions :: RandomGen g => (q -> Map.Map (IOAct i o) q) -> g -> q -> Bool -> ((g, q), [Suspended o])
        randomOutputTransitions t g q isAfterNoInput = let (g', q', outs) = randomOutputTransitions' t g q [] isAfterNoInput in ((g', q'), reverse outs)
        --randomOutputTransitions' :: RandomGen g => (q -> Map.Map (IOAct i o) q) -> g -> q -> [Suspended o] -> Bool -> (g, q, [Suspended o])
        randomOutputTransitions' t g q outs isAfterNoInput =
            let ts = Map.filterWithKey (\k _ -> isOutput k) (t q)
            in if Map.null ts -- if no outputs are available at all, 
                then if isAfterNoInput then (g, q, Out Quiescence : outs) else (g, q, outs) -- then stop producing actions (meaning a timeout or just no more actions, depending on whether a "Nothing" input was previously received)
                else let (produceOut, g') = if isAfterNoInput then (True, g) else flipCoin g p -- else decide whether to produce more actions. This is mandatory if a "Nothing" input was previously received, otherwise flip a coin
                    in if not produceOut
                        then (g', q, outs)
                        else -- pick a random output, and continue randomly picking more outputs
                            let ((o, q'), g'') = takeRandom  g' $ Map.toList ts
                            in randomOutputTransitions' t g'' q' ((Out $ OutSusp $ fromOutput o) : outs) False
        prependInput i (q, acts) = (q, In i:acts)

-- | Transform the given Adapter by introducing timeout observations. A timeout is observed after the given number of milliseconds, after any other observation.
withQuiescenceMillis :: Int -> Adapter (IOAct i o) i -> IO (Adapter (IOSuspAct i o) (Maybe i))
withQuiescenceMillis timeoutMillis = withQuiescence $ secondsToNominalDiffTime $ 0.001 * realToFrac timeoutMillis

-- | Transform the given Adapter by introducing timeout observations. A timeout is observed after the given timeout duration, after any other observation.
withQuiescence :: NominalDiffTime -> Adapter (IOAct i o) i -> IO (Adapter (IOSuspAct i o) (Maybe i))
withQuiescence timeoutDiff adap = do
    lastObservationTime <- newEmptyTMVarIO -- time of the last observed action. Nothing if observing hasn't started yet.
    isProcessingObservation <- newTVarIO False
    observedQueue <- newTQueueIO
    let ensureObservationTime = do -- start observing, if this hasn't already been done yet
            isEmpty <- atomically $ isEmptyTMVar lastObservationTime
            ifM_ isEmpty $ do
                currentTime <- getCurrentTime
                atomically $ writeTMVar lastObservationTime currentTime
        updateObservationTime = \currentTime -> do -- if the current time is past the stored observation time, then update that observation time to now
            mLastTime <- tryReadTMVar lastObservationTime
            case mLastTime of
                Nothing -> writeTMVar lastObservationTime currentTime
                Just lastTime -> ifM_ (lastTime < currentTime) $ writeTMVar lastObservationTime currentTime
        getWaitTimeMicros = \currentTime -> do -- the number of microseconds until the target timeout is reached
            lastTime <- readTMVar lastObservationTime -- blocking, in case of Nothing
            let targetTime = addUTCTime timeoutDiff lastTime
            return $ ceiling $ 1000000 * (nominalDiffTimeToSeconds $ diffUTCTime targetTime currentTime)
        waitUntilQuiescence = do -- wait until the target timeout. Blocks if there is no target timeout yet.
            currentTime <- getCurrentTime
            waitTimeMicros <- atomically $ getWaitTimeMicros currentTime
            delay waitTimeMicros
        quiescenceMonitor = forever $ do -- background task that first wait until action monitoring starts, then continuously waits until a timeout
                                         -- is reached and sets the quiescence state to true
            waitUntilQuiescence
            currentTime <- getCurrentTime
            --quiIsSet <- atomically $ do
            atomically $ do
                additionalWaitTime <- getWaitTimeMicros currentTime
                let quiescent = additionalWaitTime <= 0
                ifM_ quiescent $ do
                    writeTQueue observedQueue (Just $ Out Quiescence)
                    updateObservationTime currentTime
        actMonitor = forever $ do --background task that waits for outputs, updates the observation time and unsets the quiescence state
            mAct <- atomically $ do
                writeTVar isProcessingObservation True
                Streams.read $ actionsFromSut adap
            currentTime <- getCurrentTime
            atomically $ do
                -- observation has been made
                updateObservationTime currentTime -- update the observation time
                writeTVar isProcessingObservation False
                let timedMAct = asSuspended <$> mAct
                writeTQueue observedQueue timedMAct -- pass the action to the timeout adapter
        hasObservation = readTVar isProcessingObservation ||^ (not <$> isEmptyTQueue observedQueue) ||^ hasInput (actionsFromSut adap)
    actionsFromSut' <- makeTInputStream (readTQueue observedQueue) hasObservation
    inputCommandsToSut' <- makeOutputStream $ \mInCmd -> do
        ensureObservationTime
        case mInCmd of
            Just (Just inCmd) -> Streams.write (Just inCmd) $ inputCommandsToSut adap
            Just Nothing -> atomically $ do -- Just Nothing input means waiting, on an input or until a timeout
                hasInput <- hasObservation
                if hasInput
                    then return ()
                    else retry
            Nothing -> Streams.write Nothing $ inputCommandsToSut adap -- Nothing means closing the adapter, forward this to the underlying adapter
    forkIO quiescenceMonitor
    forkIO actMonitor
    return $ Adapter {
        inputCommandsToSut = inputCommandsToSut',
        actionsFromSut = actionsFromSut',
        close = ensureObservationTime >> close adap
        }

--------------------
-- socket adapter --
--------------------

-- | Settings for a socket Adapter.
data SocketSettings = SocketSettings {
    hostName :: HostName,
    portNumber :: PortNumber
    }

-- | Default settings for a socket Adapter.
baseSocketSettings :: SocketSettings
baseSocketSettings  = SocketSettings {
    hostName = "127.0.0.1",
    portNumber = 2929
    }

-- | Create an adapter by connecting to a server socket, with the default settings.
connectSocketAdapter :: IO (Adapter ByteString ByteString)
connectSocketAdapter = connectSocketAdapterWith baseSocketSettings

-- | Create an adapter by connecting to a server socket, with the given settings.
connectSocketAdapterWith :: SocketSettings -> IO (Adapter ByteString ByteString)
connectSocketAdapterWith settings = niceSocketsDo $ do
    socket <- connectTCP (hostName settings) (portNumber settings)
    (actionBytes, inputCommandBytes) <- socketToStreams socket
    forkedActionBytes <- fromInputStreamBuffered actionBytes
    return $ Adapter {
        inputCommandsToSut = inputCommandBytes,
        actionsFromSut = forkedActionBytes,
        close = Socket.gracefulClose socket 1000
    }

-- | Create an adapter by connecting to a server socket, with the default settings, and sending inputs and reading outputs in JSON format.
connectJSONSocketAdapter :: (ToJSON i, FromJSON o) => IO (Adapter o i)
connectJSONSocketAdapter = connectJSONSocketAdapterWith baseSocketSettings

-- | Create an adapter by connecting to a server socket, with the given settings, and sending inputs and reading outputs in JSON format.
connectJSONSocketAdapterWith :: (ToJSON i, FromJSON o) => SocketSettings -> IO (Adapter o i)
connectJSONSocketAdapterWith settings = do
    rawAdap <- connectSocketAdapterWith settings
    parsingAdap <- parseJSONActionsFromSut rawAdap
    encodeJSONTestChoices parsingAdap

-- | Create an adapter by connecting to a server socket, with the default settings, and sending inputs and reading outputs in JSON format.
connectJSONResetSocketAdapter :: (ToJSON i, FromJSON o, ToJSON reset, FromJSON resetOK) => reset -> resetOK -> IO (Adapter o i, IO ())
connectJSONResetSocketAdapter = connectJSONResetSocketAdapterWith baseSocketSettings

instance (FromJSON a, FromJSON b) => EitherNoJSONWrap a b where
    fromJSON val = leftNoJSONWrap 

 -- | Create an adapter by connecting to a server socket, with the given settings, and sending inputs and reading outputs in JSON format.
connectJSONResetSocketAdapterWith :: (ToJSON i, FromJSON o, ToJSON reset, FromJSON resetOK) => SocketSettings -> reset -> resetOK -> IO (Adapter o i, IO ())
connectJSONResetSocketAdapterWith settings resetCmd resetOKCmd = do
    rawAdap <- connectSocketAdapterWith settings
    parsingAdap <- parseJSONActionsFromSut rawAdap
    ioOrResetAdap <- encodeJSONTestChoices parsingAdap
    ioActionsFromSut <- makeTInputStream
        (do
            actOrResetOK <- Streams.read $ actionsFromSut ioOrResetAdap
            case actOrResetOK of
                Just (Left act) -> return $ Just act
                Just (Right _) -> error "resetting adapter: reset OK response received without sending a reset first!"
                Nothing -> return Nothing)
        (hasInput $ actionsFromSut ioOrResetAdap)
    ioInputCommandsToSut <- makeOutputStream $ \mi -> Streams.write (Left <$> mi) (inputCommandsToSut ioOrResetAdap)
    let ioAdap = ioOrResetAdap {
        inputCommandsToSut = ioInputCommandsToSut,
        actionsFromSut = ioActionsFromSut
    }
    _ <- dummyCoerceReset resetCmd resetOKCmd ioAdap ioOrResetAdap
    let reset = do
         send (Right resetCmd) ioOrResetAdap
         resetOK <- observe ioOrResetAdap
         return ()
         -- check Right resetOK==resetOKCmd. Or observe _until_ resetOK==resetOKCmd?
    return (ioAdap, reset)
    where
    dummyCoerceReset :: (ToJSON i, FromJSON o, ToJSON reset, FromJSON resetOK) => reset -> resetOK -> Adapter o i -> Adapter (Either o (resetOK)) (Either i reset) -> IO ()
    dummyCoerceReset resetCmd resetOKCmd ioAdap ioOrResetAdap = return ()

-- | Create an adapter by connecting to a server socket, with the default settings, and sending inputs and reading outputs in JSON format, observing any input as accepted.
connectJSONSocketAdapterAcceptingInputs :: (ToJSON i, FromJSON o) => IO (Adapter (IOAct i o) i)
connectJSONSocketAdapterAcceptingInputs = connectJSONSocketAdapter >>= acceptingInputs

-- | Create an adapter by connecting to a server socket, with the given settings, and sending inputs and reading outputs in JSON format, observing any input as accepted.
connectJSONSocketAdapterAcceptingInputsWith :: (ToJSON i, FromJSON o) => SocketSettings -> IO (Adapter (IOAct i o) i)
connectJSONSocketAdapterAcceptingInputsWith settings = connectJSONSocketAdapterWith settings >>= acceptingInputs

