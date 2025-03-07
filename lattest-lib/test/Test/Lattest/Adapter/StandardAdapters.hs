{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Test.Lattest.Adapter.StandardAdapters (
testJSONSocketAdapterByte,
testAdapterAcceptingInput,
testJSONSocketAdapterInt,
testJSONSocketAdapterObject
)
where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Adapter.Adapter(send, Adapter(..), close, observe)
import Lattest.Adapter.StandardAdapters(connectJSONSocketAdapterAcceptingInputs,connectSocketAdapter, acceptingInputs)
import System.IO.Streams.Synchronized(fromBuffer)

import Control.Concurrent(threadDelay)
import Control.Concurrent.STM.TQueue(TQueue, newTQueueIO, writeTQueue, readTQueue)
import Control.Monad.STM(atomically)
import Data.Aeson(FromJSON,ToJSON)
import Data.ByteString(ByteString)
import qualified Data.ByteString.Char8 as C8 (pack)
import Data.Text(unpack, pack)
import Data.Text.Encoding(decodeUtf8, encodeUtf8)
import Data.Functor(void)
import GHC.Generics (Generic)
import Network.Socket(withSocketsDo, accept, SockAddr(SockAddrInet), tupleToHostAddress, setSocketOption, Socket, SocketOption(ReuseAddr,RecvTimeOut))
import qualified Network.Socket as Socket(gracefulClose)
import qualified Network.Socket.ByteString as BSock(recv, send)
import Network.Utils(listenTCPAddr)
import System.IO.Streams(write, makeOutputStream)
import System.Timeout(timeout)
import Test.HUnit hiding (Path, path)

testJSONSocketAdapterByte :: Test
testJSONSocketAdapterByte = TestCase $ withSocketsDo $ do
    -- TODO use Control.Exception.bracketOnError to do cleanup
    -- TODO fix "threadWait: invalid argument (Bad file descriptor)" message when running these tests. Maybe this has to do with the forked threads in ForkStreams.mux?
    -- test whether the socket adapter works by passing numbers around
    let addr = tupleToHostAddress (127, 0, 0, 1)
    listenSock <- listenTCPAddr (SockAddrInet 2929 addr) 10 -- the SUT listens for adapter connections
    setSocketOption listenSock ReuseAddr 1
    adap <- connectSocketAdapter :: IO (Adapter ByteString ByteString)
    (listenConn, _) <- accept listenSock -- the SUT accepts the adapter connection

    void $ send (C8.pack "1") adap -- the adapter sends 1
    void $ send (C8.pack "2") adap -- the adapter sends 2
    rest <- assertRecv "receive 1 on socket" "1" listenConn
    if null rest
        then void $ assertRecv "receive 2 on socket" "2" listenConn
        else assertEqual "also received 2 on socket" "2" rest
    void $ BSock.send listenConn $ encodeUtf8 . pack $ "3" -- the SUT sends 3 and 4. Not nicely per action, but this should still work because TCP
    threadDelay 2000 -- wait 2ms to ensure that the packets are read separately by the adapter
    void $ BSock.send listenConn $ encodeUtf8 . pack $ "4"
    threadDelay 2000
    assertObserveBytes (C8.pack "3") adap -- the adapter observes 3 from the SUT
    assertObserveBytes (C8.pack "4") adap -- the adapter observes 4 from the SUT
    
    void $ send (C8.pack "5") adap -- the adapter sends 5
    _assertRecv "receive 5" "5" listenConn
    
    void $ BSock.send listenConn $ encodeUtf8 . pack $ "6" -- the SUT sends 6
    assertObserveBytes (C8.pack "6") adap -- the adapter observes 6 from the SUT

    threadDelay 10000 -- FIXME these resolve a clash between the socket test cases. Find a more elegant solution.
    close adap
    Socket.gracefulClose listenConn 1000
    Socket.gracefulClose listenSock 1000
    threadDelay 10000 -- FIXME these resolve a clash between the socket test cases. Find a more elegant solution.

testAdapterAcceptingInput :: Test
testAdapterAcceptingInput = TestCase $ do
    icQueue <- newTQueueIO
    ics <- makeOutputStream $ atomically . writeTQueue icQueue
    actQueue <- newTQueueIO
    actionsFromSut' <- fromBuffer actQueue
    let rawAdap = Adapter { inputCommandsToSut = ics, actionsFromSut = actionsFromSut', close = error ""}
    adap <- (acceptingInputs rawAdap) :: IO (Adapter (IOAct Int Int) Int)
    
    void $ send 1 adap -- send an input
    assertObserve 1 adap -- input is observed
    assertReadTQueue 1 icQueue -- input is sent to the underlying adap
    
    void $ send 2 adap -- send an input
    assertReadTQueue 2 icQueue -- input is sent to the underlying adap
    assertObserve 2 adap -- input is observed
    
    atomically $ writeTQueue actQueue (Just 3) -- let underlying adap produce an output
    assertObserve 3 adap -- output is observed
    
    atomically $ writeTQueue actQueue (Just 4) -- let underlying adap produce an output
    assertObserve 4 adap -- output is observed

    void $ send 5 adap -- send an input
    atomically $ writeTQueue actQueue (Just 6) -- let underlying adap produce an output
    assertReadTQueue 5 icQueue -- input is sent to the underlying adap
    assertObserve 5 adap -- input is observed
    threadDelay 100000 -- wait 100ms to ensure that the adap output is received
    assertObserve 6 adap -- output is observed
    
    void $ send 7 adap -- send an input
    atomically $ writeTQueue actQueue (Just 8) -- let underlying adap produce an output
    void $ send 9 adap -- send an input
    atomically $ writeTQueue actQueue (Just 10) -- let underlying adap produce an output
    assertObserve 7 adap -- input is observed
    assertObserveNonDet 8 9 adap -- input and output are observed, in arbitrary order
    threadDelay 100000 -- wait 100ms to ensure that the adap output is received
    assertObserve 10 adap -- output is observed
    assertReadTQueue 7 icQueue -- input is sent to the underlying adap    
    assertReadTQueue 9 icQueue -- input is sent to the underlying adap    

    where
    assertReadTQueue expected queue = do
        mic <- atomically $ readTQueue queue
        case mic of
            Nothing -> assertFailure $ "Adapter closed unexpectedly while reading '" ++ show expected ++ "'"
            Just ic -> assertEqual ("receiving wrong input command on adap") expected ic

testJSONSocketAdapterInt :: Test
testJSONSocketAdapterInt = TestCase $ withSocketsDo $ do
    -- TODO use Control.Exception.bracketOnError to do cleanup
    -- TODO fix "threadWait: invalid argument (Bad file descriptor)" message when running these tests. Maybe this has to do with the forked threads in ForkStreams.mux?
    -- test whether the socket adapter works by passing numbers around
    let addr = tupleToHostAddress (127, 0, 0, 1)
    listenSock <- listenTCPAddr (SockAddrInet 2929 addr) 10 -- the SUT listens for adapter connections
    setSocketOption listenSock ReuseAddr 1
    adap <- connectJSONSocketAdapterAcceptingInputs :: IO (Adapter (IOAct Int Int) Int) -- the adapter connects, with explicit typing because it should know how to parse incoming data
    (listenConn, _) <- accept listenSock -- the SUT accepts the adapter connection

    void $ send 1 adap -- the adapter sends 1
    void $ send 2 adap -- the adapter sends 2
    _assertRecv "receive 1 and 2 on socket" "1\n2\n" listenConn
    assertObserve 1 adap -- the adapter sees that input 1 was accepted
    assertObserve 2 adap -- the adapter sees that input 2 was accepted
    
    void $ BSock.send listenConn $ encodeUtf8 . pack $ "3" -- the SUT sends 3 and 4. Not nicely per action, but this should still work because TCP
    threadDelay 2000 -- wait 2ms to ensure that the packets are read separately by the adapter
    void $ BSock.send listenConn $ encodeUtf8 . pack $ "\n4"
    threadDelay 2000
    void $ BSock.send listenConn $ encodeUtf8 . pack $ "\n"
    assertObserve 3 adap -- the adapter observes 3 from the SUT
    assertObserve 4 adap -- the adapter observes 4 from the SUT
    
    void $ send 5 adap -- the adapter sends 5
    _assertRecv "receive 5" "5\n" listenConn -- the SUT reads 5 from the adapter.
    assertObserve 5 adap -- the adapter sees that input 5 was accepted

    void $ BSock.send listenConn $ encodeUtf8 . pack $ "6\n" -- the SUT sends 6
    assertObserve 6 adap -- the adapter observes 6 from the SUT

    threadDelay 10000 -- FIXME these resolve a clash between the socket test cases. Find a more elegant solution.
    close adap
    Socket.gracefulClose listenConn 1000
    Socket.gracefulClose listenSock 1000
    threadDelay 10000 -- FIXME these resolve a clash between the socket test cases. Find a more elegant solution.

_assertRecv :: String -> String -> Socket -> IO ()
_assertRecv name s sock = void $ assertRecv name s sock

assertRecv :: String -> String -> Socket -> IO String
assertRecv assertName expected sock = do
    setSocketOption sock RecvTimeOut 100000 -- 100 milliseconds. For Windows only, because there 'timeout' doesn't work
    (recvd,rest) <- recvMax $ length expected
    assertEqual assertName expected recvd
    return rest
    where
    recvMax maxChars
        | maxChars <= 0 = return ("", "")
        | otherwise = do
            maybeRecvd <- timeout 100000 $ unpack . decodeUtf8 <$> BSock.recv sock 1024
            case maybeRecvd of
                Nothing -> assertFailure $ "Adapter closed unexpectedly while reading '" ++ show expected ++ "'"
                Just "" -> return ("", "")
                Just recvd -> do
                    if length recvd >= maxChars
                        then return $ splitAt maxChars recvd
                        else do
                            (rest,tl) <- recvMax (maxChars - length recvd)
                            return $ (recvd ++ rest,tl)

assertObserveBytes expected adap = do
    maybeObserved <- timeout 100000 $ observe adap
    case maybeObserved of
        Nothing -> assertFailure $ "Adapter observation timeout while observing '" ++ show expected ++ "'"
        Just Nothing -> assertFailure $ "Adapter closed unexpectedly while observing '" ++ show expected ++ "'"
        Just (Just observed) -> assertEqual ("receiving wrong output on adap") expected observed

assertObserve expected adap = do
    maybeObserved <- timeout 100000 $ observe adap
    case maybeObserved of
        Nothing -> assertFailure $ "Adapter observation timeout while observing '" ++ show expected ++ "'"
        Just Nothing -> assertFailure $ "Adapter closed unexpectedly while observing '" ++ show expected ++ "'"
        Just (Just observed) -> assertEqual ("receiving wrong output on adap") expected (fromIOAct observed)
    where
    fromIOAct :: IOAct a a -> a
    fromIOAct (Out a) = a
    fromIOAct (In a) = a

assertObserveNonDet expected1 expected2 adap = do
    maybeObserved <- timeout 100000 $ observe adap
    case maybeObserved of
        Nothing -> assertFailure $ "Adapter observation timeout while observing '" ++ show expected1 ++ "' / '" ++ show expected2  ++ "'"
        Just Nothing -> assertFailure $ "Adapter closed unexpectedly while observing '" ++ show expected1 ++ "' / '" ++ show expected2  ++ "'"
        Just (Just observed) ->
            if expected2 == fromIOAct observed
                then assertObserve expected1 adap
                else do
                    assertEqual ("receiving wrong output on adap") expected1 (fromIOAct observed)
                    assertObserve expected2 adap
    where
    fromIOAct :: IOAct a a -> a
    fromIOAct (Out a) = a
    fromIOAct (In a) = a

data List = Cons { element :: Double, comment :: String, tail :: List } | Nil deriving (Show, Generic, Ord, Eq)
instance FromJSON List
instance ToJSON List

testJSONSocketAdapterObject :: Test
testJSONSocketAdapterObject = TestCase $ withSocketsDo $ do
    -- test whether the socket adapter works by passing numbers around
    let addr = tupleToHostAddress (127, 0, 0, 1)
    listenSock <- listenTCPAddr (SockAddrInet 2929 addr) 10 -- the SUT listens for adapter connections
    setSocketOption listenSock ReuseAddr 1
    adap <- connectJSONSocketAdapterAcceptingInputs :: IO (Adapter (IOAct List List) List) -- the adapter connects, with explicit typing because it should know how to parse incoming data
    (listenConn, _) <- accept listenSock -- the SUT accepts the adapter connection

    let list12 = Cons 1 "first!" $ Cons 2 "second!" Nil
    void $ send list12 adap -- the adapter sends [1,2]
    list12OnSock <- unpack . decodeUtf8 <$> BSock.recv listenConn 1024 -- the SUT reads [1,2] from the adapter.
    -- note: TCP may actually split this into parts. We'll assume it doesn't. If it does, we'll need to write some more flexible reading, or read in between the two sends
    assertEqual "receive [1,2] on socket"
        "{\"comment\":\"first!\",\"element\":1,\"tag\":\"Cons\",\"tail\":{\"comment\":\"second!\",\"element\":2,\"tag\":\"Cons\",\"tail\":{\"tag\":\"Nil\"}}}\n" list12OnSock
    assertObserve list12 adap -- the adapter sees that [1,2] was accepted
    
    let list34 = Cons 3 "third!" $ Cons 4 "fourth!" Nil
    void $ BSock.send listenConn $ encodeUtf8 . pack $
        "{\"comment\":\"third!\",\"element\":3,\"tag\":\"Cons\",\"tail\":{\"comment\":\"fourth!\",\"element\":4,\"tag\":\"Cons\",\"tail\":{\"tag\":\"Nil\"}}}\n" -- the SUT sends [3,4].
    assertObserve list34 adap -- the adapter observes [3,4] from the SUT

    let list56 = Cons 5 "fifth!" $ Cons 6 "sixth!" Nil
    void $ send list56 adap -- the adapter sends [5,6]
    list56OnSock <- unpack . decodeUtf8 <$> BSock.recv listenConn 1024 -- the SUT reads [5,6] from the adapter.
    assertEqual "receive [5,6] on socket"
        "{\"comment\":\"fifth!\",\"element\":5,\"tag\":\"Cons\",\"tail\":{\"comment\":\"sixth!\",\"element\":6,\"tag\":\"Cons\",\"tail\":{\"tag\":\"Nil\"}}}\n" list56OnSock
    assertObserve list56 adap -- the adapter sees that [5,6] was accepted

    let list78 = Cons 7 "seventh!" $ Cons 8 "eighth!" Nil
    void $ BSock.send listenConn $ encodeUtf8 . pack $
        "{\"comment\":\"seventh!\",\"element\":7,\"tag\":\"Cons\",\"tail\":{\"comment\":\"eighth!\",\"element\":8,\"tag\":\"Cons\",\"tail\":{\"tag\":\"Nil\"}}}\n" -- the SUT sends [7,8].
    assertObserve list78 adap -- the adapter observes [7,8] from the SUT

    threadDelay 10000 -- FIXME these resolve a clash between the socket test cases. Find a more elegant solution.
    close adap
    Socket.gracefulClose listenConn 1000
    Socket.gracefulClose listenSock 1000
    threadDelay 10000 -- FIXME these resolve a clash between the socket test cases. Find a more elegant solution.







