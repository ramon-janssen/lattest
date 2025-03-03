{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE OverloadedStrings  #-}

module System.IO.Streams.Synchronized.Attoparsec (
parseFromStream,
parserToInputStream
)
where

import           Control.Exception(Exception)
import           Control.Monad(unless, void)
import           Control.Monad.Extra((||^), (&&^))
import qualified Data.Attoparsec.ByteString as C8(parse,feed)
import qualified Data.Attoparsec.ByteString as C8(Parser)
import           Data.Attoparsec.Types(Parser,IResult(..))
import           Data.ByteString(ByteString)
import qualified Data.ByteString as C8(null)
import           Data.List(intercalate)
import           Data.String(IsString)
import           Data.Typeable(Typeable)
import           Data.IORef(IORef,newIORef,writeIORef,readIORef)
import           System.IO.Streams.Synchronized (TInputStream,makeTInputStream,hasInput)
import qualified System.IO.Streams as Streams (makeInputStream)
import qualified System.IO.Streams.Synchronized as Streams (read, unRead)
import Control.Concurrent.STM.TVar(TVar, newTVarIO, writeTVar, readTVar)
import Control.Concurrent.STM(STM)
import System.IO.Streams.Synchronized(TInputStream, makeTInputStream)
import Control.Concurrent.STM(throwSTM,catchSTM)

parseFromStream :: TVar (Bool, IResult ByteString (Maybe r)) -> Parser ByteString (Maybe r) -> TInputStream ByteString -> STM (Maybe r)
parseFromStream stateVar parser is = do
    parseFromStream' stateVar True is
    (closed, state) <- readTVar stateVar
    writeTVar stateVar (closed, C8.parse parser "")
    if closed
        then return Nothing
        else case state of
            (Done "" r) -> return r
            other ->
                let (residual,ctx,message) = errorContext other
                in throwSTM $ ParseException (toMsg ctx ++ message ++ ", residual [" ++ show residual ++ "]")
    where
    toMsg [] = ""
    toMsg xs = "[parsing " ++ intercalate "/" xs ++ "] "

parseFromStream' :: TVar (Bool, IResult ByteString (Maybe r)) -> Bool -> TInputStream ByteString -> STM ()
parseFromStream' stateVar blockUntilFinished is = do
    (closed, r) <- readTVar stateVar
    if closed
        then return ()
        else doParse r >>= writeTVar stateVar
    where
    doParse :: IResult ByteString (Maybe r) -> STM (Bool, IResult ByteString (Maybe r))
    doParse r = do
        stop <- return (isFinished r) ||^ (return (not blockUntilFinished) &&^ (not <$> hasInput is))
        if stop
            then do
                r' <- unread' r
                return (False, r')
            else  do
                m <- Streams.read is
                case m of
                    Nothing -> do
                        r' <- unread' r
                        return (True, r')
                    Just s -> if C8.null s
                        then doParse r
                        else doParse $! C8.feed r s
    unread rest = unless (C8.null rest) $ Streams.unRead rest is
    
    unread' (Fail rest ctx e) = unread rest >> return (Fail "" ctx e)
    unread' (Done rest result) = unread rest >> return (Done "" result)
    unread' partial = return partial

errorContext (Fail residual ctx msg) = (residual, ctx, msg)
errorContext (Partial _) = ("", [], "")

isFinished :: (IResult a b) -> Bool
isFinished (Partial _) = False
isFinished _ = True

data ParseException = ParseException String

instance Exception ParseException
instance Show ParseException where
    show (ParseException message) = "Parse error: " ++ message

-- Convert a stream of bytes to a stream of actions parsed from those bytes, using the provided parser. The stream ends if either the parser yields
-- a Nothing or if the underlying stream yields a Nothing
-- If the parser yields a Nothing, then all bytes up to that Nothing are consumed from the underlying stream, but if the underyling stream yields a
-- Nothing, then all bytes since the last Just result are unread.
parserToInputStream :: C8.Parser (Maybe r)
                    -> TInputStream ByteString
                    -> IO (TInputStream r)
parserToInputStream parser is = do
    stateVar <- newTVarIO (False, C8.parse parser "")
    makeTInputStream (parseFromStream stateVar parser is) (parserHasInput stateVar)
    where
    parserHasInput stateVar = do
        parseFromStream' stateVar False is
        (closed, state) <- readTVar stateVar
        return $ closed || isFinished state



