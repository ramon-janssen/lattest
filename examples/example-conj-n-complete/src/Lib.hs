{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Lib
    ( runMultipleTests
    ) where

import Lattest.Model.Alphabet (IOAct(..))
import Lattest.Adapter.StandardAdapters (Adapter, connectJSONSocketAdapterAcceptingInputs, withQuiescenceMillis, SocketSettings(..))
import Lattest.Model.StandardAutomata
import Lattest.Exec.Testing (TestController(..), Verdict(..))
import Lattest.Exec.StandardTestControllers
import Lattest.Util.ModelParsingUtils (dumpLTSdot, readMultipleAutFiles)
import Control.Monad (forM_)
import qualified Data.Set as Set
import Lattest.Model.Automaton(reachable, determinize)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (hSetEncoding, stdout, stderr, utf8)
import Text.Read (readMaybe)
import GHC.Generics (Generic)

nrSteps = 10
delta = "delta"
initialSeed = 1000
filePath = "../specs/"

runMultipleTests :: IO ()
runMultipleTests = do

    (!inputAlphabet, !outputAlphabet, !initialState, !maybeTransitions) <- readMultipleAutFiles filePath
    case maybeTransitions of
        [] -> error "No transitions found"
        transitions -> do
            let !nonDetConcTransitions = nonDetConcTransFromMRel transitions
                !alphabet = ioAlphabet inputAlphabet outputAlphabet
                !initialConfiguration = pure initialState
                !nonDetSpec = automaton initialConfiguration alphabet nonDetConcTransitions
                !detSpec = determinize nonDetSpec
                !model = interpretConcrete detSpec
                delta = "delta"
                adap = connectJSONSocketAdapterAcceptingInputs

            let states = Set.toList (reachable detSpec)
                seeds = [initialSeed + n | n <- [1..(length states)]]
             
            results <- runNCompleteTestSuite adap detSpec nrSteps delta (zip states seeds)
        
            forM_ results $ \(state, verdict, (observed, maybeMq)) -> do
                putStrLn $ "state: " ++ show state
                putStrLn $ "verdict: " ++ show verdict
                putStrLn $ "observed: " ++ show observed

