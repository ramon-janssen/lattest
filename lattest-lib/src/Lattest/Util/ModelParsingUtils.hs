{-# LANGUAGE OverloadedStrings #-}

module Lattest.Util.ModelParsingUtils (readAutFile, dumpLTSdot) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Util.Utils(removeDuplicates)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath (replaceExtension)
import Data.List (isSuffixOf)

{-|
    Read an .aut file representing an LTS from the provided filepath, parse its content and return:
    - [String]: Input Alphabet
    - [String]: Output Alphabet
    - Set.Set String: Set of all LTS states
    - String: Initial state
    - Maybe [(String, IOAct String String, String)]: List of LTS transition tuples as (InitialState, Action, EndState)
    NOTE: In order to parse actions correctly, inputs and outputs must end in _i and _o respectively. The first line of the .aut file must follow the structure des (initState,nEdges,nStates).
-}
readAutFile :: FilePath -> IO ([String], [String], Set.Set String, String, Maybe [(String, IOAct String String, String)])
readAutFile path = do
    contents <- TIO.readFile path
    let linesT = T.lines contents
    case linesT of
      firstLine : restLines ->
        case parseInitialState firstLine of
          Nothing -> error "Error: Could not parse initial state from header."
          Just initialState ->
            let parsed = mapMaybe parseTupleLine restLines
                inputAlphabet  = removeDuplicates [s | (_, In s, _)  <- parsed]
                outputAlphabet = removeDuplicates [s | (_, Out s, _) <- parsed]
                allStates = Set.fromList $
                            [s1 | (s1, _, _) <- parsed] ++
                            [s2 | (_, _, s2) <- parsed]
            in return (inputAlphabet, outputAlphabet, allStates, initialState, Just parsed)

-- | Parse initial line of .aut file and return initialState. The line must follow the structure des (initState,nEdges,nStates).
parseInitialState :: T.Text -> Maybe String
parseInitialState line =
  case T.stripPrefix "des (" (T.strip line) of
    Nothing -> Nothing
    Just rest ->
      let elems = T.split (==',') (T.replace ")," "" rest)
      in case elems of
           (s:_) -> Just (T.unpack (T.strip s))
           _     -> Nothing

-- | Parse a text line of the form (state, action, state), and return the transition tuple
-- | NOTE: only action labels finished in "_i" or "_o" are considered
parseTupleLine :: T.Text -> Maybe (String, IOAct String String, String)
parseTupleLine line =
    let stripped = T.strip line -- Remove trailing whitespaces
        removedParen = (T.replace ")" "" . T.replace "(" "" . T.replace ")," "") stripped
        transition = T.split (==',') removedParen
    in case transition of
        [s1, act, s2] ->
            let actionStr = T.unpack (T.strip act)
                initState = T.unpack (T.strip s1)
                endState = T.unpack (T.strip s2)
            in if "_i" `isSuffixOf` actionStr then
                   Just (initState, In actionStr, endState)
               else if "_o" `isSuffixOf` actionStr then
                   Just (initState, Out actionStr, endState)
               else
                   Nothing -- Non-valid action
        _ -> Nothing  -- Malformed line

-- | Build a .dot file representation of LTS transitions and save it in the specified File Path
dumpLTSdot :: (Ord s, Show s, Ord i, Show i, Ord o, Show o) => FilePath -> [(s, IOAct i o, s)] -> IO ()
dumpLTSdot path transitions = do
    let edges = [ (show from, T.unpack (T.replace "!" "" . T.replace "?" "" $ T.pack (show label)), show to)
                | (from, label, to) <- transitions ]
    let dotPath = if ".dot" `isSuffixOf` path then path else path ++ ".dot"
    writeFile dotPath $
        unlines $
            ["digraph Automaton {"] ++
            [ "    " ++ from ++ " -> " ++ to ++ " [label=" ++ label ++ "];" 
            | (from, label, to) <- edges
            ] ++ ["}"]
    putStrLn $ "DOT file written to: " ++ dotPath