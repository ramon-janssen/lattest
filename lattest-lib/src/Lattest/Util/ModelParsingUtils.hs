{-# LANGUAGE OverloadedStrings #-}

module Lattest.Util.ModelParsingUtils (readAutFile, readMultipleAutFiles, dumpLTSdot) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Util.Utils(removeDuplicates)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath (replaceExtension, takeBaseName, takeExtension, (</>))
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import Control.Monad (zipWithM)
import Debug.Trace (trace, traceShow)
import Lattest.Model.StandardAutomata((\/), (/\), atom, FreeLattice)
import qualified Data.Map as M
import qualified Data.IntMap as IM

newtype StateName = StateName String
    deriving (Eq, Ord, Show)
{-|
    Read an .aut file representing an LTS from the provided filepath, parse its content and return:
    - [String]: Input Alphabet
    - [String]: Output Alphabet
    - Set.Set String: Set of all LTS states
    - String: Initial state
    - Maybe [(String, IOAct String String, String)]: List of LTS transition tuples as (InitialState, Action, EndState)
    NOTE: In order to parse actions correctly, inputs and outputs must end in _i and _o respectively. The first line of the .aut file must follow the structure des (initState,nEdges,nStates).
-}
readAutFile :: FilePath -> Maybe String -> IO ([String], [String], Set.Set String, String, Maybe [(String, IOAct String String, String)])
readAutFile path mSuffix = do
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
                suffix = maybe "" id mSuffix
                renamedParsed = [ (s1 ++ suffix, t, s2 ++ suffix) | (s1, t, s2) <- parsed ]
                allStates = Set.fromList $
                            [s1 | (s1, _, _) <- renamedParsed] ++
                            [s2 | (_, _, s2) <- renamedParsed]
                initStateWSuffix = initialState ++ suffix
            in return (inputAlphabet, outputAlphabet, allStates, initStateWSuffix, Just renamedParsed)

readMultipleAutFiles
  :: FilePath
  -> IO ([String], [String], StateName, [(StateName, IOAct String String, FreeLattice StateName)])
readMultipleAutFiles dir = do
    entries <- listDirectory dir
    let files = [ dir </> f | f <- entries, takeExtension f == ".aut" ]
    let suffixes = map (("_" ++) . takeBaseName) files
    parsedResults <- zipWithM (\fp s -> readAutFile fp (Just s)) files suffixes

    case parsedResults of
      [] -> return ([], [], StateName "", [])
      _  -> do
        let transitionsRaw :: [(String, IOAct String String, String)]
            transitionsRaw =
              concatMap
                (\(_, _, _, _, mts) ->
                    case mts of
                      Just ts -> ts
                      Nothing -> [])
                parsedResults

            inputAlphabets  = [ inp | (inp, _, _, _, _) <- parsedResults ]
            outputAlphabets = [ out | (_, out, _, _, _) <- parsedResults ]
            initialsRaw     = [ ini | (_,_,_,ini,_) <- parsedResults ]

            mergedInput  = removeDuplicates (concat inputAlphabets)
            mergedOutput = removeDuplicates (concat outputAlphabets)

            allStateStrings =
                 removeDuplicates
                   ( initialsRaw
                  ++ [ s1 | (s1,_,_) <- transitionsRaw ]
                  ++ [ s2 | (_,_,s2) <- transitionsRaw ]
                   )

            transitions =
                [ ( StateName s1
                    , t
                    , atom (StateName s2)
                    )
                | (s1,t,s2) <- transitionsRaw
                ]

            atoms = [ atom (StateName s) | s <- initialsRaw ]
            initialState =
                case atoms of
                  [] -> error "No initial states found"
                  _  -> foldr1 (/\) atoms

            initTransitions = [ (StateName "Initial", In "Reset", initialState) ]
            completeTransitions = transitions ++ initTransitions

        return ( mergedInput, mergedOutput, StateName "Initial", completeTransitions )

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