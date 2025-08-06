{-# LANGUAGE OverloadedStrings #-}

module Lattest.Util.ModelParsingUtils (readAutFile) where

import Lattest.Model.Alphabet(IOAct(..))
import Lattest.Util.Utils(removeDuplicates)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath (replaceExtension)
import Data.List (isSuffixOf)

type Edge = (String, String, String)

readAutFile :: FilePath -> IO ([String], [String], Set.Set String, Maybe [(String, IOAct String String, String)])
readAutFile path = do
    contents <- TIO.readFile path
    let ls = drop 1 (T.lines contents)  -- Skip the first line (header)
        parsed = mapMaybe parseTupleLine ls

        inputAlphabet  = removeDuplicates [s | (_, In s, _)  <- parsed]
        outputAlphabet = removeDuplicates [s | (_, Out s, _) <- parsed]

        allStates = Set.fromList $
                    [s1 | (s1, _, _) <- parsed] ++
                    [s2 | (_, _, s2) <- parsed]

    return (inputAlphabet, outputAlphabet, allStates, Just parsed)

parseTupleLine :: T.Text -> Maybe (String, IOAct String String, String)
parseTupleLine line =
    let stripped = T.strip line -- Remove trailing whitespaces
        removeParenAux = T.replace "(" "" stripped 
        removeParenAux2 = T.replace ")," "" removeParenAux
        transition = T.split (==',') removeParenAux2
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

-- removeDuplicates :: Ord a => [a] -> [a]
-- removeDuplicates = go Set.empty
--   where
--     go _    []     = []
--     go seen (x:xs)
--       | x `Set.member` seen = go seen xs
--       | otherwise           = x : go (Set.insert x seen) xs

