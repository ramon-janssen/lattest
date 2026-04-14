--- This is a modified version of:
--- TorXakis - Model Based Testing
--- See LICENSE in the parent SMT folder.
-- ----------------------------------------------------------------------------------------- --
-- uninterpreted haskell preamble

{
-----------------------------------------------------------------------------
-- Parse SMT String.
-----------------------------------------------------------------------------
module Lattest.SMT.SMTStringHappy
( smtStringParser
)
where

import Lattest.SMT.SMTStringAlex (Token(..), smtStringLexer)

import Numeric
import Data.Char
import Data.Tuple                                           
}

-- ----------------------------------------------------------------------------------------- --
--  happy preamble

%name happySmtString       StringValue
%tokentype { Token }
%error { parseError }

-- ----------------------------------------------------------------------------------------- --
-- tokens

%token
    "\""           { Tquotes            pos }
    escSequence    { TescSequence       pos  $$ }
    char           { Tchar              pos  $$ }

%% ----------------------------------------------------------------------------------------- --

-- ----------------------------------------------------------------------------------------- --
-- happy grammar for SMT string according to smtlib 2.5 standard

StringValue :: { String }
            : 
                {
                    ""
                }
            |   CharValue StringValue
                {
                    $1 ++ $2
                }

CharValue   :: { String }
            : escSequence
                {  
                    case (length $1) of
                    {   4 -> [chr (fst (head (readHex (drop 2 $1))))]
                    ;   2 -> case (tail $1) of
                        {   "\\"    -> "\\"
                        ;   "a"     -> "\a"
                        ;   "b"     -> "\b"
                        ;   "e"     -> "\x1B"
                        ;   "f"     -> "\f"
                        ;   "n"     -> "\n"
                        ;   "r"     -> "\r"
                        ;   "t"     -> "\t"
                        ;   "v"     -> "\v"
                        }
                    ;   _ -> error $ "SMTStringHappy: unexpected length (" ++ (show (length $1)) ++ ") for '"++(show $1)++"'"
                    }
                }
            | "\"" "\""
                {
                    "\""
                }
            | char
                {
                    $1
                }

-- ----------------------------------------------------------------------------------------- --
-- uninterpreted haskell postamble
{
-- ----------------------------------------------------------------------------------------- --
-- error handling

parseError :: [Token] -> a
parseError _ = error "Parse Error"

noerror = ()

-- | Smt String Parser.
smtStringParser :: [Token] -> String
smtStringParser = happySmtString
}
-- ----------------------------------------------------------------------------------------- --
-- end uninterpreted haskell postamble
