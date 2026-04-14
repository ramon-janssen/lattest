{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent SMT folder.
-}
{
-----------------------------------------------------------------------------
-- Tokenize SMT String.
-----------------------------------------------------------------------------

module Lattest.SMT.SMTStringAlex
( Token(..)                  -- exporting
, smtStringLexer             -- txsStringLexer :: String -> [Token]
)

where

}

-- ----------------------------------------------------------------------------------------- --
-- alex grammar for SMT string according to smtlib 2.5 standard

%wrapper "posn"

$escchar    = [\\abefnrtv]
$hexdig     = [0-9A-Fa-f]   

@escSequence     = \\ ($escchar | x $hexdig{2})

tokens :-                                          -- Each right-hand side has type
                                                   -- :: AlexPosn -> String -> Token

   \"                                    { tok ( \p _s -> Tquotes p ) }
   @escSequence                          { tok ( \p s -> TescSequence p s) }
   $printable                            { tok ( \p s -> Tchar p s ) }
      
-- ----------------------------------------------------------------------------------------- --

{
-- Some action helpers:
tok f p s = f p s

-- | Data structure for Smt String Tokens.
data  Token  =  Tquotes           AlexPosn
              | TescSequence      AlexPosn  String
              | Tchar             AlexPosn  String
   deriving (Eq,Show)

-- | Smt String lexer.
smtStringLexer :: String -> [Token]
smtStringLexer = alexScanTokens
}

-- ----------------------------------------------------------------------------------------- --
