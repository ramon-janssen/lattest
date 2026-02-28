{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}

-- ----------------------------------------------------------------------------------------- --
-- uninterpreted haskell preamble

{
-----------------------------------------------------------------------------
-- |
-- Module      :  SMTHappy
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (Embedded Systems Innovation by TNO)
-- Stability   :  experimental
-- Portability :  portable
--
-- Parse SMT response.
-----------------------------------------------------------------------------
module Lattest.SMT.SMTHappy
( smtParser
)
where
import Lattest.SMT.SMTAlex (Token(..), smtLexer)
import qualified Lattest.Model.Symbolic.ValExpr.ValExprDefs as C
import Data.Text (Text)
import qualified Data.Text as T
import qualified Lattest.SMT.SMTString as SMTString    -- Parse SMT string according to smtlib 2.5 standard

import qualified Data.Map    as Map
import Data.String.Utils
import Text.Regex.TDFA
}
    
-- ----------------------------------------------------------------------------------------- --
--  happy preamble

%name happySmt       ValueResponse
%tokentype { Token }
%error { parseError }

%attributetype          { MyAttributes a }
%attribute parseVal     { a }
%attribute bind         { Map.Map String C.Constant }

-- ----------------------------------------------------------------------------------------- --
-- tokens

%token
    "-"           { Tminus            pos }
    "("           { Topenpar          pos }
    ")"           { Tclosepar         pos }
    "let"         { Tlet              pos }
    name          { Tname             pos  $$ }
    bool          { Tbool             pos  $$ }
    integer       { Tinteger          pos  $$ }
    string        { Tstring           pos  $$ }


%% ----------------------------------------------------------------------------------------- --

-- ----------------------------------------------------------------------------------------- --
-- happy grammar for syntax and attributes

-- https://www.haskell.org/happy/doc/html/sec-sequences.html 
-- The only reason we used left recursion is that Happy is more efficient at parsing left-recursive rules; 

ValueResponse  -- :: { Map.Map String C.Constant }
            : "(" ValuationPairs ")"
                {
                    $2.bind = Map.empty
                ;   $$ = $2
                }

ValuationPairs -- :: { Map.Map String C.Constant }
            :  ValuationPair
                {  
                    $1.bind = $$.bind
                ;   $$ = Map.singleton (fst $1) (snd $1)
                }
            |  ValuationPairs ValuationPair
                {  
                    $1.bind = $$.bind
                ;   $2.bind = $$.bind
                ;   $$ = Map.insert (fst $2) (snd $2) $1
                }
            
ValuationPair -- :: { (String, C.Constant) }
            : "("  name RuleValue ")"
                {
                    $3.bind = Map.empty
                ;   $$ = ($2, $3)
                }
            
RuleValues  -- :: { [C.Constant] }
            : RuleValue
                {   
                    $1.bind = $$.bind
                ;   $$ = [$1]
                }
            | RuleValues RuleValue 
                {  
                    $1.bind = $$.bind
                ;   $2.bind = $$.bind
                ;   $$ = $1 ++ [ $2 ]
                }

RuleValue  -- :: { C.Constant }
              : RuleExpression
                {  
                    $1.bind = $$.bind
                ;   $$ = $1
                }
              | "(" "let" "(" VarBindings ")" RuleValue ")"
                {
                    $4.bind = $$.bind
                ;   $6.bind = Map.union (Map.fromList $4) $$.bind
                ;   $$ = $6
                }
            
VarBindings  -- :: { [( var, C.Constant)] }
             : VarBinding
                {
                    $1.bind = $$.bind
                ;   $$ = [$1]
                }
             | VarBindings VarBinding
                {
                    $1.bind = $$.bind
                ;   $2.bind = $$.bind
                ;   $$ = $1 ++ [$2]
                }

VarBinding   -- :: { ( name, C.Constant) }
             : "(" name RuleExpression ")"
                {   
                    $3.bind = $$.bind
                ;   $$ = ($2, $3)
                }
                
RuleExpression -- :: { C.Constant }
                : "(" "-" RuleExpression ")"
                  { 
                     $3.bind = $$.bind
                  ;  $$ = case $3 of
                            { C.Cint i -> C.Cint (-1*i)
                            ; _        -> error "SMT unexpected format"
                            }
                  }
                | name
                  {  
                     $$ = case Map.lookup $1 $$.bind of 
                             { Nothing  -> if ($1 =~ cstrRegex) then
                                               C.Ccstr ($1) []
                                           else
                                               error ("SMT var " ++ $1 ++ " not declared")
                             ; Just val -> val
                             }
                  }
                | bool
                  {
                    $$ = C.Cbool $1 
                  }
                | integer
                  {
                    $$ = C.Cint $1
                  }
                | string
                  {
                    $$ = C.Cstring $ T.unpack $ SMTString.stringFromSMT (T.pack (init (tail $1)))
                  }
                | "(" name RuleValues ")"
                  {
                    $3.bind = $$.bind
                  ; $$ = if ($2 =~ cstrRegex) then
                            C.Ccstr ($2) $3
                         else
                            error ("SMT: " ++ $2 ++ " is not a constructor name.")
                  }

-- ----------------------------------------------------------------------------------------- --
-- uninterpreted haskell postamble
{
-- ----------------------------------------------------------------------------------------- --
-- error handling
parseError :: [Token] -> a
parseError _ = error "Parse Error"

noerror = ()

-- | Smt Parser.
smtParser :: [Token] -> Map.Map String C.Constant
smtParser = happySmt

cstrRegex :: String
cstrRegex = "[A-Z][A-Za-z0-9_$]*"
}
-- ----------------------------------------------------------------------------------------- --
-- end uninterpreted haskell postamble
