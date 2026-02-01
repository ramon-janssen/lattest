{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE in the parent Symbolic folder.
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Constant
-- Copyright   :  (c) TNO and Radboud University
-- License     :  BSD3 (see the file license.txt)
-- 
-- Maintainer  :  pierre.vandelaar@tno.nl (ESI)
-- Stability   :  experimental
-- Portability :  portable
--
-- Data structure for constant definitions.
-----------------------------------------------------------------------------
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
module Lattest.Model.Symbolic.ValExpr.Constant
( 
-- * Data structure for constant definitions
  Constant (..)
)
where

import           Control.DeepSeq
import           Data.Data
import           Data.Text       (Text)
import           GHC.Generics    (Generic)

-- | Union of Boolean, Integer, String, and AlgebraicDataType constant values.
data Constant = -- | Constructor of Boolean constant.
                Cbool    { toBool :: Bool }
                -- | Constructor of Integer constant.
              | Cint     { toInteger :: Integer }
                -- | Constructor of String constant.
              | Cstring  { toText :: Text }
                -- | Constructor of Regular Expression constant.
{-
              | Cregex   { -- | Regular Expression in XSD format
                           toXSDRegex :: Text } 
                                            -- PvdL: performance gain: translate only once,
                                            --       storing SMT string as well
                -- | Constructor of constructor constant (value of ADT).
              | Ccstr    { cstrId :: CstrId, args :: [Constant] }
                -- | Constructor of ANY constant.
              | Cany     { sort :: SortId }
-}
  deriving (Eq, Ord, Read, Generic, NFData, Data)

instance Show Constant where
  show (Cbool b) = show b
  show (Cint i) = show i
  show (Cstring t) = show t

