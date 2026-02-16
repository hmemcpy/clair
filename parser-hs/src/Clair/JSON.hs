{-# LANGUAGE OverloadedStrings #-}

module Clair.JSON
  ( beliefsToJSON
  , beliefToJSON
  , beliefStoreToJSON
  , exportBeliefsToJSON
  , exportBeliefsToJSONFile
  , importBeliefsFromJSON
  , importBeliefsFromJSONFile
  ) where

import           Data.Aeson                 (encode)
import           Data.Aeson.Encode.Pretty   (Config(..), defConfig, 
                                              encodePretty', keyOrder)
import           Data.ByteString.Lazy       (ByteString)
import qualified Data.ByteString.Lazy       as BL
import qualified Data.ByteString.Lazy.Char8 as BLC8

import           Clair.Types

-- | Export a list of beliefs to JSON ByteString
beliefsToJSON :: [Belief] -> ByteString
beliefsToJSON = encode

-- | Export a single belief to JSON ByteString
beliefToJSON :: Belief -> ByteString
beliefToJSON = encode

-- | Export a belief store to JSON ByteString
beliefStoreToJSON :: BeliefStore -> ByteString
beliefStoreToJSON = encode . getAllBeliefs

-- | Export beliefs to pretty-printed JSON ByteString
exportBeliefsToJSON :: [Belief] -> ByteString
exportBeliefsToJSON = encodePretty' prettyConfig
  where
    prettyConfig = defConfig
      { confCompare = keyOrder ["id", "confidence", "level", "source", 
                                "justifications", "content", "type", "references"]
      , confIndent = Spaces 2
      }

-- | Export beliefs to a JSON file
exportBeliefsToJSONFile :: FilePath -> [Belief] -> IO ()
exportBeliefsToJSONFile path beliefs = BL.writeFile path (exportBeliefsToJSON beliefs)

-- | Import beliefs from JSON ByteString
importBeliefsFromJSON :: ByteString -> Either String [Belief]
importBeliefsFromJSON = eitherDecode

-- | Import beliefs from a JSON file
importBeliefsFromJSONFile :: FilePath -> IO (Either String [Belief])
importBeliefsFromJSONFile path = importBeliefsFromJSON <$> BL.readFile path
