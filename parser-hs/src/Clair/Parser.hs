{-# LANGUAGE OverloadedStrings #-}

module Clair.Parser
  ( -- * Parsers
    parseBelief
  , parseBeliefLine
  , parseBeliefs
  , parseBeliefsFromText
  , parseBeliefsFromFile
    -- * Individual component parsers
  , beliefIdParser
  , confidenceParser
  , levelParser
  , sourceParser
  , justificationParser
  , contentParser
  , parsedContentParser
  ) where

import           Control.Applicative (optional, (<|>))
import           Data.Attoparsec.Text
import           Data.Char           (isAlphaNum, isDigit)
import           Data.Scientific     (Scientific)
import           Data.Text           (Text)
import qualified Data.Text           as T
import qualified Data.Text.IO        as TIO

import           Clair.Types

-- | Parse a belief ID (e.g., "b1", "b2", "belief_123")
-- Format: letter followed by alphanumeric characters
beliefIdParser :: Parser BeliefId
beliefIdParser = do
  first <- satisfy (\c -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
  rest <- takeWhile (\c -> isAlphaNum c || c == '_' || c == '-')
  skipSpace
  return $ BeliefId $ T.cons first rest

-- | Parse a confidence value (scientific notation or decimal)
-- Must be in range [0, 1]
confidenceParser :: Parser Confidence
confidenceParser = do
  num <- scientific
  skipSpace
  case mkConfidence num of
    Just c  -> return c
    Nothing -> fail $ "Confidence must be in [0, 1], got: " ++ show num

-- | Parse a level (L0, L1, L2, ...)
levelParser :: Parser Level
levelParser = do
  _ <- char 'L' <|> char 'l'
  n <- decimal
  skipSpace
  return $ Level (fromIntegral n)

-- | Parse a source (@user, @self, @file:path, @model:name)
sourceParser :: Parser Source
sourceParser = do
  _ <- char '@'
  src <- takeWhile1 (\c -> isAlphaNum c || c == '_' || c == '-')
  case src of
    "user" -> skipSpace >> return SourceUser
    "self" -> skipSpace >> return SourceSelf
    _      -> do
      -- Check for file: or model: prefix
      case T.breakOn ":" src of
        ("file", rest) | not (T.null rest) -> do
          let path = T.tail rest
          skipSpace
          return $ SourceFile (T.unpack path)
        ("model", rest) | not (T.null rest) -> do
          let name = T.tail rest
          skipSpace
          return $ SourceModel name
        _ -> fail $ "Unknown source: @" ++ T.unpack src

-- | Parse a single justification reference (<id)
justificationParser :: Parser Justification
justificationParser = do
  _ <- char '<'
  bid <- beliefIdParser
  return $ Justification bid

-- | Parse a quoted string content
-- Supports escaped quotes: \"
quotedStringParser :: Parser Text
quotedStringParser = do
  _ <- char '"'
  content <- T.concat <$> many' (escapedQuote <|> plainChar)
  _ <- char '"'
  return content
  where
    escapedQuote = T.singleton <$> (char '\\' *> char '"')
    plainChar = takeWhile1 (/= '"') <|> (char '\\' >> return "\\")

-- | Parse plain content (just a quoted string)
plainContentParser :: Parser ParsedContent
plainContentParser = PlainContent <$> quotedStringParser

-- | Parse derived content with justifications (<id1 <id2 "content")
derivedContentParser :: Parser ParsedContent
derivedContentParser = do
  refs <- many1' justificationParser
  skipSpace
  content <- quotedStringParser
  return $ DerivedContent refs content

-- | Parse either plain or derived content
parsedContentParser :: Parser ParsedContent
parsedContentParser = 
  (do lookAhead (char '<'); derivedContentParser) <|> plainContentParser

-- | Parse optional justifications appearing after source and before content
optionalJustifications :: Parser [Justification]
optionalJustifications = many' $ do
  skipSpace
  ref <- justificationParser
  skipSpace
  return ref

-- | Parse a complete belief line
beliefParser :: Parser Belief
beliefParser = do
  -- Parse ID
  bid <- beliefIdParser
  
  -- Parse confidence
  conf <- confidenceParser
  
  -- Parse level
  lvl <- levelParser
  
  -- Parse source
  src <- sourceParser
  
  -- Parse optional justifications
  justs <- optionalJustifications
  
  -- Parse content
  content <- parsedContentParser
  
  -- Handle end of line
  skipSpace
  optional endOfLine
  
  return $ Belief
    { beliefId = bid
    , beliefConfidence = conf
    , beliefLevel = lvl
    , beliefSource = src
    , beliefJustifications = justs
    , beliefContent = content
    }

-- | Parse a single belief from Text (allows leading/trailing whitespace)
parseBelief :: Text -> Either String Belief
parseBelief = parseOnly (skipSpace *> beliefParser <* skipSpace <* endOfInput)

-- | Parse a single belief line (doesn't require consuming all input)
parseBeliefLine :: Text -> Either String Belief
parseBeliefLine = parseOnly (skipSpace *> beliefParser)

-- | Parse multiple beliefs from text (one per line)
-- Empty lines and comment lines (starting with #) are ignored
beliefsParser :: Parser [Belief]
beliefsParser = do
  skipSpace
  many' $ do
    -- Skip empty lines and comments
    skipMany $ do
      skipSpace
      optional (char '#' *> takeTill isEndOfLine *> endOfLine)
      skipSpace
      endOfLine
    
    -- Try to parse a belief
    mb <- optional beliefParser
    case mb of
      Just b  -> return b
      Nothing -> do
        -- If we can't parse a belief, check if we're at end
        atEnd <- atEnd
        if atEnd
          then fail "No more beliefs"
          else do
            -- Skip this line and try next
            takeTill isEndOfLine
            optional endOfLine
            skipSpace
            return undefined  -- Will be filtered out
  >>= \bs -> return $ filter (/= undefined) bs

-- | Parse multiple beliefs from Text
parseBeliefsFromText :: Text -> Either String [Belief]
parseBeliefsFromText = parseOnly (beliefsParser <* skipSpace <* endOfInput)

-- | Parse beliefs from a file
parseBeliefsFromFile :: FilePath -> IO (Either String [Belief])
parseBeliefsFromFile path = parseBeliefsFromText <$> TIO.readFile path

-- | Parse beliefs with error handling for individual lines
parseBeliefs :: Text -> ([Belief], [(Int, String)])
parseBeliefs text = 
  let lines' = zip [1..] (T.lines text)
      results = map parseLine lines'
      beliefs = [b | (_, Right b) <- results]
      errors  = [(n, e) | (n, Left e) <- results]
  in (beliefs, errors)
  where
    parseLine (n, line) 
      | T.null (T.strip line) = (n, Left "Empty line")
      | "#" `T.isPrefixOf` T.strip line = (n, Left "Comment")
      | otherwise = (n, parseBeliefLine line)
