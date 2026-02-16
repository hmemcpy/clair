{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.ByteString.Lazy     as BL
import           Data.Maybe               (fromMaybe)
import qualified Data.Text                as T
import qualified Data.Text.IO             as TIO
import           Options.Applicative
import           System.Exit              (exitFailure, exitSuccess)
import           System.IO                (hPutStrLn, stderr)

import           Clair.JSON
import           Clair.Parser
import           Clair.Types
import           Clair.Validation

-- | CLI options
data Options = Options
  { optInput    :: Maybe FilePath
  , optOutput   :: Maybe FilePath
  , optValidate :: Bool
  , optPretty   :: Bool
  }

-- | Command line parser
optionsParser :: Parser Options
optionsParser = Options
  <$> optional (strOption
      $ long "input"
     <> short 'i'
     <> metavar "FILE"
     <> help "Input CLAIR trace file (default: stdin)")
  <*> optional (strOption
      $ long "output"
     <> short 'o'
     <> metavar "FILE"
     <> help "Output file (default: stdout)")
  <*> switch
      ( long "validate"
     <> short 'v'
     <> help "Validate only, no output")
  <*> switch
      ( long "pretty"
     <> short 'p'
     <> help "Pretty print JSON output")

-- | Main entry point
main :: IO ()
main = do
  opts <- execParser $ info (optionsParser <**> helper)
    ( fullDesc
   <> progDesc "Parse and validate CLAIR trace files"
   <> header "clair-parser - A CLAIR trace file parser" )
  runOptions opts

runOptions :: Options -> IO ()
runOptions opts = do
  -- Read input
  input <- case optInput opts of
    Nothing    -> TIO.getContents
    Just path  -> TIO.readFile path
  
  -- Parse
  let (beliefs, parseErrors) = parseBeliefs input
  
  -- Report parse errors
  case parseErrors of
    [] -> return ()
    es -> do
      hPutStrLn stderr "Parse errors:"
      mapM_ (\(n, e) -> hPutStrLn stderr $ "  Line " ++ show n ++ ": " ++ e) es
  
  -- Validate
  case validateBeliefs beliefs of
    Invalid errs -> do
      hPutStrLn stderr "Validation errors:"
      mapM_ (hPutStrLn stderr . ("  " ++) . showError) errs
      exitFailure
    Valid -> do
      if optValidate opts
        then putStrLn "Valid CLAIR file."
        else outputResult opts beliefs

outputResult :: Options -> [Belief] -> IO ()
outputResult opts beliefs = do
  let output = if optPretty opts 
               then exportBeliefsToJSON beliefs
               else beliefsToJSON beliefs
  
  case optOutput opts of
    Nothing   -> BL.putStr output
    Just path -> BL.writeFile path output

-- | Format error messages
showError :: ValidationError -> String
showError (DuplicateId bid) = 
  "Duplicate belief ID: " ++ T.unpack (unBeliefId bid)
showError (InvalidConfidence c) = 
  "Invalid confidence value: " ++ show c ++ " (must be in [0, 1])"
showError (InvalidLevel n) = 
  "Invalid level: " ++ show n ++ " (must be >= 0)"
showError (MissingReference bid ref) = 
  "Belief " ++ T.unpack (unBeliefId bid) ++ " references unknown belief: " ++ T.unpack (unBeliefId ref)
showError (CycleDetected cycle) = 
  "Cycle detected: " ++ unwords (map (T.unpack . unBeliefId) cycle)
showError (InvalidSource src) = 
  "Invalid source: " ++ T.unpack src
