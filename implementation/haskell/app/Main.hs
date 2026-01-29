{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : Main
-- Description : CLAIR REPL
--
-- Interactive read-eval-print loop for CLAIR.

module Main where

import qualified System.Console.Haskeline as H
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import CLAIR.Syntax
import CLAIR.Parser
import CLAIR.TypeChecker
import CLAIR.TypeChecker.Types (emptyContext, prettyTypeError)
import CLAIR.Evaluator
import CLAIR.Confidence (Confidence)
import CLAIR.Pretty

-- ============================================================================
-- Main
-- ============================================================================

main :: IO ()
main = H.runInputT H.defaultSettings loop

-- ============================================================================
-- REPL Loop
-- ============================================================================

loop :: H.InputT IO ()
loop = do
  minput <- H.getInputLine "clair> "
  case minput of
    Nothing -> return ()  -- EOF
    Just ":quit" -> return ()
    Just ":help" -> do
      printHelp
      loop
    Just input -> do
      case parseExpr input of
        Left err -> do
          H.outputStrLn $ "Parse error: " ++ prettyParseError err
        Right expr -> do
          -- Type check
          case infer emptyContext expr of
            Left err -> do
              H.outputStrLn $ "Type error: " ++ prettyTypeError err
            Right tcResult -> do
              H.outputStrLn $ "Type: " ++ prettyType (getType tcResult)

              -- Evaluate
              case eval expr of
                Left err -> do
                  H.outputStrLn $ "Evaluation error: " ++ prettyEvalError err
                Right val -> do
                  H.outputStrLn $ "Result: " ++ prettyValue val

                  -- Show AST if requested
                  -- H.outputStrLn $ "\nAST:\n" ++ prettyAST expr
      loop

-- ============================================================================
-- Commands
-- ============================================================================

printHelp :: H.InputT IO ()
printHelp = H.outputStrLn $ unlines
  [ "CLAIR REPL - Commands:"
  , "  :quit  Exit the REPL"
  , "  :help  Show this help message"
  , ""
  , "Examples:"
  , "  5"
  , "  λx:Nat. x"
  , "  (λx:Nat. x + 1) 5"
  , "  3 + 4"
  , "  □0.8 true"
  , "  belief(5, 0.9, none, none, none)"
  ]
