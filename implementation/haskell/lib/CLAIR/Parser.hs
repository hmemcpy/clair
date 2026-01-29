{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : CLAIR.Parser
-- Description : Parse CLAIR surface syntax
--
-- Parses CLAIR source text into abstract syntax.
--
-- Example syntax:
--
-- @
-- let x = belief("rain", 0.8, [], none, none)
-- let y = belief("clouds", 0.7, [x], none, none)
-- belief("wet", x.conf ⊕ y.conf, [x, y], none, none)
-- @

module CLAIR.Parser
  ( -- * Parsing
    parseExpr
  , parseProgram
  , parseFile
    -- * Error Handling
  , CLAIRParseError(..)
  , prettyParseError
    -- * Lexer
  , lexCLAIR
  , Token(..)
  ) where

import CLAIR.Syntax
import CLAIR.Confidence (Confidence(..), Defeat(..), toDouble)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Text.Parsec
import Text.Parsec.Text (Parser)
import Control.Monad (void)

-- ============================================================================
-- Tokens
-- ============================================================================

-- | Lexical tokens for CLAIR.
data Token
  = -- | Identifiers: x, foo_bar
    TIdent String
  | -- | Keywords: let, in, belief, justify, invalidate, none
    TLet | TIn | TKBelief | TJustify | TInvalidate | TNone
  | -- | Operators
    TLambda | TArrow | TDot
  | TOPlus | TOTimes | TOUndercut | TORebut
  | TBox | TPlus | TMinus | TMul | TDiv
  | TEq | TLt | TGt
  | TAnd | TOr | TImp
  | -- | Literals
    TInt Integer
  | TFloat Double
  | TKBool Bool
  | TKString String
  | -- | Delimiters
    TLParen | TRParen
  | TLBracket | TRBracket
  | TBrace | TBraceClose
  | TComma | TColon | TSemicolon
  | -- | End of file
    TEOF
  deriving (Eq, Show)

-- ============================================================================
-- Parse Errors
-- ============================================================================

-- | Parse error with location information.
data CLAIRParseError = CLAIRParseError
  { errPos     :: SourcePos
  , errMessage :: String
  } deriving (Eq, Show)

-- | Pretty print a parse error.
prettyParseError :: CLAIRParseError -> String
prettyParseError CLAIRParseError{..} =
  "Parse error at " ++ show errPos ++ ": " ++ errMessage

-- ============================================================================
-- Lexer
-- ============================================================================

-- | Lexer for CLAIR source code.
lexer :: Parser Token
lexer = choice
  [ reserved "let" *> return TLet
  , reserved "in" *> return TIn
  , reserved "belief" *> return TKBelief
  , reserved "justify" *> return TJustify
  , reserved "invalidate" *> return TInvalidate
  , reserved "none" *> return TNone
  , reservedOp "⊕" *> return TOPlus
  , reservedOp "⊗" *> return TOTimes
  , reservedOp "⊙" *> return TOUndercut
  , reservedOp "⊘" *> return TORebut
  , reservedOp "□" *> return TBox
  , reservedOp "→" *> return TArrow
  , reservedOp "λ" *> return TLambda
  , reservedOp "." *> return TDot
  , reservedOp "+" *> return TPlus
  , reservedOp "-" *> return TMinus
  , reservedOp "*" *> return TMul
  , reservedOp "/" *> return TDiv
  , reservedOp "=" *> return TEq
  , reservedOp "<" *> return TLt
  , reservedOp ">" *> return TGt
  , reservedOp "∧" *> return TAnd
  , reservedOp "∨" *> return TOr
  , reservedOp "→" *> return TImp
  , floatLiteral
  , intLiteral
  , stringLiteral
  , boolLiteral
  , identifier
  , charLiteral >>= \c -> case c of
      '(' -> return TLParen
      ')' -> return TRParen
      '[' -> return TLBracket
      ']' -> return TRBracket
      '{' -> return TBrace
      '}' -> return TBraceClose
      ',' -> return TComma
      ':' -> return TColon
      ';' -> return TSemicolon
      _ -> fail $ "Unexpected character: " ++ [c]
  ] <* whitespace
  where
    reserved s = try $ string s <* notFollowedBy alphaNum

    reservedOp s = try $ string s <* notFollowedBy (oneOf "+-*/=<>.")

    identifier = do
      start <- letter <|> char '_'
      rest <- many (alphaNum <|> oneOf "_'")
      return (TIdent (start : rest))

    intLiteral = do
      digits <- many1 digit
      return (TInt (read digits))

    floatLiteral = do
      digits <- many1 digit
      _ <- char '.'
      decimals <- many1 digit
      return (TFloat (read (digits ++ "." ++ decimals)))

    stringLiteral = between (char '"') (char '"') $ do
      content <- many (noneOf "\"")
      return (TKString content)

    boolLiteral = choice
      [ string "true" *> return (TKBool True)
      , string "false" *> return (TKBool False)
      ]

    charLiteral = anyChar

    whitespace = many (space <|> (comment *> return ' '))

    comment = try $ string "--" *> manyTill anyChar newline

-- | Lex a string into tokens.
lexCLAIR :: String -> Either CLAIRParseError [Token]
lexCLAIR input = case parse (many lexer) "(input)" (T.pack input) of
  Left err -> Left (CLAIRParseError (errorPos err) (show err))
  Right toks -> Right toks

-- ============================================================================
-- Expression Parser
-- ============================================================================

-- | Parse a CLAIR expression.
parseExpr :: String -> Either CLAIRParseError Expr
parseExpr input = case parse expr "(input)" (T.pack input) of
  Left err -> Left (CLAIRParseError (errorPos err) (show err))
  Right e -> Right e

-- | Parse a program (sequence of expressions).
parseProgram :: String -> Either CLAIRParseError [Expr]
parseProgram input = case parse (many expr <* eof) "(input)" (T.pack input) of
  Left err -> Left (CLAIRParseError (errorPos err) (show err))
  Right es -> Right es

-- | Parse a CLAIR source file.
parseFile :: FilePath -> IO (Either CLAIRParseError [Expr])
parseFile path = do
  content <- TIO.readFile path
  return $ parseProgram (T.unpack content)

-- ============================================================================
-- Expression Grammar
-- ============================================================================

-- | expr ::= lambda | let | app
expr :: Parser Expr
expr = lambda <|> letExpr <|> parseApp

-- | lambda ::= "λ" x ":" type "." expr
lambda :: Parser Expr
lambda = do
  _ <- (char 'λ' *> return ()) <|> (string "lambda" *> return ())
  spaces
  x <- identifier
  _ <- char ':'
  ty <- typeParser
  _ <- char '.'
  body <- expr
  return (ELam (name x) ty body)
  where
    identifier :: Parser String
    identifier = do
      start <- letter <|> char '_'
      rest <- many (alphaNum <|> oneOf "_'")
      return (start : rest)

-- | let ::= "let" x "=" expr "in" expr
letExpr :: Parser Expr
letExpr = do
  _ <- reserved "let"
  x <- identifier
  _ <- char '='
  e1 <- expr
  _ <- reserved "in"
  e2 <- expr
  return (EApp (ELam (name x) (TBase TNat) e2) e1) -- Desugar to application
  where
    reserved s = try $ string s <* spaces
    identifier = do
      start <- letter <|> char '_'
      rest <- many (alphaNum <|> oneOf "_'")
      spaces
      return (start : rest)

-- | app ::= atom (atom | ":" type)*
parseApp :: Parser Expr
parseApp = do
  head <- atom
  apps <- many (try (atom >>= \a -> return (Left a)) <|>
                try (char ':' *> typeParser >>= \t -> return (Right t)))
  return $ foldl (\e (ea) -> case ea of
    Left arg -> EApp e arg
    Right ty -> EAnn e ty
    ) head apps

-- | atom ::= variable | literal | belief | box | "(" expr ")"
atom :: Parser Expr
atom = choice
  [ varExpr
  , literalExpr
  , beliefExpr
  , boxExpr
  , between (char '(') (char ')') expr
  , between (char '[') (char ']') expr
  ]
  where
    varExpr = do
      x <- identifier
      return (EVar (name x))

    identifier = do
      start <- letter <|> char '_'
      rest <- many (alphaNum <|> oneOf "_'")
      return (start : rest)

-- | belief ::= "belief" "(" expr "," float "," "," justify "," invalidate "," provenance ")"
beliefExpr :: Parser Expr
beliefExpr = do
  _ <- reserved "belief"
  _ <- char '('
  e <- expr
  _ <- char ','
  c <- floatLit
  _ <- char ','
  j <- justParser
  _ <- char ','
  i <- invParser
  _ <- char ','
  p <- provParser
  _ <- char ')'
  return (EBelief (Belief e c j i p))
  where
    reserved s = try $ string s <* spaces
    floatLit = do
      digits <- many1 digit
      _ <- char '.'
      decimals <- many1 digit
      spaces
      return (Confidence (read (digits ++ "." ++ decimals)))

    justParser = choice
      [ reserved "none" *> return JNone
      , between (char '[') (char ']') (do
          es <- sepBy expr (char ',')
          case es of
            [] -> return JNone
            [e] -> return (JSingle e)
            _ -> return (JAggregate es))
      ]

    invParser = choice
      [ reserved "none" *> return INone
      , do
          _ <- reserved "undercut"
          _ <- char '('
          d <- floatLit
          _ <- char ')'
          return (IUndercut (Defeat (toDouble d)))
      , do
          _ <- reserved "rebut"
          _ <- char '('
          d <- floatLit
          _ <- char ','
          e <- expr
          _ <- char ')'
          return (IRebut (Defeat (toDouble d)) e)
      ]

    provParser = choice
      [ reserved "none" *> return PNone
      , reserved "human" *> return PHuman
      , do
          _ <- reserved "model"
          _ <- char '('
          s <- stringLit
          _ <- char ')'
          return (PModel (T.pack s))
      ]
      where
        stringLit = between (char '"') (char '"') (many (noneOf "\""))

-- | box ::= "□" float expr
boxExpr :: Parser Expr
boxExpr = do
  _ <- (char '□' *> return ()) <|> (string "box" *> return ())
  spaces
  c <- floatLit
  e <- atom
  return (EBox c e)
  where
    floatLit = do
      digits <- many1 digit
      _ <- char '.'
      decimals <- many1 digit
      spaces
      return (Confidence (read (digits ++ "." ++ decimals)))

-- | literal ::= int | bool | string
literalExpr :: Parser Expr
literalExpr = choice
  [ intLit
  , boolLit
  , stringLit
  , unitLit
  ]
  where
    intLit = do
      n <- many1 digit
      return (ELit (LNat (read n)))

    boolLit = choice
      [ string "true" *> return (ELit (LBool True))
      , string "false" *> return (ELit (LBool False))
      ]

    stringLit = between (char '"') (char '"') $ do
      s <- many (noneOf "\"")
      return (ELit (LString (T.pack s)))

    unitLit = string "()" *> return (ELit LUnit)

-- ============================================================================
-- Type Parser
-- ============================================================================

-- | type ::= base | type "→" type | "Belief" "[" type "]"
typeParser :: Parser Type
typeParser = choice
  [ beliefType
  , try funType
  , baseType
  ]
  where
    beliefType = do
      _ <- string "Belief"
      _ <- char '['
      ty <- baseType
      _ <- char ']'
      return (TBelief (Confidence 0.5) ty) -- Default confidence

    funType = do
      arg <- baseType
      _ <- string "→" <|> string "->"
      res <- typeParser
      return (TFun arg res)

    baseType = choice
      [ string "Nat" *> return (TBase TNat)
      , string "Bool" *> return (TBase TBool)
      , string "String" *> return (TBase TString)
      , string "Unit" *> return (TBase TUnit)
      ]
