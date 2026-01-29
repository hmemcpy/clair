{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : CLAIR.Pretty
-- Description : Pretty printing for CLAIR AST and values

module CLAIR.Pretty
  ( -- * Expressions
    prettyExpr
  , prettyType
    -- * Values
  , prettyValue
    -- * Confidence
  , prettyConfidence
    -- * AST
  , prettyAST
  ) where

import CLAIR.Syntax
import CLAIR.Confidence (Confidence(..), Defeat(..), toDouble)
import CLAIR.Evaluator (Value(..), BeliefValue(..))
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

-- ============================================================================
-- Expressions
-- ============================================================================

-- | Pretty print an expression.
prettyExpr :: Expr -> String
prettyExpr = \case
  EVar x -> T.unpack (getName x)
  ELam x ty body ->
    "λ" ++ T.unpack (getName x) ++ ": " ++ prettyType ty ++ ". " ++ prettyExpr body
  EApp e1 e2 ->
    case (e1, e2) of
      (EApp{}, _) -> "(" ++ prettyExpr e1 ++ ") " ++ prettyAtom e2
      (_, _) -> prettyExpr e1 ++ " " ++ prettyAtom e2
  EAnn e ty ->
    "(" ++ prettyExpr e ++ " : " ++ prettyType ty ++ ")"
  EBelief b -> prettyBelief b
  EJustify _ -> "justify(...)"
  EInvalidate _ -> "invalidate(...)"
  EBox c e ->
    "□_" ++ show (fromIntegral (round (toDouble c * 100)) / 100 :: Double) ++ " " ++ prettyAtom e
  EPrim op e1 e2 ->
    "(" ++ prettyExpr e1 ++ " " ++ prettyOp op ++ " " ++ prettyExpr e2 ++ ")"
  ELit lit -> prettyLiteral lit

-- | Pretty print an atomic expression.
prettyAtom :: Expr -> String
prettyAtom e = case e of
  EVar{} -> prettyExpr e
  ELit{} -> prettyExpr e
  EBox{} -> prettyExpr e
  EBelief{} -> prettyExpr e
  _ -> "(" ++ prettyExpr e ++ ")"

-- | Pretty print a type.
prettyType :: Type -> String
prettyType = \case
  TBase TNat -> "Nat"
  TBase TBool -> "Bool"
  TBase TString -> "String"
  TBase TUnit -> "Unit"
  TFun t1 t2 -> prettyType t1 ++ " → " ++ prettyType t2
  TBelief c t -> "Belief_" ++ show (fromIntegral (round (toDouble c * 100)) / 100 :: Double) ++ "[" ++ prettyType t ++ "]"
  TJustification -> "Justification"
  TProvenance -> "Provenance"

-- | Pretty print a literal.
prettyLiteral :: Literal -> String
prettyLiteral = \case
  LNat n -> show n
  LBool b -> if b then "true" else "false"
  LString s -> "\"" ++ T.unpack s ++ "\""
  LUnit -> "()"

-- | Pretty print an operator.
prettyOp :: Op -> String
prettyOp = \case
  OAdd -> "+"
  OSub -> "-"
  OMul -> "*"
  ODiv -> "/"
  OEq -> "="
  OLt -> "<"
  OGt -> ">"
  OAnd -> "∧"
  OOr -> "∨"
  OImp -> "→"
  OPlus -> "⊕"
  OTimes -> "⊗"

-- ============================================================================
-- Beliefs
-- ============================================================================

-- | Pretty print a belief.
prettyBelief :: Belief -> String
prettyBelief (Belief e c j i p) =
  "belief(" ++ prettyExpr e ++ ", " ++ prettyConfidence c ++ ", " ++
  prettyJustification j ++ ", " ++ prettyInvalidation i ++ ", " ++
  prettyProvenance p ++ ")"

-- | Pretty print confidence.
prettyConfidence :: Confidence -> String
prettyConfidence (Confidence c) = show (fromIntegral (round (c * 1000)) / 1000 :: Double)

-- | Pretty print justification.
prettyJustification :: Justification -> String
prettyJustification = \case
  JNone -> "none"
  JSingle e -> "[" ++ prettyExpr e ++ "]"
  JAggregate es -> "[" ++ unwords (map prettyExpr es) ++ "]"

-- | Pretty print invalidation.
prettyInvalidation :: Invalidation -> String
prettyInvalidation = \case
  INone -> "none"
  IUndercut (Defeat d) -> "undercut(" ++ show (fromIntegral (round (d * 100)) / 100 :: Double) ++ ")"
  IRebut (Defeat d) e -> "rebut(" ++ show (fromIntegral (round (d * 100)) / 100 :: Double) ++ ", " ++ prettyExpr e ++ ")"
  ICombined is -> "combined(" ++ unwords (map prettyInvalidation is) ++ ")"

-- | Pretty print provenance.
prettyProvenance :: Provenance -> String
prettyProvenance = \case
  PNone -> "none"
  PModel s -> "model(" ++ T.unpack s ++ ")"
  PHuman -> "human"
  PDerived es -> "derived(" ++ unwords (map prettyExpr es) ++ ")"
  PExternal s -> "external(" ++ T.unpack s ++ ")"

-- ============================================================================
-- Values
-- ============================================================================

-- | Pretty print a runtime value.
prettyValue :: Value -> String
prettyValue = \case
  VClosure x _ _ -> "<closure " ++ T.unpack (getName x) ++ ">"
  VNat n -> show n
  VBool b -> if b then "true" else "false"
  VString s -> "\"" ++ T.unpack s ++ "\""
  VUnit -> "()"
  VBelief bv -> prettyBeliefValue bv

-- | Pretty print a belief value.
prettyBeliefValue :: BeliefValue -> String
prettyBeliefValue (BeliefValue v c j inv) =
  "Belief(" ++ prettyValue v ++ ", " ++ prettyConfidence c ++ ")" ++
  (if null j then "" else " justified by [" ++ unwords (map prettyValue j) ++ "]") ++
  (if inv then " [defeated]" else "")

-- ============================================================================
-- AST (debugging)
-- ============================================================================

-- | Pretty print AST structure (for debugging).
prettyAST :: Expr -> String
prettyAST = go 0
  where
    go indent expr = replicate (indent * 2) ' ' ++ case expr of
      EVar x -> "Var " ++ T.unpack (getName x)
      ELam x ty body ->
        "Lam " ++ T.unpack (getName x) ++ ": " ++ prettyType ty ++ "\n" ++
        go (indent + 1) body
      EApp e1 e2 ->
        "App\n" ++
        go (indent + 1) e1 ++ "\n" ++
        go (indent + 1) e2
      EAnn e ty ->
        "Ann : " ++ prettyType ty ++ "\n" ++
        go (indent + 1) e
      EBelief b ->
        "Belief conf=" ++ prettyConfidence (beliefConf b)
      EBox c e ->
        "Box " ++ prettyConfidence c ++ "\n" ++
        go (indent + 1) e
      EPrim op e1 e2 ->
        "Prim " ++ prettyOp op ++ "\n" ++
        go (indent + 1) e1 ++ "\n" ++
        go (indent + 1) e2
      ELit lit ->
        "Lit " ++ prettyLiteral lit
      EJustify _ -> "Justify ..."
      EInvalidate _ -> "Invalidate ..."
