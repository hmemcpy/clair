{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}

-- |
-- Module      : CLAIR.TypeChecker.Types
-- Description : Type checking types and utilities
--
-- Provides type context, error types, and utilities for the
-- bidirectional type checker.

module CLAIR.TypeChecker.Types
  ( -- * Type Context
    Context
  , emptyContext
  , extend
  , ctxLookup
    -- * Type Errors
  , TypeError(..)
  , prettyTypeError
    -- * Subtyping
  , subtypeOf
  , join
    -- * Well-formedness
  , WellFormed(..)
  , checkWellFormed
  ) where

import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import CLAIR.Syntax (Name(..), Type(..), BaseType(..))
import CLAIR.Confidence (Confidence)

-- ============================================================================
-- Type Context
-- ============================================================================

-- | Type context Γ maps variables to their types.
newtype Context = Context (Map.Map Name Type)
  deriving (Eq, Show)

-- | Empty context.
emptyContext :: Context
emptyContext = Context Map.empty

-- | Extend context with a binding.
extend :: Name -> Type -> Context -> Context
extend x ty (Context ctx) = Context (Map.insert x ty ctx)

-- | Look up a variable in the context.
ctxLookup :: Name -> Context -> Maybe Type
ctxLookup x (Context ctx) = Map.lookup x ctx

-- ============================================================================
-- Type Errors
-- ============================================================================

-- | Type checking errors.
data TypeError
  = -- | Variable not in scope
    UnboundVar Name
  | -- | Type mismatch (expected, actual)
    TypeMismatch Type Type
  | -- | Not a function type
    NotFunction Type
  | -- | Confidence out of range
    InvalidConfidence Confidence
  | -- | Not a belief type
    NotBelief Type
  | -- | Cyclic dependency detected
    CyclicDependency [Name]
  | -- | Ill-typed subexpression
    IllTyped String
  deriving (Eq, Show)

-- | Pretty print a type error.
prettyTypeError :: TypeError -> String
prettyTypeError = \case
  UnboundVar x -> "Unbound variable: " ++ T.unpack (getName x)
  TypeMismatch expected actual ->
    "Type mismatch: expected " ++ show expected ++ ", got " ++ show actual
  NotFunction ty ->
    "Expected function type, got " ++ show ty
  InvalidConfidence c ->
    "Invalid confidence value: " ++ show c ++ " (must be in [0,1])"
  NotBelief ty ->
    "Expected belief type, got " ++ show ty
  CyclicDependency cycle ->
    "Cyclic dependency detected: " ++ unwords (map (T.unpack . getName) cycle)
  IllTyped msg ->
    "Ill-typed expression: " ++ msg

-- ============================================================================
-- Subtyping
-- ============================================================================

-- | Subtyping relation τ₁ ≤ τ₂.
--
-- Rules:
--   - τ ≤ τ (reflexive)
--   - If τ₁ ≤ τ₂ and τ₂ ≤ τ₃, then τ₁ ≤ τ₃ (transitive)
--   - Belief_c₁[τ] ≤ Belief_c₂[τ] when c₁ ≥ c₂ (confidence weakening)
subtypeOf :: Type -> Type -> Bool
subtypeOf t1 t2 = t1 == t2 || confidenceWeakening t1 t2
  where
    -- Belief type with higher confidence is subtype of lower confidence
    confidenceWeakening (TBelief c1 tau1) (TBelief c2 tau2) =
      c1 >= c2 && tau1 == tau2
    confidenceWeakening _ _ = False

-- | Join (least upper bound) of two types.
--
-- join(τ₁, τ₂) = τ₃ where τ₁ ≤ τ₃ and τ₂ ≤ τ₃
join :: Type -> Type -> Maybe Type
join t1 t2
  | t1 == t2 = Just t1
  | subtypeOf t1 t2 = Just t2
  | subtypeOf t2 t1 = Just t1
join (TBelief c1 tau) (TBelief c2 tau')
  | tau == tau' = Just (TBelief (min c1 c2) tau)
join _ _ = Nothing

-- ============================================================================
-- Well-formedness Constraints
-- ============================================================================

-- | Well-formedness checks for CLAIR expressions.
--
-- CLAIR requires:
--   1. Justification graphs must be acyclic (DAG property)
--   2. Confidence values must be in [0,1]
--   3. Stratification: self-reference only via □_c
data WellFormed
  = -- | Well-formed
    WFOK
  | -- | Not well-formed with reason
    WFError String
  deriving (Eq, Show)

-- | Check well-formedness of a component.
checkWellFormed :: WellFormed -> Either String ()
checkWellFormed WFOK = Right ()
checkWellFormed (WFError msg) = Left msg
