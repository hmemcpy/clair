{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : CLAIR.TypeChecker
-- Description : Bidirectional type checking for CLAIR
--
-- Bidirectional type checking distinguishes between:
--   - Checking (↓): Given e and τ, verify e : τ
--   - Synthesis (↑): Given e, compute its type τ
--
-- This approach improves error messages and handles implicit
-- arguments more naturally.

module CLAIR.TypeChecker
  ( -- * Type Checking
    infer
  , check
    -- * Result Types
  , TCResult(..)
  , getType
    -- * Utilities
  , typeOf
  , wellFormed
  ) where

import CLAIR.Syntax
import CLAIR.TypeChecker.Types
import CLAIR.Confidence (Confidence, toDouble, isNormalized)
import qualified Data.Text as T
import Control.Monad (unless)

-- ============================================================================
-- Type Checking Result
-- ============================================================================

-- | Result of type checking.
data TCResult = TCResult
  { tcType    :: Type        -- ^ Inferred or checked type
  , tcContext :: Context     -- ^ Possibly extended context
  } deriving (Eq, Show)

-- | Extract the type from a TCResult.
getType :: TCResult -> Type
getType = tcType

-- ============================================================================
-- Bidirectional Type Checking
-- ============================================================================

-- | Infer (synthesize) the type of an expression.
--
-- Γ ⊢ e ↑ τ
--
-- Uses synthesis rules to determine the type from the expression
-- structure.
infer :: Context -> Expr -> Either TypeError TCResult
infer ctx expr = case expr of
  -- Variable: Γ ⊢ x : Γ(x)
  EVar x -> case ctxLookup x ctx of
    Just ty -> return (TCResult ty ctx)
    Nothing -> Left (UnboundVar x)

  -- Application: Γ ⊢ e ↑ τ₁ → τ₂
  --            Γ ⊢ e' ↓ τ₁
  --            ────────────────
  --            Γ ⊢ e e' ↑ τ₂
  EApp e1 e2 -> do
    TCResult ty1 ctx1 <- infer ctx e1
    case ty1 of
      TFun argTy resTy -> do
        ctx2 <- check ctx1 e2 argTy
        return (TCResult resTy ctx2)
      _ -> Left (NotFunction ty1)

  -- Type annotation: Γ ⊢ e : τ
  --                ─────────
  --                Γ ⊢ e : τ ↑ τ
  EAnn e ty -> do
    ctx' <- check ctx e ty
    return (TCResult ty ctx')

  -- Literals have obvious types
  ELit (LNat _) -> return (TCResult (TBase TNat) ctx)
  ELit (LBool _) -> return (TCResult (TBase TBool) ctx)
  ELit (LString _) -> return (TCResult (TBase TString) ctx)
  ELit LUnit -> return (TCResult (TBase TUnit) ctx)

  -- Primitive operations have fixed types
  EPrim op _ _ -> inferPrimOp op

  -- Belief: Γ ⊢ e : τ
  --         c ∈ [0,1]
  --         ──────────────────
  --         Γ ⊢ belief(e,c) ↑ Belief_c[τ]
  EBelief (Belief e c _ _ _) -> do
    unless (isNormalized c) $
      Left (InvalidConfidence c)
    TCResult ty ctx' <- infer ctx e
    let beliefTy = TBelief c ty
    return (TCResult beliefTy ctx')

  -- Box (self-reference): Γ ⊢ e ↑ τ
  --                      ───────────────
  --                      Γ ⊢ □_c e ↑ Belief_c[τ]
  EBox c e -> do
    unless (isNormalized c) $
      Left (InvalidConfidence c)
    TCResult ty ctx' <- infer ctx e
    let boxTy = TBelief c ty
    return (TCResult boxTy ctx')

  -- Justification and invalidation are internal constructs
  EJustify _ -> return (TCResult TJustification ctx)
  EInvalidate _ -> return (TCResult TProvenance ctx)

  -- Lambda must be checked (cannot synthesize type without annotation)
  ELam{} -> Left (IllTyped "Cannot infer type for lambda without annotation")

-- | Check that an expression has the given type.
--
-- Γ ⊢ e ↓ τ
--
-- Uses checking rules when the type is known.
check :: Context -> Expr -> Type -> Either TypeError Context
check ctx expr ty = case expr of
  -- Lambda: Γ, x:τ₁ ⊢ e ↑ τ₂
  --         ───────────────────
  --         Γ ⊢ λx:τ₁. e ↓ τ₁ → τ₂
  ELam x argTy body -> case ty of
    TFun expectedArgTy resTy -> do
      unless (argTy == expectedArgTy) $
        Left (TypeMismatch expectedArgTy argTy)
      let ctx' = extend x argTy ctx
      TCResult inferredBodyTy ctx'' <- infer ctx' body
      unless (inferredBodyTy == resTy) $
        Left (TypeMismatch resTy inferredBodyTy)
      return ctx
    _ -> Left (NotFunction ty)

  -- For all other cases, infer and check subtyping
  _ -> do
    TCResult inferredTy ctx' <- infer ctx expr
    if subtypeOf inferredTy ty || inferredTy == ty
      then return ctx'
      else Left (TypeMismatch ty inferredTy)

-- ============================================================================
-- Primitive Operations
-- ============================================================================

-- | Infer the type of a primitive operation.
inferPrimOp :: Op -> Either TypeError TCResult
inferPrimOp = \case
  -- Arithmetic: Nat → Nat → Nat
  OAdd -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TNat))) emptyContext)
  OSub -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TNat))) emptyContext)
  OMul -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TNat))) emptyContext)
  ODiv -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TNat))) emptyContext)

  -- Comparison: τ → τ → Bool (for comparable τ)
  OEq -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TBool))) emptyContext)
  OLt -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TBool))) emptyContext)
  OGt -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TBool))) emptyContext)

  -- Logical: Bool → Bool → Bool
  OAnd -> return (TCResult (TFun (TBase TBool) (TFun (TBase TBool) (TBase TBool))) emptyContext)
  OOr -> return (TCResult (TFun (TBase TBool) (TFun (TBase TBool) (TBase TBool))) emptyContext)
  OImp -> return (TCResult (TFun (TBase TBool) (TFun (TBase TBool) (TBase TBool))) emptyContext)

  -- Confidence operations: Conf → Conf → Conf
  OPlus -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TNat))) emptyContext) -- Simplified
  OTimes -> return (TCResult (TFun (TBase TNat) (TFun (TBase TNat) (TBase TNat))) emptyContext) -- Simplified

-- ============================================================================
-- Utilities
-- ============================================================================

-- | Get the type of an expression (convenience wrapper).
typeOf :: Expr -> Either TypeError Type
typeOf = fmap getType . infer emptyContext

-- | Check well-formedness of an expression.
wellFormed :: Expr -> Either String ()
wellFormed expr = case checkWellFormed (checkWellFormedExpr expr) of
  Right () -> Right ()
  Left err -> Left err
  where
    checkWellFormedExpr :: Expr -> WellFormed
    checkWellFormedExpr = \case
      EBelief (Belief e c _ _ _) ->
        if isNormalized c
        then checkWellFormedExpr e
        else WFError $ "Invalid confidence: " ++ show (toDouble c)

      EBox c e ->
        if isNormalized c
        then checkWellFormedExpr e
        else WFError $ "Invalid confidence: " ++ show (toDouble c)

      _ -> WFOK
