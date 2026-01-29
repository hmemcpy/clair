{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : CLAIR.Syntax
-- Description : Abstract syntax for CLAIR expressions
--
-- CLAIR is a simply-typed lambda calculus extended with:
--   - Confidence-annotated beliefs
--   - Justification graphs with provenance
--   - Defeat operators (undercut, rebut)
--   - Stratified self-reference via □_c

module CLAIR.Syntax
  ( -- * Names
    Name(..)
  , getName
  , name
    -- * Types
  , Type(..)
  , BaseType(..)
    -- * Expressions
  , Expr(..)
    -- * Literals
  , Literal(..)
    -- * Operators
  , Op(..)
    -- * Belief Operations
  , Belief(..)
  , Justification(..)
  , Invalidation(..)
  , Provenance(..)
    -- * Helper Constructors
  , belief
  , var
  , app
  , lam
  , ann
  , mkOp
  ) where

import qualified Data.Text as T
import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)
import CLAIR.Confidence (Confidence, Defeat)

-- ============================================================================
-- Names
-- ============================================================================

-- | A variable or identifier name.
-- Internally represented as Text for efficient hashing.
newtype Name = Name { getName :: T.Text }
  deriving (Eq, Ord, Show, Generic, ToJSON, FromJSON)

-- | Create a Name from a String.
name :: String -> Name
name = Name . T.pack

-- ============================================================================
-- Types
-- ============================================================================

-- | CLAIR types.
data Type
  = -- | Base type
    TBase BaseType
  | -- | Function type A → B
    TFun Type Type
  | -- | Belief type at confidence c: Belief_c[A]
    TBelief Confidence Type
  | -- | Justification graph type
    TJustification
  | -- | Provenance tracking type
    TProvenance
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Base types in CLAIR.
data BaseType
  = -- | Natural numbers
    TNat
  | -- | Booleans
    TBool
  | -- | Strings
    TString
  | -- | Unit type
    TUnit
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- ============================================================================
-- Expressions
-- ============================================================================

-- | The core expression language for CLAIR.
--
-- This is a simply-typed lambda calculus with belief constructors
-- and stratified self-reference.
data Expr
  = -- | Variable: x
    EVar Name
  | -- | Lambda abstraction: λx:A. e
    ELam Name Type Expr
  | -- | Application: e1 e2
    EApp Expr Expr
  | -- | Type annotation: e : A
    EAnn Expr Type
  | -- | Belief: belief(v, c, j, i, p)
    EBelief Belief
  | -- | Justification reference: justify(j)
    EJustify Justification
  | -- | Invalidation reference: invalidate(i)
    EInvalidate Invalidation
  | -- | Self-reference: □_c e (necessity at confidence c)
    EBox Confidence Expr
  | -- | Primitive operations
    EPrim Op Expr Expr
  | -- | Literals
    ELit Literal
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Binary primitive operations.
data Op
  = -- | Arithmetic: +, -, *, /
    OAdd | OSub | OMul | ODiv
  | -- | Comparison: =, <, >
    OEq | OLt | OGt
  | -- | Logical: ∧, ∨, →
    OAnd | OOr | OImp
  | -- | Confidence operations: ⊕, ⊗
    OPlus | OTimes
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Literal values.
data Literal
  = -- | Natural number
    LNat Integer
  | -- | Boolean
    LBool Bool
  | -- | String
    LString T.Text
  | -- | Unit
    LUnit
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- ============================================================================
-- Belief Operations
-- ============================================================================

-- | A belief value with all its annotations.
--
-- belief(v, c, j, i, p) represents:
--   - v: the proposition or value being believed
--   - c: confidence level in [0,1]
--   - j: justification graph (supports)
--   - i: invalidation information (defeats)
--   - p: provenance tracking
data Belief = Belief
  { beliefValue     :: Expr           -- ^ The proposition/content
  , beliefConf      :: Confidence     -- ^ Confidence level
  , beliefJustify   :: Justification  -- ^ Supporting arguments
  , beliefInvalidate :: Invalidation  -- ^ Defeating information
  , beliefProvenance :: Provenance    -- ^ Source tracking
  } deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Justification graph.
--
-- A justification is a set of supporting arguments with their
-- associated confidences. This forms a DAG when well-formed.
data Justification
  = -- | No supporting arguments (axiom/foundation)
    JNone
  | -- | Single supporting argument
    JSingle Expr
  | -- | Multiple supporting arguments (aggregated)
    JAggregate [Expr]
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Invalidation (defeat) information.
--
-- Tracks undercut and rebut defeats that affect the belief.
data Invalidation
  = -- | No invalidation
    INone
  | -- | Undercut defeat (attacks connection)
    IUndercut Defeat
  | -- | Rebut defeat (opposes conclusion)
    IRebut Defeat Expr
  | -- | Combined defeats
    ICombined [Invalidation]
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Provenance tracking.
--
-- Tracks the source of a belief for auditing and explanation.
data Provenance
  = -- | No provenance info
    PNone
  | -- | LLM-generated with model info
    PModel T.Text
  | -- | Human-provided
    PHuman
  | -- | Derived from other beliefs
  PDerived [Expr]
  | -- | External source
    PExternal T.Text
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- ============================================================================
-- Helper Constructors
-- ============================================================================

-- | Create a belief with minimal annotations.
belief :: Expr -> Confidence -> Belief
belief e c = Belief e c JNone INone PNone

-- | Create a variable expression.
var :: Name -> Expr
var = EVar

-- | Create a function application.
app :: Expr -> Expr -> Expr
app = EApp

-- | Create a lambda abstraction.
lam :: Name -> Type -> Expr -> Expr
lam = ELam

-- | Add a type annotation.
ann :: Expr -> Type -> Expr
ann = EAnn

-- | Create a primitive operation.
mkOp :: Op -> Expr -> Expr -> Expr
mkOp = EPrim
