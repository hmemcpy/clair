/-
CLAIR - Comprehensible LLM AI Intermediate Representation
Lean 4 Formalization

This library formalizes the core types and operations for CLAIR,
a language where beliefs are first-class values with explicit
confidence, provenance, justification, and invalidation conditions.

Modules:
- Confidence: The [0,1] interval type with operations (×, ⊕, undercut, rebut, min)
- Belief: The core Belief<α> type pairing values with confidence
- Belief.Stratified: Level-indexed beliefs for safe introspection (Session 49)
- Syntax: Type and expression grammars with de Bruijn indices (Session 64)
- Typing: Typing relations with graded confidence judgments (Session 64)
- Semantics: Small-step operational semantics (Session 64)

Reference: exploration/thread-8-verification.md, exploration/thread-8.10-belief-type-formalization.md,
           exploration/thread-8.12-clair-syntax-lean.md
-/

-- Confidence type and operations (semantic)
import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut
import CLAIR.Confidence.Rebut
import CLAIR.Confidence.Min

-- Belief types (semantic)
import CLAIR.Belief.Basic        -- Core Belief<α> type (Session 48)
import CLAIR.Belief.Stratified   -- Level-indexed StratifiedBelief<n, α> (Session 49)

-- Syntax (syntactic representation) - Session 64
import CLAIR.Syntax.Types        -- Type grammar
import CLAIR.Syntax.Expr         -- Expression grammar with de Bruijn indices
import CLAIR.Syntax.Context      -- Typing contexts
import CLAIR.Syntax.Subst        -- Substitution for de Bruijn terms

-- Typing (type system) - Session 64
import CLAIR.Typing.Subtype      -- Subtyping relation
import CLAIR.Typing.HasType      -- Typing judgment Γ ⊢ e : A @c

-- Semantics (operational) - Session 64
import CLAIR.Semantics.Step      -- Small-step reduction
import CLAIR.Semantics.Eval      -- Computable evaluation function

-- Parser for surface syntax - Session 82
import CLAIR.Parser             -- S-expression parser
