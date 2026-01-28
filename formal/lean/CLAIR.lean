/-
CLAIR - Comprehensible LLM AI Intermediate Representation
Lean 4 Formalization

This library formalizes the core types and operations for CLAIR,
a language where beliefs are first-class values with explicit
confidence, provenance, justification, and invalidation conditions.

Modules:
- Confidence: The [0,1] interval type with operations (×, ⊕, undercut, rebut, min)
- Belief: The core Belief<α> type pairing values with confidence

Reference: exploration/thread-8-verification.md, exploration/thread-8.10-belief-type-formalization.md
-/

-- Confidence type and operations
import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut
import CLAIR.Confidence.Rebut
import CLAIR.Confidence.Min

-- Belief type (Session 48)
import CLAIR.Belief.Basic
