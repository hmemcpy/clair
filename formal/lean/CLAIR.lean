/-
CLAIR - Comprehensible LLM AI Intermediate Representation
Lean 4 Formalization

This library formalizes the core confidence operations for CLAIR,
a language where beliefs are first-class values with explicit
confidence, provenance, justification, and invalidation conditions.

Reference: exploration/thread-8-verification.md
-/

import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut
import CLAIR.Confidence.Rebut
import CLAIR.Confidence.Min
