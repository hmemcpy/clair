/-
CLAIR Semantics - Single-Step Reduction (Stub)

This file provides the minimal Step relation needed for the build.
Full operational semantics are still to be implemented.
-/

import CLAIR.Syntax.Expr
import CLAIR.Syntax.Subst
import CLAIR.Typing.HasType

namespace CLAIR.Syntax

open Expr

/-- Single-step reduction relation: e → e'
    Uses call-by-value evaluation order. -/
inductive Step : Expr → Expr → Prop where
  | beta : ∀ {A : Ty} {e v : Expr}, IsValue v →
      Step (app (lam A e) v) (subst0 v e)
  | letBeta : ∀ {v e : Expr}, IsValue v →
      Step (letIn v e) (subst0 v e)

/-- Notation for single step -/
infix:50 " ⟶ " => Step

namespace Step

/-- Multi-step reduction: reflexive-transitive closure of Step -/
inductive Star : Expr → Expr → Prop where
  | refl : ∀ e, Star e e
  | step : ∀ {e e' e'' : Expr}, Step e e' → Star e' e'' → Star e e''

end Step

end CLAIR.Syntax
