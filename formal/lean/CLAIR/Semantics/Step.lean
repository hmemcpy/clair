/-
CLAIR Semantics - Single-Step Reduction (Complete)

This file provides the complete small-step operational semantics for CLAIR.
Uses call-by-value evaluation order with explicit progress and stuck states.

Design: exploration/thread-8.4-extract-interpreter-analysis.md
-/

import CLAIR.Syntax.Expr
import CLAIR.Syntax.Subst
import CLAIR.Typing.HasType

namespace CLAIR.Syntax

open Expr

/-- Values are fully evaluated expressions -/
inductive IsValue : Expr → Prop where
  | lam        : ∀ {A : Ty} {e : Expr}, IsValue (lam A e)
  | pair       : ∀ {v₁ v₂ : Expr}, IsValue v₁ → IsValue v₂ → IsValue (pair v₁ v₂)
  | inl        : ∀ {B : Ty} {v : Expr}, IsValue v → IsValue (inl B v)
  | inr        : ∀ {A : Ty} {v : Expr}, IsValue v → IsValue (inr A v)
  | litNat     : ∀ {n : Nat}, IsValue (litNat n)
  | litBool    : ∀ {b : Bool}, IsValue (litBool b)
  | litString  : ∀ {s : String}, IsValue (litString s)
  | litUnit    : IsValue litUnit
  | belief     : ∀ {v : Expr} {c : ConfBound} {j : Justification},
      IsValue v → IsValue (belief v c j)

/-- Single-step reduction relation: e → e'
    Uses call-by-value evaluation order. -/
inductive Step : Expr → Expr → Prop where
  -- Beta reduction
  | beta : ∀ {A : Ty} {e v : Expr}, IsValue v →
      Step (app (lam A e) v) (subst0 v e)
  -- App context rules
  | app1 : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (app e₁ e₂) (app e₁' e₂)
  | app2 : ∀ {v₁ e₂ e₂' : Expr}, IsValue v₁ → Step e₂ e₂' →
      Step (app v₁ e₂) (app v₁ e₂')
  -- Pair rules
  | pair1 : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (pair e₁ e₂) (pair e₁' e₂)
  | pair2 : ∀ {v₁ e₂ e₂' : Expr}, IsValue v₁ → Step e₂ e₂' →
      Step (pair v₁ e₂) (pair v₁ e₂')
  | fstPair : ∀ {v₁ v₂ : Expr}, IsValue v₁ → IsValue v₂ →
      Step (fst (pair v₁ v₂)) v₁
  | fstCtx : ∀ {e e' : Expr}, Step e e' →
      Step (fst e) (fst e')
  | sndPair : ∀ {v₁ v₂ : Expr}, IsValue v₁ → IsValue v₂ →
      Step (snd (pair v₁ v₂)) v₂
  | sndCtx : ∀ {e e' : Expr}, Step e e' →
      Step (snd e) (snd e')
  -- Sum rules
  | caseInl : ∀ {B : Ty} {v e₁ e₂ : Expr}, IsValue v →
      Step (Expr.case (inl B v) e₁ e₂) (subst0 v e₁)
  | caseInr : ∀ {A : Ty} {v e₁ e₂ : Expr}, IsValue v →
      Step (Expr.case (inr A v) e₁ e₂) (subst0 v e₂)
  | caseCtx : ∀ {e e' e₁ e₂ : Expr}, Step e e' →
      Step (Expr.case e e₁ e₂) (Expr.case e' e₁ e₂)
  -- Let rules
  | letBeta : ∀ {v e : Expr}, IsValue v →
      Step (letIn v e) (subst0 v e)
  | letCtx : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (letIn e₁ e₂) (letIn e₁' e₂)
  -- Belief operations
  | valBelief : ∀ {v : Expr} {c : ConfBound} {j : Justification},
      IsValue v → Step (val (belief v c j)) v
  | valCtx : ∀ {e e' : Expr}, Step e e' →
      Step (val e) (val e')
  | confBelief : ∀ {v : Expr} {c : ConfBound} {j : Justification},
      IsValue v → Step (conf (belief v c j)) (belief v c j)
  | confCtx : ∀ {e e' : Expr}, Step e e' →
      Step (conf e) (conf e')
  | justBelief : ∀ {v : Expr} {c : ConfBound} {j : Justification},
      IsValue v → Step (just (belief v c j)) (litString (toString j))
  | justCtx : ∀ {e e' : Expr}, Step e e' →
      Step (just e) (just e')
  -- Derivation (context rules only - computation in evaluator)
  | derive1 : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (derive e₁ e₂) (derive e₁' e₂)
  | derive2 : ∀ {v₁ e₂ e₂' : Expr}, IsValue v₁ → Step e₂ e₂' →
      Step (derive v₁ e₂) (derive v₁ e₂')
  -- Aggregation (context rules only - computation in evaluator)
  | aggregate1 : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (aggregate e₁ e₂) (aggregate e₁' e₂)
  | aggregate2 : ∀ {v₁ e₂ e₂' : Expr}, IsValue v₁ → Step e₂ e₂' →
      Step (aggregate v₁ e₂) (aggregate v₁ e₂')
  -- Defeat operations (context rules only - computation in evaluator)
  | undercut1 : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (undercut e₁ e₂) (undercut e₁' e₂)
  | undercut2 : ∀ {v₁ e₂ e₂' : Expr}, IsValue v₁ → Step e₂ e₂' →
      Step (undercut v₁ e₂) (undercut v₁ e₂')
  | rebut1 : ∀ {e₁ e₁' e₂ : Expr}, Step e₁ e₁' →
      Step (rebut e₁ e₂) (rebut e₁' e₂)
  | rebut2 : ∀ {v₁ e₂ e₂' : Expr}, IsValue v₁ → Step e₂ e₂' →
      Step (rebut v₁ e₂) (rebut v₁ e₂')
  -- Introspection
  | introspectValue : ∀ {v : Expr}, IsValue v →
      Step (introspect v) v
  | introspectCtx : ∀ {e e' : Expr}, Step e e' →
      Step (introspect e) (introspect e')

/-- Notation for single step -/
infix:50 " ⟶ " => Step

namespace Step

/-- Multi-step reduction: reflexive-transitive closure of Step -/
inductive Star : Expr → Expr → Prop where
  | refl : ∀ e, Star e e
  | step : ∀ {e e' e'' : Expr}, Step e e' → Star e' e'' → Star e e''

/-- Notation for multi-step (zero or more steps) -/
infix:50 " ⟶* " => Star

/-- Notation for multi-step (one or more steps) -/
inductive Star₁ : Expr → Expr → Prop where
  | step₁ : ∀ {e e' : Expr}, Step e e' → Star₁ e e'
  | trans : ∀ {e e' e'' : Expr}, Step e e' → Star₁ e' e'' → Star₁ e e''

infix:50 " ⟶+ " => Star₁

end Step

end CLAIR.Syntax
