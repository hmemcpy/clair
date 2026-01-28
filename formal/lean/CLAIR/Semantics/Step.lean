/-
CLAIR Semantics - Single-Step Reduction

Defines the small-step operational semantics for CLAIR.
The judgment e → e' means "e reduces to e' in one step".

Key beta reductions:
- Function application: (λ:A. e) v → e[v/x]
- Let binding: let x = v in e → e[v/x]
- Projections: (v₁, v₂).1 → v₁
- Belief extraction: val(belief(v, c, j)) → v
- Defeat application: undercut(belief(...), belief(...)) → belief(...)
- Aggregation: aggregate(belief(v, c₁, j₁), belief(v, c₂, j₂)) → belief(v, c₁⊕c₂, ...)

See: exploration/thread-8.12-clair-syntax-lean.md
-/

import CLAIR.Syntax.Expr
import CLAIR.Syntax.Subst
import CLAIR.Typing.HasType

namespace CLAIR.Syntax

open Expr

/-!
## Single-Step Reduction

The Step relation defines how expressions reduce.
Call-by-value: arguments must be values before application.
-/

/-- Single-step reduction relation: e → e'
    Uses call-by-value evaluation order. -/
inductive Step : Expr → Expr → Prop where

  /-!
  ### Lambda Calculus Beta Reductions
  -/

  /-- Beta reduction for functions: (λ:A. e) v → e[v/x] -/
  | beta : IsValue v →
           Step (app (lam A e) v) (subst0 v e)

  /-- Let beta: let x = v in e → e[v/x] -/
  | letBeta : IsValue v →
              Step (letIn v e) (subst0 v e)

  /-!
  ### Product Beta Reductions
  -/

  /-- First projection: (v₁, v₂).1 → v₁ -/
  | fstBeta : IsValue v₁ → IsValue v₂ →
              Step (fst (pair v₁ v₂)) v₁

  /-- Second projection: (v₁, v₂).2 → v₂ -/
  | sndBeta : IsValue v₁ → IsValue v₂ →
              Step (snd (pair v₁ v₂)) v₂

  /-!
  ### Sum Beta Reductions
  -/

  /-- Case-inl: case inl(v) of { e₁ | e₂ } → e₁[v/x] -/
  | caseInlBeta : IsValue v →
                  Step (case (inl B v) e₁ e₂) (subst0 v e₁)

  /-- Case-inr: case inr(v) of { e₁ | e₂ } → e₂[v/x] -/
  | caseInrBeta : IsValue v →
                  Step (case (inr A v) e₁ e₂) (subst0 v e₂)

  /-!
  ### Belief Beta Reductions
  -/

  /-- Value extraction: val(belief(v, c, j)) → v -/
  | valBeta : IsValue v →
              Step (val (belief v c j)) v

  /-- Confidence extraction: conf(belief(v, c, j)) → litNat(representation of c)
      Note: Simplified - returns 0 for now -/
  | confBeta : IsValue v →
               Step (conf (belief v c j)) (litNat 0)  -- Simplified

  /-- Justification extraction: just(belief(v, c, j)) → litUnit
      Note: Simplified - returns unit for now -/
  | justBeta : IsValue v →
               Step (just (belief v c j)) litUnit  -- Simplified

  /-!
  ### Derivation Beta Reduction
  -/

  /-- Derivation: derive(belief(v₁, c₁, j₁), belief(v₂, c₂, j₂)) →
                  belief((v₁, v₂), c₁×c₂, rule("derive", [j₁, j₂])) -/
  | deriveBeta : IsValue v₁ → IsValue v₂ →
                 Step (derive (belief v₁ c₁ j₁) (belief v₂ c₂ j₂))
                      (belief (pair v₁ v₂) (c₁ * c₂)
                              (Justification.rule "derive" [j₁, j₂]))

  /-!
  ### Aggregation Beta Reduction
  -/

  /-- Aggregation: aggregate(belief(v, c₁, j₁), belief(v, c₂, j₂)) →
                   belief(v, c₁⊕c₂, agg([j₁, j₂]))
      Note: Assumes values are equal (same conclusion being aggregated) -/
  | aggregateBeta : IsValue v₁ → IsValue v₂ →
                    Step (aggregate (belief v₁ c₁ j₁) (belief v₂ c₂ j₂))
                         (belief v₁ (ConfBound.oplus c₁ c₂)
                                 (Justification.agg [j₁, j₂]))

  /-!
  ### Defeat Beta Reductions
  -/

  /-- Undercut: undercut(belief(v, c, j_v), belief(d, c_d, j_d)) →
                belief(v, c×(1-c_d), undercut_j(j_v, j_d)) -/
  | undercutBeta : IsValue v → IsValue d →
                   Step (undercut (belief v c_v j_v) (belief d c_d j_d))
                        (belief v (ConfBound.undercut c_v c_d)
                                (Justification.undercut_j j_v j_d))

  /-- Rebut: rebut(belief(v_for, c_for, j_for), belief(v_against, c_against, j_against)) →
             belief(v_for, rebut_conf(c_for, c_against), rebut_j(j_for, j_against))
      Note: v_for wins the value; confidence is "market share" -/
  | rebutBeta : IsValue v_for → IsValue v_against →
                Step (rebut (belief v_for c_for j_for)
                           (belief v_against c_against j_against))
                     (belief v_for (ConfBound.rebut c_for c_against)
                             (Justification.rebut_j j_for j_against))

  /-!
  ### Congruence Rules (Evaluation Contexts)

  These rules specify evaluation order: call-by-value, left-to-right.
  -/

  -- Application: evaluate function first, then argument
  | app₁ : Step e₁ e₁' →
           Step (app e₁ e₂) (app e₁' e₂)

  | app₂ : IsValue v →
           Step e₂ e₂' →
           Step (app v e₂) (app v e₂')

  -- Pair: evaluate left-to-right
  | pair₁ : Step e₁ e₁' →
            Step (pair e₁ e₂) (pair e₁' e₂)

  | pair₂ : IsValue v →
            Step e₂ e₂' →
            Step (pair v e₂) (pair v e₂')

  -- Projections
  | fst_cong : Step e e' →
               Step (fst e) (fst e')

  | snd_cong : Step e e' →
               Step (snd e) (snd e')

  -- Injections
  | inl_cong : Step e e' →
               Step (inl B e) (inl B e')

  | inr_cong : Step e e' →
               Step (inr A e) (inr A e')

  -- Case: evaluate scrutinee first
  | case_cong : Step e e' →
                Step (case e e₁ e₂) (case e' e₁ e₂)

  -- Belief constructor: evaluate value first
  | belief_cong : Step v v' →
                  Step (belief v c j) (belief v' c j)

  -- Extractions
  | val_cong : Step e e' →
               Step (val e) (val e')

  | conf_cong : Step e e' →
                Step (conf e) (conf e')

  | just_cong : Step e e' →
                Step (just e) (just e')

  -- Derivation: left-to-right
  | derive₁ : Step e₁ e₁' →
              Step (derive e₁ e₂) (derive e₁' e₂)

  | derive₂ : IsValue v →
              Step e₂ e₂' →
              Step (derive v e₂) (derive v e₂')

  -- Aggregation: left-to-right
  | aggregate₁ : Step e₁ e₁' →
                 Step (aggregate e₁ e₂) (aggregate e₁' e₂)

  | aggregate₂ : IsValue v →
                 Step e₂ e₂' →
                 Step (aggregate v e₂) (aggregate v e₂')

  -- Undercut: left-to-right
  | undercut₁ : Step e e' →
                Step (undercut e d) (undercut e' d)

  | undercut₂ : IsValue v →
                Step d d' →
                Step (undercut v d) (undercut v d')

  -- Rebut: left-to-right
  | rebut₁ : Step e e' →
             Step (rebut e d) (rebut e' d)

  | rebut₂ : IsValue v →
             Step d d' →
             Step (rebut v d) (rebut v d')

  -- Introspection
  | introspect_cong : Step e e' →
                      Step (introspect e) (introspect e')

  -- Let: evaluate definition first
  | letIn_cong : Step e₁ e₁' →
                 Step (letIn e₁ e₂) (letIn e₁' e₂)

/-- Notation for single step -/
infix:50 " ⟶ " => Step

namespace Step

/-!
## Multi-Step Reduction

The reflexive-transitive closure of single-step reduction.
-/

/-- Multi-step reduction: reflexive-transitive closure of Step -/
inductive Star : Expr → Expr → Prop where
  | refl : Star e e
  | step : e ⟶ e' → Star e' e'' → Star e e''

/-- Notation for multi-step -/
infix:50 " ⟶* " => Star

/-- Single step implies multi-step -/
theorem step_to_star : e ⟶ e' → e ⟶* e' :=
  fun h => Star.step h Star.refl

/-- Multi-step is transitive -/
theorem star_trans : e₁ ⟶* e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃ := by
  intro h1 h2
  induction h1 with
  | refl => exact h2
  | step hs hr ih => exact Star.step hs (ih h2)

/-!
## Progress and Preservation Statements

These are the key type safety theorems. Full proofs are in
CLAIR/Safety/ modules (to be implemented).
-/

/-- Progress: A closed, well-typed term is either a value or can step.
    (Statement only - proof is complex) -/
theorem progress_statement :
    ∀ (e : Expr) (A : Ty) (c : ConfBound),
    HasType [] e A c → IsValue e ∨ ∃ e', e ⟶ e' := by
  sorry  -- To be proven in Safety/Progress.lean

/-- Preservation: Stepping preserves types (confidence may decrease).
    (Statement only - proof requires substitution lemma) -/
theorem preservation_statement :
    ∀ (e e' : Expr) (A : Ty) (c : ConfBound),
    HasType [] e A c → e ⟶ e' → ∃ c', c' ≤ c ∧ HasType [] e' A c' := by
  sorry  -- To be proven in Safety/Preservation.lean

/-- Type Safety: Well-typed terms don't get stuck.
    Corollary of progress + preservation. -/
theorem type_safety_statement :
    ∀ (e : Expr) (A : Ty) (c : ConfBound),
    HasType [] e A c → ∀ e', e ⟶* e' → IsValue e' ∨ ∃ e'', e' ⟶ e'' := by
  sorry  -- Follows from progress + preservation

end Step

end CLAIR.Syntax
