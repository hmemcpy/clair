/-
CLAIR Typing - Subtyping Relation

Defines the subtyping relation for CLAIR types.
Key principle: Higher confidence is a subtype.

  Belief<A>[c] <: Belief<A>[c']  when c ≥ c'

This means a more confident belief can be used where a
less confident one is expected.

Function types have standard variance:
- Contravariant in argument type
- Covariant in result type

See: exploration/thread-8.12-clair-syntax-lean.md, Thread 2.23
-/

import CLAIR.Syntax.Types

namespace CLAIR.Syntax

/-!
## Subtyping Relation

The subtyping judgment A <: B means "A is a subtype of B" or
"values of type A can be used where type B is expected".
-/

/-- Subtyping relation for CLAIR types.
    Key insight: Higher confidence → subtype.
    This is opposite from resource grading (where more resources = supertype). -/
inductive Subtype : Ty → Ty → Prop where
  /-- Reflexivity: every type is a subtype of itself -/
  | refl : Subtype A A

  /-- Belief subtyping: higher confidence is subtype.
      If c ≥ c', then Belief<A>[c] <: Belief<A>[c'] -/
  | belief_sub : c ≥ c' → Subtype (Ty.belief A c) (Ty.belief A c')

  /-- Meta subtyping: higher confidence is subtype (same level).
      If c ≥ c', then Meta<A>[n][c] <: Meta<A>[n][c'] -/
  | meta_sub : c ≥ c' → Subtype (Ty.meta A n c) (Ty.meta A n c')

  /-- Function subtyping: contravariant in argument, covariant in result.
      If A' <: A and B <: B', then (A → B) <: (A' → B') -/
  | fn_sub : Subtype A' A → Subtype B B' →
             Subtype (Ty.fn A B) (Ty.fn A' B')

  /-- Product subtyping: covariant in both components.
      If A <: A' and B <: B', then (A × B) <: (A' × B') -/
  | prod_sub : Subtype A A' → Subtype B B' →
               Subtype (Ty.prod A B) (Ty.prod A' B')

  /-- Sum subtyping: covariant in both components.
      If A <: A' and B <: B', then (A + B) <: (A' + B') -/
  | sum_sub : Subtype A A' → Subtype B B' →
              Subtype (Ty.sum A B) (Ty.sum A' B')

/-- Notation for subtyping -/
infix:50 " <: " => Subtype

namespace Subtype

/-!
## Basic Properties
-/

/-- Transitivity of subtyping -/
theorem trans : A <: B → B <: C → A <: C := by
  intro h1 h2
  induction h1 generalizing C with
  | refl => exact h2
  | belief_sub hc =>
    cases h2 with
    | refl => exact belief_sub hc
    | belief_sub hc' => exact belief_sub (le_trans hc' hc)
  | meta_sub hc =>
    cases h2 with
    | refl => exact meta_sub hc
    | meta_sub hc' => exact meta_sub (le_trans hc' hc)
  | fn_sub hA hB ihA ihB =>
    cases h2 with
    | refl => exact fn_sub hA hB
    | fn_sub hA' hB' =>
      exact fn_sub (ihA hA') (ihB hB')
  | prod_sub hA hB ihA ihB =>
    cases h2 with
    | refl => exact prod_sub hA hB
    | prod_sub hA' hB' =>
      exact prod_sub (ihA hA') (ihB hB')
  | sum_sub hA hB ihA ihB =>
    cases h2 with
    | refl => exact sum_sub hA hB
    | sum_sub hA' hB' =>
      exact sum_sub (ihA hA') (ihB hB')

/-!
## Confidence Monotonicity

Operations preserve subtyping when confidence changes.
-/

/-- Belief with higher confidence can be used for derivation -/
theorem belief_conf_mono {A : Ty} {c c' : ConfBound} (h : c ≥ c') :
    Ty.belief A c <: Ty.belief A c' :=
  belief_sub h

/-- Meta with higher confidence can be used -/
theorem meta_conf_mono {A : Ty} {n : Nat} {c c' : ConfBound} (h : c ≥ c') :
    Ty.meta A n c <: Ty.meta A n c' :=
  meta_sub h

/-!
## Inversion Lemmas

Useful for proving type safety.
-/

/-- Inversion for function subtyping -/
theorem fn_inv : Ty.fn A B <: Ty.fn A' B' →
    A' <: A ∧ B <: B' := by
  intro h
  cases h with
  | refl => exact ⟨refl, refl⟩
  | fn_sub hA hB => exact ⟨hA, hB⟩

/-- Inversion for belief subtyping -/
theorem belief_inv : Ty.belief A c <: Ty.belief A' c' →
    A = A' ∧ c ≥ c' := by
  intro h
  cases h with
  | refl => exact ⟨rfl, le_refl c⟩
  | belief_sub hc => exact ⟨rfl, hc⟩

/-- Inversion for meta subtyping -/
theorem meta_inv : Ty.meta A n c <: Ty.meta A' n' c' →
    A = A' ∧ n = n' ∧ c ≥ c' := by
  intro h
  cases h with
  | refl => exact ⟨rfl, rfl, le_refl c⟩
  | meta_sub hc => exact ⟨rfl, rfl, hc⟩

/-- Inversion for product subtyping -/
theorem prod_inv : Ty.prod A B <: Ty.prod A' B' →
    A <: A' ∧ B <: B' := by
  intro h
  cases h with
  | refl => exact ⟨refl, refl⟩
  | prod_sub hA hB => exact ⟨hA, hB⟩

/-- Inversion for sum subtyping -/
theorem sum_inv : Ty.sum A B <: Ty.sum A' B' →
    A <: A' ∧ B <: B' := by
  intro h
  cases h with
  | refl => exact ⟨refl, refl⟩
  | sum_sub hA hB => exact ⟨hA, hB⟩

end Subtype

end CLAIR.Syntax
