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
import Mathlib

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
  | refl : ∀ A, Subtype A A

  /-- Belief subtyping: higher confidence is subtype.
      If c ≥ c', then Belief<A>[c] <: Belief<A>[c'] -/
  | belief_sub : ∀ {A : Ty} {c c' : ConfBound}, c ≥ c' →
      Subtype (Ty.belief A c) (Ty.belief A c')

  /-- Meta subtyping: higher confidence is subtype (same level).
      If c ≥ c', then Meta<A>[n][c] <: Meta<A>[n][c'] -/
  | meta_sub : ∀ {A : Ty} {n : Nat} {c c' : ConfBound}, c ≥ c' →
      Subtype (Ty.meta A n c) (Ty.meta A n c')

  /-- Function subtyping: contravariant in argument, covariant in result.
      If A' <: A and B <: B', then (A → B) <: (A' → B') -/
  | fn_sub : ∀ {A A' B B' : Ty}, Subtype A' A → Subtype B B' →
      Subtype (Ty.fn A B) (Ty.fn A' B')

  /-- Product subtyping: covariant in both components.
      If A <: A' and B <: B', then (A × B) <: (A' × B') -/
  | prod_sub : ∀ {A A' B B' : Ty}, Subtype A A' → Subtype B B' →
      Subtype (Ty.prod A B) (Ty.prod A' B')

  /-- Sum subtyping: covariant in both components.
      If A <: A' and B <: B', then (A + B) <: (A' + B') -/
  | sum_sub : ∀ {A A' B B' : Ty}, Subtype A A' → Subtype B B' →
      Subtype (Ty.sum A B) (Ty.sum A' B')

/-- Notation for subtyping -/
infix:50 " <: " => Subtype

namespace Subtype

/-!
## Basic Properties
-/

/-- Transitivity of subtyping -/
theorem trans {A B C : Ty} : A <: B → B <: C → A <: C := by
  intro _ _
  sorry

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
theorem fn_inv {A B A' B' : Ty} : Ty.fn A B <: Ty.fn A' B' →
    A' <: A ∧ B <: B' := by
  intro h
  cases h with
  | refl _ => exact ⟨Subtype.refl _, Subtype.refl _⟩
  | fn_sub hA hB => exact ⟨hA, hB⟩

/-- Inversion for belief subtyping -/
theorem belief_inv {A A' : Ty} {c c' : ConfBound} : Ty.belief A c <: Ty.belief A' c' →
    A = A' ∧ c ≥ c' := by
  intro h
  cases h with
  | refl _ => exact ⟨rfl, le_rfl⟩
  | belief_sub hc => exact ⟨rfl, hc⟩

/-- Inversion for meta subtyping -/
theorem meta_inv {A A' : Ty} {n n' : Nat} {c c' : ConfBound} :
    Ty.meta A n c <: Ty.meta A' n' c' → A = A' ∧ n = n' ∧ c ≥ c' := by
  intro h
  cases h with
  | refl _ => exact ⟨rfl, rfl, le_rfl⟩
  | meta_sub hc => exact ⟨rfl, rfl, hc⟩

/-- Inversion for product subtyping -/
theorem prod_inv {A B A' B' : Ty} : Ty.prod A B <: Ty.prod A' B' →
    A <: A' ∧ B <: B' := by
  intro h
  cases h with
  | refl _ => exact ⟨Subtype.refl _, Subtype.refl _⟩
  | prod_sub hA hB => exact ⟨hA, hB⟩

/-- Inversion for sum subtyping -/
theorem sum_inv {A B A' B' : Ty} : Ty.sum A B <: Ty.sum A' B' →
    A <: A' ∧ B <: B' := by
  intro h
  cases h with
  | refl _ => exact ⟨Subtype.refl _, Subtype.refl _⟩
  | sum_sub hA hB => exact ⟨hA, hB⟩

end Subtype

end CLAIR.Syntax
