/-
CLAIR Confidence - Probabilistic OR (⊕) Operation

The oplus operation aggregates independent evidence:
  a ⊕ b = a + b - a × b

This is the algebraic sum t-conorm from fuzzy logic.
Interpretation: "Survival of doubt" - combined confidence is the probability
that at least one piece of evidence succeeds.

Key properties:
- Commutative monoid with identity 0
- Confidence-increasing: a ⊕ b ≥ max(a, b)
- De Morgan dual of multiplication: a ⊕ b = 1 - (1-a) × (1-b)

CRITICAL: (⊕, ×) do NOT form a semiring - distributivity fails!
This is mathematically fundamental, not a CLAIR limitation.

See: exploration/thread-8-verification.md §12.4
-/

import CLAIR.Confidence.Basic

namespace CLAIR

open Set unitInterval

namespace Confidence

/-!
## Definition

a ⊕ b = a + b - a × b = a + b(1-a) = a(1-b) + b
-/

/-- Probabilistic OR for aggregating independent evidence.
    Formula: a ⊕ b = a + b - ab
    Interpretation: probability at least one succeeds -/
def oplus (a b : Confidence) : Confidence :=
  ⟨(a : ℝ) + (b : ℝ) - (a : ℝ) * (b : ℝ), by
    constructor
    · -- Lower bound: 0 ≤ a + b - ab
      -- Rewrite as: a + b(1-a) ≥ 0
      have h1 : 0 ≤ 1 - (a : ℝ) := a.one_minus_nonneg
      have h2 : 0 ≤ (b : ℝ) * (1 - (a : ℝ)) := mul_nonneg b.nonneg h1
      linarith [a.nonneg]
    · -- Upper bound: a + b - ab ≤ 1
      -- Rewrite as: a + b(1-a) ≤ 1
      have h1 : (b : ℝ) * (1 - (a : ℝ)) ≤ 1 - (a : ℝ) := by
        apply mul_le_of_le_one_left a.one_minus_nonneg b.le_one
      linarith [a.le_one]⟩

/-- Unicode notation for oplus -/
infixl:65 " ⊕ " => oplus

/-!
## Boundedness
-/

/-- Oplus preserves the [0,1] bounds -/
theorem oplus_bounded (a b : Confidence) :
    0 ≤ ((a ⊕ b) : ℝ) ∧ ((a ⊕ b) : ℝ) ≤ 1 :=
  (a ⊕ b).2

theorem oplus_nonneg (a b : Confidence) : 0 ≤ ((a ⊕ b) : ℝ) :=
  (a ⊕ b).nonneg

theorem oplus_le_one (a b : Confidence) : ((a ⊕ b) : ℝ) ≤ 1 :=
  (a ⊕ b).le_one

/-!
## Algebraic Properties - Commutative Monoid Structure

([0,1], ⊕, 0) forms a commutative monoid with absorbing element 1.
-/

/-- Oplus is commutative -/
theorem oplus_comm (a b : Confidence) : a ⊕ b = b ⊕ a := by
  apply Subtype.ext
  simp only [oplus, Subtype.coe_mk]
  ring

/-- Oplus is associative -/
theorem oplus_assoc (a b c : Confidence) : (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c) := by
  apply Subtype.ext
  simp only [oplus, Subtype.coe_mk]
  ring

/-- Zero is the identity for oplus -/
theorem zero_oplus (a : Confidence) : (0 : Confidence) ⊕ a = a := by
  apply Subtype.ext
  simp only [oplus, Subtype.coe_mk]
  simp [unitInterval.coe_zero]
  ring

/-- Zero is the identity for oplus (right) -/
theorem oplus_zero (a : Confidence) : a ⊕ (0 : Confidence) = a := by
  rw [oplus_comm]
  exact zero_oplus a

/-- One absorbs under oplus -/
theorem one_oplus (a : Confidence) : (1 : Confidence) ⊕ a = 1 := by
  apply Subtype.ext
  simp only [oplus, Subtype.coe_mk]
  simp [unitInterval.coe_one]
  ring

/-- One absorbs under oplus (right) -/
theorem oplus_one (a : Confidence) : a ⊕ (1 : Confidence) = 1 := by
  rw [oplus_comm]
  exact one_oplus a

/-!
## Confidence-Increasing Property

Oplus increases confidence: a ⊕ b ≥ max(a, b)
This is the key property that distinguishes aggregation from derivation.
-/

/-- Oplus is at least as large as the first operand -/
theorem le_oplus_left (a b : Confidence) : (a : ℝ) ≤ ((a ⊕ b) : ℝ) := by
  simp only [oplus, Subtype.coe_mk]
  have h : 0 ≤ (b : ℝ) * (1 - (a : ℝ)) := mul_nonneg b.nonneg a.one_minus_nonneg
  linarith

/-- Oplus is at least as large as the second operand -/
theorem le_oplus_right (a b : Confidence) : (b : ℝ) ≤ ((a ⊕ b) : ℝ) := by
  rw [oplus_comm]
  exact le_oplus_left b a

/-- Oplus is at least as large as both operands (max) -/
theorem max_le_oplus (a b : Confidence) : max (a : ℝ) (b : ℝ) ≤ ((a ⊕ b) : ℝ) :=
  max_le (le_oplus_left a b) (le_oplus_right a b)

/-!
## Monotonicity
-/

/-- Oplus is monotone in the first argument -/
theorem oplus_mono_left (a a' b : Confidence) (h : (a : ℝ) ≤ (a' : ℝ)) :
    ((a ⊕ b) : ℝ) ≤ ((a' ⊕ b) : ℝ) := by
  simp only [oplus, Subtype.coe_mk]
  have h1 : 0 ≤ 1 - (b : ℝ) := b.one_minus_nonneg
  nlinarith

/-- Oplus is monotone in the second argument -/
theorem oplus_mono_right (a b b' : Confidence) (h : (b : ℝ) ≤ (b' : ℝ)) :
    ((a ⊕ b) : ℝ) ≤ ((a ⊕ b') : ℝ) := by
  rw [oplus_comm, oplus_comm a b']
  exact oplus_mono_left b b' a h

/-!
## De Morgan Duality

a ⊕ b = 1 - (1-a) × (1-b)

This connects oplus to multiplication via complementation.
Note: CLAIR doesn't use negation semantically, but this is mathematically useful.
-/

/-- De Morgan duality: oplus via complement and multiplication -/
theorem oplus_eq_one_sub_mul_symm (a b : Confidence) :
    ((a ⊕ b) : ℝ) = 1 - (1 - (a : ℝ)) * (1 - (b : ℝ)) := by
  simp only [oplus, Subtype.coe_mk]
  ring

/-!
## Non-Distributivity

CRITICAL: (⊕, ×) do NOT form a semiring.
Distributivity fails: a × (b ⊕ c) ≠ (a × b) ⊕ (a × c)

Counterexample: a = b = c = 0.5
  a × (b ⊕ c) = 0.5 × (0.5 + 0.5 - 0.25) = 0.5 × 0.75 = 0.375
  (a × b) ⊕ (a × c) = 0.25 + 0.25 - 0.0625 = 0.4375 ≠ 0.375

This is documented but not proven here (would require a counterexample construction).
-/

end Confidence

end CLAIR
