/-
CLAIR Confidence Type - Basic Definitions

The Confidence type represents epistemic commitment on a [0,1] scale.
Key insight: Confidence is NOT probability.
- No normalization requirement (can believe both P and ¬P)
- Represents degree of commitment, not frequency or degree of belief
- 0.5 is maximal uncertainty, not "coin flip"

We use Mathlib's unitInterval as the foundation.
See: exploration/thread-8-verification.md, Thread 1
-/

import Mathlib.Topology.UnitInterval

namespace CLAIR

open Set unitInterval

/-!
## Confidence Type Definition

CLAIR's Confidence is exactly Mathlib's unitInterval: the closed interval [0,1] in ℝ.
This provides:
- Full multiplication monoid structure (via LinearOrderedCommMonoidWithZero)
- The symm operation (1 - x) for undercut
- Bound lemmas (nonneg, le_one)
- The unit_interval tactic for proof automation
-/

/-- Confidence values are the unit interval [0,1].
    Represents epistemic commitment, not probability. -/
abbrev Confidence := unitInterval

namespace Confidence

/-- Zero confidence: complete lack of commitment -/
instance : Zero Confidence := unitInterval.hasZero

/-- Full confidence: complete commitment (but not certainty in the epistemological sense) -/
instance : One Confidence := unitInterval.hasOne

/-- Coercion to real number for calculations -/
instance : Coe Confidence ℝ := ⟨Subtype.val⟩

/-!
## Basic Properties

These follow directly from Mathlib's unitInterval infrastructure.
-/

/-- Confidence values are non-negative -/
theorem nonneg (c : Confidence) : 0 ≤ (c : ℝ) := c.2.1

/-- Confidence values are at most 1 -/
theorem le_one (c : Confidence) : (c : ℝ) ≤ 1 := c.2.2

/-- The complement (1 - c) is also in [0,1] -/
theorem one_minus_nonneg (c : Confidence) : 0 ≤ 1 - (c : ℝ) := by linarith [Confidence.le_one c]

/-- The complement (1 - c) is at most 1 -/
theorem one_minus_le_one (c : Confidence) : 1 - (c : ℝ) ≤ 1 := by linarith [Confidence.nonneg c]

/-!
## Multiplication

Multiplication on Confidence comes from Mathlib's unitInterval monoid structure.
This models conjunctive derivation: if A has confidence c₁ and B has confidence c₂,
and B is derived from A, then B has confidence c₁ × c₂ (assuming independence).

Key property: Derivation can only decrease confidence.
-/

/-- Multiplication is closed on Confidence (from Mathlib) -/
theorem mul_mem' (a b : Confidence) : (a : ℝ) * (b : ℝ) ∈ Icc 0 1 :=
  ⟨mul_nonneg (nonneg a) (nonneg b),
   calc (a : ℝ) * b ≤ (a : ℝ) * 1 := by apply mul_le_mul_of_nonneg_left (le_one b) (nonneg a)
     _ = a := mul_one _
     _ ≤ 1 := le_one a⟩

/-- Derivation can only decrease confidence -/
theorem mul_le_left (a b : Confidence) : (a : ℝ) * (b : ℝ) ≤ (a : ℝ) := by
  calc (a : ℝ) * b ≤ (a : ℝ) * 1 := by apply mul_le_mul_of_nonneg_left (le_one b) (nonneg a)
    _ = a := mul_one _

/-- Derivation can only decrease confidence (symmetric) -/
theorem mul_le_right (a b : Confidence) : (a : ℝ) * (b : ℝ) ≤ (b : ℝ) := by
  rw [mul_comm]
  exact mul_le_left b a

end Confidence

end CLAIR
