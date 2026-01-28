/-
CLAIR Confidence - Minimum Operation

The min operation provides conservative combination of confidence.
Formula: min(a, b) = if a ≤ b then a else b

This is the Gödel t-norm from fuzzy logic.
Interpretation: "As confident as the weakest link."

Key properties:
- Bounded meet-semilattice with identity 1
- Idempotent: min(a, a) = a
- Importantly: min(a, b) ≥ a × b (min is MORE optimistic than multiplication)

Use min when you want a pessimistic estimate without the compounding effect
of multiplication.

See: exploration/thread-8-verification.md §12.3.2
-/

import CLAIR.Confidence.Basic

namespace CLAIR

open Set unitInterval

namespace Confidence

/-!
## Definition

min(a, b) = if a ≤ b then a else b

Result is always one of the operands, so trivially in [0,1].
-/

/-- Minimum for conservative combination of confidence.
    Returns the lower of two confidences. -/
def min (a b : Confidence) : Confidence :=
  if (a : ℝ) ≤ (b : ℝ) then a else b

/-!
## Boundedness

Trivial: result is one of the operands.
-/

/-- Min preserves the [0,1] bounds -/
theorem min_bounded (a b : Confidence) :
    0 ≤ ((min a b) : ℝ) ∧ ((min a b) : ℝ) ≤ 1 := by
  unfold min
  split_ifs <;> exact ⟨Confidence.nonneg _, Confidence.le_one _⟩

theorem min_nonneg (a b : Confidence) : 0 ≤ ((min a b) : ℝ) :=
  (min_bounded a b).1

theorem min_le_one (a b : Confidence) : ((min a b) : ℝ) ≤ 1 :=
  (min_bounded a b).2

/-!
## Ordering Properties
-/

/-- Min is at most the first operand -/
theorem min_le_left (a b : Confidence) : ((min a b) : ℝ) ≤ (a : ℝ) := by
  unfold min
  split_ifs with h
  · exact le_refl _
  · push_neg at h
    exact le_of_lt h

/-- Min is at most the second operand -/
theorem min_le_right (a b : Confidence) : ((min a b) : ℝ) ≤ (b : ℝ) := by
  unfold min
  split_ifs with h
  · exact h
  · exact le_refl _

/-- Min is the greatest lower bound -/
theorem le_min (c a b : Confidence) (ha : (c : ℝ) ≤ (a : ℝ)) (hb : (c : ℝ) ≤ (b : ℝ)) :
    (c : ℝ) ≤ ((min a b) : ℝ) := by
  unfold min
  split_ifs <;> assumption

/-!
## Algebraic Properties - Bounded Meet-Semilattice

([0,1], min, 1) forms a bounded meet-semilattice (commutative idempotent monoid).
-/

/-- Min is commutative -/
theorem min_comm (a b : Confidence) : min a b = min b a := by
  unfold min
  split_ifs with h1 h2
  · -- a ≤ b and b ≤ a → a = b
    apply Subtype.ext
    linarith
  · -- a ≤ b and ¬(b ≤ a) → a < b, so min is a
    rfl
  · -- ¬(a ≤ b) and b ≤ a → b < a, so min is b
    rfl
  · -- ¬(a ≤ b) and ¬(b ≤ a) → contradiction (trichotomy)
    push_neg at h1 h2
    exfalso; linarith

/-- Min is associative -/
theorem min_assoc (a b c : Confidence) : min (min a b) c = min a (min b c) := by
  unfold min
  -- Case analysis on all orderings
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;>
    try rfl
  all_goals (apply Subtype.ext; push_neg at *; try linarith)

/-- One is the identity for min -/
theorem one_min (a : Confidence) : min 1 a = a := by
  unfold min
  split_ifs with h
  · simp only [unitInterval.coe_one] at h
    apply Subtype.ext
    linarith [a.le_one]
  · rfl

/-- One is the identity for min (right) -/
theorem min_one (a : Confidence) : min a 1 = a := by
  rw [min_comm]
  exact one_min a

/-- Zero absorbs under min -/
theorem zero_min (a : Confidence) : min 0 a = 0 := by
  unfold min
  split_ifs with h
  · rfl
  · push_neg at h
    simp only [unitInterval.coe_zero] at h
    exfalso
    linarith [a.nonneg]

/-- Zero absorbs under min (right) -/
theorem min_zero (a : Confidence) : min a 0 = 0 := by
  rw [min_comm]
  exact zero_min a

/-- Min is idempotent -/
theorem min_idem (a : Confidence) : min a a = a := by
  unfold min
  simp

/-!
## Comparison with Multiplication

Key insight: min(a, b) ≥ a × b for all a, b ∈ [0,1].

Min is MORE optimistic than multiplication:
- × compounds uncertainty: each step reduces confidence
- min just takes the worst case: doesn't compound

This is why × models derivation (each step costs) while min models
conservative combination (pessimistic but not compounding).
-/

/-- Min is at least as large as multiplication -/
theorem mul_le_min (a b : Confidence) : (a : ℝ) * (b : ℝ) ≤ ((min a b) : ℝ) := by
  unfold min
  split_ifs with h
  · -- Case a ≤ b: show a × b ≤ a
    calc (a : ℝ) * (b : ℝ)
      ≤ (a : ℝ) * 1 := by apply mul_le_mul_of_nonneg_left b.le_one a.nonneg
      _ = (a : ℝ) := mul_one _
  · -- Case b < a: show a × b ≤ b
    push_neg at h
    calc (a : ℝ) * (b : ℝ)
      ≤ 1 * (b : ℝ) := by apply mul_le_mul_of_nonneg_right a.le_one b.nonneg
      _ = (b : ℝ) := one_mul _

/-!
## Monotonicity
-/

/-- Min is monotone in the first argument -/
theorem min_mono_left (a a' b : Confidence) (h : (a : ℝ) ≤ (a' : ℝ)) :
    ((min a b) : ℝ) ≤ ((min a' b) : ℝ) := by
  unfold min
  split_ifs with h1 h2
  · exact h
  · exact le_refl _
  · linarith
  · exact le_refl _

/-- Min is monotone in the second argument -/
theorem min_mono_right (a b b' : Confidence) (h : (b : ℝ) ≤ (b' : ℝ)) :
    ((min a b) : ℝ) ≤ ((min a b') : ℝ) := by
  rw [min_comm, min_comm a b']
  exact min_mono_left b b' a h

end Confidence

end CLAIR
