/-
CLAIR Confidence - Undercutting Defeat

Undercut models defeat that attacks the inferential link (not the conclusion).
Formula: undercut(c, d) = c × (1 - d)

Interpretation: d is the strength of the defeater.
The defeater "discounts" the confidence multiplicatively.

Key properties:
- Identity: undercut(c, 0) = c (no defeat means no change)
- Annihilation: undercut(c, 1) = 0 (complete defeat eliminates confidence)
- Composition: undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)
  Sequential undercuts combine via ⊕!

This aligns with Subjective Logic's discounting operator.

See: exploration/thread-2.10-defeat-confidence.md
-/

import CLAIR.Confidence.Oplus

namespace CLAIR

open Set unitInterval

namespace Confidence

/-!
## Definition

undercut(c, d) = c × (1 - d) = c × symm(d)

Uses Mathlib's symm operation for (1 - x).
-/

/-- Undercutting defeat: multiplicative discounting.
    c is the original confidence, d is the defeat strength.
    Result is c × (1 - d). -/
def undercut (c d : Confidence) : Confidence :=
  ⟨(c : ℝ) * (1 - (d : ℝ)), by
    constructor
    · -- Lower bound: c × (1-d) ≥ 0
      exact mul_nonneg c.nonneg d.one_minus_nonneg
    · -- Upper bound: c × (1-d) ≤ 1
      calc (c : ℝ) * (1 - (d : ℝ))
        ≤ 1 * (1 - (d : ℝ)) := by
          apply mul_le_mul_of_nonneg_right c.le_one d.one_minus_nonneg
        _ = 1 - (d : ℝ) := by ring
        _ ≤ 1 := by linarith [d.nonneg]⟩

/-!
## Boundedness
-/

/-- Undercut preserves the [0,1] bounds -/
theorem undercut_bounded (c d : Confidence) :
    0 ≤ ((undercut c d) : ℝ) ∧ ((undercut c d) : ℝ) ≤ 1 :=
  (undercut c d).2

theorem undercut_nonneg (c d : Confidence) : 0 ≤ ((undercut c d) : ℝ) :=
  (undercut c d).nonneg

theorem undercut_le_one (c d : Confidence) : ((undercut c d) : ℝ) ≤ 1 :=
  (undercut c d).le_one

/-!
## Identity and Annihilation
-/

/-- No defeat means no change -/
theorem undercut_zero (c : Confidence) : undercut c 0 = c := by
  apply Subtype.ext
  simp only [undercut, Subtype.coe_mk]
  simp [unitInterval.coe_zero]
  ring

/-- Complete defeat eliminates all confidence -/
theorem undercut_one (c : Confidence) : undercut c 1 = 0 := by
  apply Subtype.ext
  simp only [undercut, Subtype.coe_mk]
  simp [unitInterval.coe_one, unitInterval.coe_zero]
  ring

/-- Zero confidence is unaffected by defeat -/
theorem zero_undercut (d : Confidence) : undercut 0 d = 0 := by
  apply Subtype.ext
  simp only [undercut, Subtype.coe_mk]
  simp [unitInterval.coe_zero]
  ring

/-!
## Monotonicity

Undercut is:
- Monotone in confidence: higher confidence → higher result
- Antitone in defeat: stronger defeat → lower result
-/

/-- Undercut is monotone in the confidence argument -/
theorem undercut_mono_conf (c₁ c₂ d : Confidence) (h : (c₁ : ℝ) ≤ (c₂ : ℝ)) :
    ((undercut c₁ d) : ℝ) ≤ ((undercut c₂ d) : ℝ) := by
  simp only [undercut, Subtype.coe_mk]
  exact mul_le_mul_of_nonneg_right h d.one_minus_nonneg

/-- Undercut is antitone in the defeat argument -/
theorem undercut_anti_defeat (c d₁ d₂ : Confidence) (h : (d₁ : ℝ) ≤ (d₂ : ℝ)) :
    ((undercut c d₂) : ℝ) ≤ ((undercut c d₁) : ℝ) := by
  simp only [undercut, Subtype.coe_mk]
  apply mul_le_mul_of_nonneg_left
  · linarith
  · exact c.nonneg

/-!
## Undercut Reduces Confidence

Defeat can only decrease confidence.
-/

/-- Undercut never increases confidence -/
theorem undercut_le (c d : Confidence) : ((undercut c d) : ℝ) ≤ (c : ℝ) := by
  simp only [undercut, Subtype.coe_mk]
  calc (c : ℝ) * (1 - (d : ℝ))
    ≤ (c : ℝ) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · linarith [d.nonneg]
      · exact c.nonneg
    _ = (c : ℝ) := by ring

/-!
## Composition Law

The key theorem: sequential undercuts compose via ⊕.

undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)

Proof:
  undercut(undercut(c, d₁), d₂)
  = c × (1 - d₁) × (1 - d₂)
  = c × (1 - d₁ - d₂ + d₁×d₂)
  = c × (1 - (d₁ + d₂ - d₁×d₂))
  = c × (1 - (d₁ ⊕ d₂))
  = undercut(c, d₁ ⊕ d₂)

This is a beautiful algebraic result connecting defeat composition to aggregation!
-/

/-- Sequential undercuts compose via oplus -/
theorem undercut_compose (c d₁ d₂ : Confidence) :
    undercut (undercut c d₁) d₂ = undercut c (d₁ ⊕ d₂) := by
  apply Subtype.ext
  simp only [undercut, oplus, Subtype.coe_mk]
  ring

/-- Undercut composition is commutative (via oplus commutativity) -/
theorem undercut_compose_comm (c d₁ d₂ : Confidence) :
    undercut (undercut c d₁) d₂ = undercut (undercut c d₂) d₁ := by
  rw [undercut_compose, undercut_compose, oplus_comm]

/-!
## Connection to Mathlib's symm

undercut(c, d) = c × symm(d) where symm(d) = 1 - d
-/

/-- Undercut expressed using unitInterval.symm -/
theorem undercut_eq_mul_symm (c d : Confidence) :
    undercut c d = ⟨(c : ℝ) * ((unitInterval.symm d) : ℝ), (undercut c d).2⟩ := by
  apply Subtype.ext
  simp only [undercut, Subtype.coe_mk, unitInterval.coe_symm_eq]

end Confidence

end CLAIR
