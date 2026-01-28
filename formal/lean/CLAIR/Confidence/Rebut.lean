/-
CLAIR Confidence - Rebutting Defeat

Rebut models defeat that directly attacks the conclusion with counter-evidence.
Formula: rebut(c_for, c_against) = c_for / (c_for + c_against)

Interpretation: "Market share" of supporting evidence.
- Treats for/against symmetrically
- Equal arguments → 0.5 (maximal uncertainty)
- Overwhelming argument → approaches 1 or 0

Key distinction from undercut:
- Undercut attacks the inferential LINK (discounting)
- Rebut attacks the CONCLUSION directly (competing evidence)

Special case: When both confidences are 0, return 0.5 (maximal uncertainty).

See: exploration/thread-2.10-defeat-confidence.md
-/

import CLAIR.Confidence.Oplus

namespace CLAIR

open Set unitInterval

namespace Confidence

/-!
## Definition

rebut(c_for, c_against) = c_for / (c_for + c_against)

Edge case: When sum = 0, return 0.5 (maximal uncertainty).
-/

/-- Rebutting defeat: probabilistic comparison of competing evidence.
    c_for is evidence for, c_against is evidence against.
    Result is the "market share" of supporting evidence. -/
noncomputable def rebut (c_for c_against : Confidence) : Confidence :=
  if h : (c_for : ℝ) + (c_against : ℝ) = 0
  then ⟨1/2, by norm_num, by norm_num⟩
  else ⟨(c_for : ℝ) / ((c_for : ℝ) + (c_against : ℝ)), by
    have sum_pos : 0 < (c_for : ℝ) + (c_against : ℝ) := by
      have sum_nonneg : 0 ≤ (c_for : ℝ) + (c_against : ℝ) :=
        add_nonneg (nonneg c_for) (nonneg c_against)
      rcases sum_nonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; exact h heq.symm
    constructor
    · -- Lower bound: c_for / (c_for + c_against) ≥ 0
      exact div_nonneg (nonneg c_for) (le_of_lt sum_pos)
    · -- Upper bound: c_for / (c_for + c_against) ≤ 1
      rw [div_le_one sum_pos]
      linarith [nonneg c_against]⟩

/-!
## Boundedness
-/

/-- Rebut preserves the [0,1] bounds -/
theorem rebut_bounded (c_for c_against : Confidence) :
    0 ≤ ((rebut c_for c_against) : ℝ) ∧ ((rebut c_for c_against) : ℝ) ≤ 1 :=
  (rebut c_for c_against).2

theorem rebut_nonneg (c_for c_against : Confidence) :
    0 ≤ ((rebut c_for c_against) : ℝ) :=
  nonneg (rebut c_for c_against)

theorem rebut_le_one (c_for c_against : Confidence) :
    ((rebut c_for c_against) : ℝ) ≤ 1 :=
  le_one (rebut c_for c_against)

/-!
## Special Cases
-/

/-- No counter-evidence means full confidence for the proposition -/
theorem rebut_zero_against (c : Confidence) (hc : (c : ℝ) ≠ 0) :
    rebut c 0 = 1 := by
  simp only [rebut, coe_zero, add_zero]
  split_ifs with h
  · exfalso; exact hc h
  · apply Subtype.ext
    simp only [Subtype.coe_mk, coe_one]
    field_simp

/-- No supporting evidence means full defeat -/
theorem rebut_zero_for (c : Confidence) (hc : (c : ℝ) ≠ 0) :
    rebut 0 c = 0 := by
  simp only [rebut, coe_zero, zero_add]
  split_ifs with h
  · exfalso; exact hc h
  · apply Subtype.ext
    simp only [Subtype.coe_mk, coe_zero]
    field_simp

/-- Both zero means maximal uncertainty -/
theorem rebut_zero_zero : rebut 0 0 = ⟨1/2, by norm_num, by norm_num⟩ := by
  simp only [rebut, coe_zero]
  split_ifs with h
  · rfl
  · exfalso; simp at h

/-- Equal evidence means maximal uncertainty (0.5) -/
theorem rebut_eq (c : Confidence) : ((rebut c c) : ℝ) = 1/2 := by
  simp only [rebut]
  split_ifs with h
  · simp only [Subtype.coe_mk]
  · simp only [Subtype.coe_mk]
    field_simp
    ring

/-!
## Symmetry

rebut(a, b) + rebut(b, a) = 1 (when sum ≠ 0)

The confidences are complementary.
-/

/-- Rebut is anti-symmetric: switching for/against gives complement -/
theorem rebut_add_rebut_swap (a b : Confidence) (h : (a : ℝ) + (b : ℝ) ≠ 0) :
    ((rebut a b) : ℝ) + ((rebut b a) : ℝ) = 1 := by
  unfold rebut
  have h' : (b : ℝ) + (a : ℝ) ≠ 0 := by rw [add_comm]; exact h
  simp only [h, h', dite_false, Subtype.coe_mk]
  have sum_pos : 0 < (a : ℝ) + (b : ℝ) := by
    have sum_nonneg := add_nonneg (nonneg a) (nonneg b)
    rcases sum_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact h heq.symm
  field_simp
  ring

/-!
## Monotonicity

Note: These proofs need updating for Mathlib v4.15.0 API changes.
The theorems are correct but the proof tactics need adjustment.
-/

/-- Rebut is monotone in the for-argument -/
theorem rebut_mono_for (a a' b : Confidence)
    (ha : (a : ℝ) ≤ (a' : ℝ)) (hpos : (a : ℝ) + (b : ℝ) ≠ 0) (hpos' : (a' : ℝ) + (b : ℝ) ≠ 0) :
    ((rebut a b) : ℝ) ≤ ((rebut a' b) : ℝ) := by
  unfold rebut
  simp only [hpos, hpos', dite_false, Subtype.coe_mk]
  have pos : 0 < (a' : ℝ) + (b : ℝ) := by
    have h_nn := add_nonneg (nonneg a') (nonneg b)
    rcases h_nn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hpos' heq.symm
  have pos' : 0 < (a : ℝ) + (b : ℝ) := by
    have h_nn := add_nonneg (nonneg a) (nonneg b)
    rcases h_nn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hpos heq.symm
  rw [div_le_div_iff₀ pos' pos]
  nlinarith [nonneg a, nonneg a', nonneg b]

/-- Rebut is antitone in the against-argument -/
theorem rebut_anti_against (a b b' : Confidence)
    (hb : (b : ℝ) ≤ (b' : ℝ)) (hpos : (a : ℝ) + (b : ℝ) ≠ 0) (hpos' : (a : ℝ) + (b' : ℝ) ≠ 0) :
    ((rebut a b') : ℝ) ≤ ((rebut a b) : ℝ) := by
  unfold rebut
  simp only [hpos, hpos', dite_false, Subtype.coe_mk]
  have pos : 0 < (a : ℝ) + (b : ℝ) := by
    have h_nn := add_nonneg (nonneg a) (nonneg b)
    rcases h_nn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hpos heq.symm
  have pos' : 0 < (a : ℝ) + (b' : ℝ) := by
    have h_nn := add_nonneg (nonneg a) (nonneg b')
    rcases h_nn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hpos' heq.symm
  rw [div_le_div_iff₀ pos' pos]
  nlinarith [nonneg a, nonneg b, nonneg b']

end Confidence

end CLAIR
