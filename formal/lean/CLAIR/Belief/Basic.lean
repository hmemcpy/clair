/-
CLAIR Belief Type - Core Definitions

The Belief type is CLAIR's central abstraction: a value paired with
epistemic metadata (confidence, provenance, justification, invalidation).

This module defines the core Belief<α> type with just value and confidence,
laying the foundation for more complete versions.

Design approach (Thread 8.10, Session 48):
- Phase 1: Core Belief = value + confidence (this file)
- Phase 2: JustifiedBelief adds justification
- Phase 3: StratifiedBelief adds level indexing (Task 8.11)
- Phase 4: FullBelief adds provenance and invalidation

Key properties:
- Derivation (×) can only decrease confidence
- Aggregation (⊕) can only increase confidence
- Defeat (undercut/rebut) reduces confidence
- Forms a graded monad over ([0,1], ×, 1)

See: exploration/thread-8.10-belief-type-formalization.md
-/

import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut
import CLAIR.Confidence.Rebut
import CLAIR.Confidence.Min

namespace CLAIR

open Confidence

/-- A belief is a value paired with confidence in that value.
    This is the minimal core; full beliefs add justification, provenance,
    and invalidation conditions. -/
structure Belief (α : Type*) where
  /-- The value being believed -/
  value : α
  /-- Confidence in [0,1] representing epistemic commitment -/
  confidence : Confidence
  deriving Repr

namespace Belief

variable {α β γ : Type*}

/-!
## Basic Operations
-/

/-- Extract the value from a belief -/
def getValue (b : Belief α) : α := b.value

/-- Extract the confidence from a belief -/
def getConfidence (b : Belief α) : Confidence := b.confidence

/-- Create a belief with full confidence (1.0).
    Note: CLAIR discourages confidence 1.0 due to fallibilism principle -
    no belief should have complete certainty. -/
def certain (v : α) : Belief α := ⟨v, 1⟩

/-- Create a belief with zero confidence.
    Represents complete lack of commitment. -/
def uncertain (v : α) : Belief α := ⟨v, 0⟩

/-- Create a belief with specified confidence -/
def withConfidence (v : α) (c : Confidence) : Belief α := ⟨v, c⟩

/-!
## Functorial Structure

Belief is a functor: we can map over the value while preserving confidence.
-/

/-- Map a function over the value, preserving confidence -/
def map (f : α → β) (b : Belief α) : Belief β :=
  ⟨f b.value, b.confidence⟩

/-- Functor identity law: map id = id -/
theorem map_id (b : Belief α) : map id b = b := rfl

/-- Functor composition law: map f ∘ map g = map (f ∘ g) -/
theorem map_comp (f : β → γ) (g : α → β) (b : Belief α) :
    map f (map g b) = map (f ∘ g) b := rfl

/-- Map preserves confidence exactly -/
theorem map_confidence (f : α → β) (b : Belief α) :
    (map f b).confidence = b.confidence := rfl

/-!
## Derivation: Combining Beliefs

Derivation models inference: given beliefs in premises, derive a belief
in the conclusion. Confidence multiplies because each premise is a
potential point of failure.

Key property: Derivation can only DECREASE confidence.
-/

/-- Derive a new belief by applying a function to two beliefs.
    Confidence multiplies (conjunctive derivation - both premises needed). -/
def derive₂ (f : α → β → γ) (b₁ : Belief α) (b₂ : Belief β) : Belief γ :=
  ⟨f b₁.value b₂.value,
   ⟨(b₁.confidence : ℝ) * (b₂.confidence : ℝ),
    mul_mem' b₁.confidence b₂.confidence⟩⟩

/-- Derive from a single belief (unary rule) -/
def derive₁ (f : α → β) (b : Belief α) : Belief β :=
  ⟨f b.value, b.confidence⟩

/-- Derive using a rule with explicit confidence factor (rule strength).
    Total confidence = strength × c₁ × c₂ -/
def deriveWithStrength (f : α → β → γ) (s : Confidence)
    (b₁ : Belief α) (b₂ : Belief β) : Belief γ :=
  ⟨f b₁.value b₂.value,
   ⟨(s : ℝ) * (b₁.confidence : ℝ) * (b₂.confidence : ℝ), by
      have h1 := mul_mem' s b₁.confidence
      constructor
      · apply mul_nonneg
        exact h1.1
        exact b₂.confidence.nonneg
      · calc (s : ℝ) * (b₁.confidence : ℝ) * (b₂.confidence : ℝ)
          ≤ (s : ℝ) * (b₁.confidence : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left b₂.confidence.le_one h1.1
          _ = (s : ℝ) * (b₁.confidence : ℝ) := mul_one _
          _ ≤ 1 := h1.2⟩⟩

/-!
### Derivation Theorems
-/

/-- Derived confidence is bounded in [0,1] -/
theorem derive₂_bounded (f : α → β → γ) (b₁ : Belief α) (b₂ : Belief β) :
    let result := derive₂ f b₁ b₂
    0 ≤ (result.confidence : ℝ) ∧ (result.confidence : ℝ) ≤ 1 :=
  (derive₂ f b₁ b₂).confidence.2

/-- Derivation cannot increase confidence beyond first premise -/
theorem derive₂_le_left (f : α → β → γ) (b₁ : Belief α) (b₂ : Belief β) :
    ((derive₂ f b₁ b₂).confidence : ℝ) ≤ (b₁.confidence : ℝ) :=
  mul_le_left b₁.confidence b₂.confidence

/-- Derivation cannot increase confidence beyond second premise -/
theorem derive₂_le_right (f : α → β → γ) (b₁ : Belief α) (b₂ : Belief β) :
    ((derive₂ f b₁ b₂).confidence : ℝ) ≤ (b₂.confidence : ℝ) :=
  mul_le_right b₁.confidence b₂.confidence

/-- Derivation is monotone in first argument -/
theorem derive₂_mono_left (f : α → β → γ) (b₁ b₁' : Belief α) (b₂ : Belief β)
    (h : (b₁.confidence : ℝ) ≤ (b₁'.confidence : ℝ)) :
    ((derive₂ f b₁ b₂).confidence : ℝ) ≤ ((derive₂ f b₁' b₂).confidence : ℝ) := by
  simp only [derive₂, Subtype.coe_mk]
  exact mul_le_mul_of_nonneg_right h b₂.confidence.nonneg

/-- Derivation is monotone in second argument -/
theorem derive₂_mono_right (f : α → β → γ) (b₁ : Belief α) (b₂ b₂' : Belief β)
    (h : (b₂.confidence : ℝ) ≤ (b₂'.confidence : ℝ)) :
    ((derive₂ f b₁ b₂).confidence : ℝ) ≤ ((derive₂ f b₁ b₂').confidence : ℝ) := by
  simp only [derive₂, Subtype.coe_mk]
  exact mul_le_mul_of_nonneg_left h b₁.confidence.nonneg

/-!
## Aggregation: Combining Independent Evidence

Aggregation models the combination of independent supporting evidence.
Unlike derivation, aggregation INCREASES confidence - more evidence
is better!

Uses ⊕ (probabilistic OR): P(at least one succeeds).
-/

/-- Aggregate two beliefs about the same value with independent evidence.
    Uses ⊕ (probabilistic OR) for confidence combination.
    The value combiner handles potential disagreements. -/
def aggregate (b₁ b₂ : Belief α) (combine : α → α → α) : Belief α :=
  ⟨combine b₁.value b₂.value, b₁.confidence ⊕ b₂.confidence⟩

/-- Aggregate two beliefs known to have equal values (confidence only).
    This is the common case where multiple sources support the same conclusion. -/
def aggregateSame (b₁ b₂ : Belief α) (h : b₁.value = b₂.value) : Belief α :=
  ⟨b₁.value, b₁.confidence ⊕ b₂.confidence⟩

/-!
### Aggregation Theorems
-/

/-- Aggregation is bounded in [0,1] -/
theorem aggregate_bounded (b₁ b₂ : Belief α) (combine : α → α → α) :
    let result := aggregate b₁ b₂ combine
    0 ≤ (result.confidence : ℝ) ∧ (result.confidence : ℝ) ≤ 1 :=
  (aggregate b₁ b₂ combine).confidence.2

/-- Aggregation increases confidence: result ≥ first premise -/
theorem aggregate_ge_left (b₁ b₂ : Belief α) (combine : α → α → α) :
    (b₁.confidence : ℝ) ≤ ((aggregate b₁ b₂ combine).confidence : ℝ) :=
  le_oplus_left b₁.confidence b₂.confidence

/-- Aggregation increases confidence: result ≥ second premise -/
theorem aggregate_ge_right (b₁ b₂ : Belief α) (combine : α → α → α) :
    (b₂.confidence : ℝ) ≤ ((aggregate b₁ b₂ combine).confidence : ℝ) :=
  le_oplus_right b₁.confidence b₂.confidence

/-- Aggregation is commutative in confidence -/
theorem aggregate_comm (b₁ b₂ : Belief α) (combine combine' : α → α → α)
    (hc : combine b₁.value b₂.value = combine' b₂.value b₁.value) :
    (aggregate b₁ b₂ combine).confidence = (aggregate b₂ b₁ combine').confidence := by
  simp only [aggregate]
  exact oplus_comm b₁.confidence b₂.confidence

/-!
## Defeat Operations

Defeat models challenges to beliefs. CLAIR distinguishes two types:
- Undercut: attacks the inferential link (discounting)
- Rebut: attacks the conclusion directly (competing evidence)

Key property: Defeat can only DECREASE confidence.
-/

/-- Apply undercutting defeat to a belief.
    Undercut attacks the inference that produced the belief.
    d is the strength of the defeater.
    Result: c' = c × (1 - d) -/
def applyUndercut (b : Belief α) (d : Confidence) : Belief α :=
  ⟨b.value, undercut b.confidence d⟩

/-- Apply rebutting defeat.
    Rebut attacks the conclusion with counter-evidence.
    Returns the "market share" of the supporting evidence.
    Result: c' = c_for / (c_for + c_against) -/
noncomputable def applyRebut (b_for b_against : Belief α) (resolve : α → α → α) : Belief α :=
  ⟨resolve b_for.value b_against.value,
   rebut b_for.confidence b_against.confidence⟩

/-!
### Defeat Theorems
-/

/-- Undercut reduces confidence -/
theorem undercut_le (b : Belief α) (d : Confidence) :
    ((applyUndercut b d).confidence : ℝ) ≤ (b.confidence : ℝ) :=
  Confidence.undercut_le b.confidence d

/-- No undercut means no change -/
theorem undercut_zero (b : Belief α) :
    applyUndercut b 0 = b := by
  simp only [applyUndercut]
  congr 1
  exact Confidence.undercut_zero b.confidence

/-- Complete undercut eliminates confidence -/
theorem undercut_one (b : Belief α) :
    (applyUndercut b 1).confidence = 0 := by
  simp only [applyUndercut]
  exact Confidence.undercut_one b.confidence

/-- Sequential undercuts compose via ⊕ -/
theorem undercut_compose (b : Belief α) (d₁ d₂ : Confidence) :
    applyUndercut (applyUndercut b d₁) d₂ = applyUndercut b (d₁ ⊕ d₂) := by
  simp only [applyUndercut]
  congr 1
  exact undercut_compose b.confidence d₁ d₂

/-!
## Conservative Combination (Min)

Sometimes we want to combine beliefs conservatively, taking the
minimum confidence without compounding uncertainty.

Use case: When the "weakest link" determines overall confidence,
but we don't want the multiplicative effect of derivation.
-/

/-- Combine beliefs conservatively using minimum confidence -/
def combineConservative (b₁ b₂ : Belief α) (combine : α → α → α) : Belief α :=
  ⟨combine b₁.value b₂.value, Confidence.min b₁.confidence b₂.confidence⟩

/-- Conservative combination is at most either input -/
theorem conservative_le_left (b₁ b₂ : Belief α) (combine : α → α → α) :
    ((combineConservative b₁ b₂ combine).confidence : ℝ) ≤ (b₁.confidence : ℝ) :=
  min_le_left b₁.confidence b₂.confidence

/-- Conservative combination is at most either input -/
theorem conservative_le_right (b₁ b₂ : Belief α) (combine : α → α → α) :
    ((combineConservative b₁ b₂ combine).confidence : ℝ) ≤ (b₂.confidence : ℝ) :=
  min_le_right b₁.confidence b₂.confidence

/-- Conservative combination is at least derivation -/
theorem derive_le_conservative (f : α → β → γ) (b₁ : Belief α) (b₂ : Belief β)
    (combine : γ → γ → γ) :
    let derived := derive₂ f b₁ b₂
    let conservative := combineConservative ⟨derived.value, b₁.confidence⟩
                                            ⟨derived.value, b₂.confidence⟩
                                            (fun x _ => x)
    ((derived.confidence : ℝ) ≤ (conservative.confidence : ℝ)) := by
  simp only [derive₂, combineConservative, Subtype.coe_mk]
  exact mul_le_min b₁.confidence b₂.confidence

/-!
## Monadic Structure (Graded)

Belief forms a graded monad over ([0,1], ×, 1).
- Return (pure) has grade 1 (full confidence)
- Bind composes grades multiplicatively

Note: Monad laws hold up to provenance equivalence, not strict equality.
This is because bind tracks that derivation occurred.
-/

/-- Monadic bind for beliefs: derive using a belief-producing function.
    Confidence multiplies (the monad is graded over ([0,1], ×, 1)).
    This models chained derivation: first belief's value determines
    what second belief to use. -/
def bind (b : Belief α) (f : α → Belief β) : Belief β :=
  let result := f b.value
  ⟨result.value,
   ⟨(b.confidence : ℝ) * (result.confidence : ℝ),
    mul_mem' b.confidence result.confidence⟩⟩

/-- Monadic return: create a belief with full confidence -/
def pure (v : α) : Belief α := certain v

/-- Bind preserves confidence bounds -/
theorem bind_bounded (b : Belief α) (f : α → Belief β) :
    let result := bind b f
    0 ≤ (result.confidence : ℝ) ∧ (result.confidence : ℝ) ≤ 1 :=
  (bind b f).confidence.2

/-- Bind cannot increase confidence beyond input -/
theorem bind_le_left (b : Belief α) (f : α → Belief β) :
    ((bind b f).confidence : ℝ) ≤ (b.confidence : ℝ) :=
  mul_le_left b.confidence (f b.value).confidence

/-- Bind cannot increase confidence beyond result of f -/
theorem bind_le_right (b : Belief α) (f : α → Belief β) :
    ((bind b f).confidence : ℝ) ≤ ((f b.value).confidence : ℝ) :=
  mul_le_right b.confidence (f b.value).confidence

/-- Pure has full confidence -/
theorem pure_confidence (v : α) : (pure v).confidence = 1 := rfl

/-- Left identity: pure v >>= f has same confidence as f v
    (when we account for the multiplication by 1) -/
theorem bind_pure_left_confidence (v : α) (f : α → Belief β) :
    ((bind (pure v) f).confidence : ℝ) = ((f v).confidence : ℝ) := by
  simp only [bind, pure, certain, Subtype.coe_mk]
  simp only [unitInterval.coe_one, one_mul]

/-- Right identity: b >>= pure has same confidence as b
    (when we account for the multiplication by 1) -/
theorem bind_pure_right_confidence (b : Belief α) :
    ((bind b pure).confidence : ℝ) = (b.confidence : ℝ) := by
  simp only [bind, pure, certain, Subtype.coe_mk]
  simp only [unitInterval.coe_one, mul_one]

/-!
## Full Graded Monad Laws

Belief forms a graded monad over ([0,1], ×, 1).
The grading is tracked at the value level, not the type level.
These theorems prove the three monad laws hold for full Belief equality,
not just confidence components.
-/

/-- Left identity law: bind (pure a) f = f a
    This is the full equality, combining value and confidence components. -/
theorem bind_pure_left (v : α) (f : α → Belief β) :
    bind (pure v) f = f v := by
  simp only [bind, pure, certain]
  constructor <;> rfl

/-- Right identity law: bind b pure = b
    This is the full equality, combining value and confidence components. -/
theorem bind_pure_right (b : Belief α) :
    bind b pure = b := by
  simp only [bind, pure, certain]
  constructor
  · rfl
  · apply Subtype.ext
    simp only [Subtype.coe_mk, unitInterval.coe_one, mul_one]

/-- Associativity law: bind (bind b f) g = bind b (λx. bind (f x) g)
    Values match definitionally; confidences match via × associativity. -/
theorem bind_assoc (b : Belief α) (f : α → Belief β) (g : β → Belief γ) :
    bind (bind b f) g = bind b (fun x => bind (f x) g) := by
  simp only [bind]
  constructor
  · rfl  -- values match definitionally
  · apply Subtype.ext
    simp only [Subtype.coe_mk]
    ring  -- confidence associativity

/-- Associativity for confidence only (may be useful separately) -/
theorem bind_assoc_confidence (b : Belief α) (f : α → Belief β) (g : β → Belief γ) :
    ((bind (bind b f) g).confidence : ℝ) =
    ((bind b (fun x => bind (f x) g)).confidence : ℝ) := by
  simp only [bind, Subtype.coe_mk]
  ring

end Belief

end CLAIR
