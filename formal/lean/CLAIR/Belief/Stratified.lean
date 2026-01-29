/-
CLAIR Stratified Belief Type - Level-Indexed Beliefs with Löb Discount

Stratified beliefs add an introspection level parameter to the basic Belief type.
This formalizes Tarski's hierarchy: level-n beliefs can only reference level-m
beliefs where m < n, preventing Liar-like paradoxes.

Key innovation (2026-01-29): Löb discount for meta-beliefs.
When introspecting (forming beliefs about beliefs), confidence is squared: c → c².
This prevents confidence bootstrapping through meta-reasoning.

Example: Starting at 0.9 confidence:
- Level 0: c = 0.9
- Level 1: c² = 0.81
- Level 2: c⁴ ≈ 0.65
- Level 3: c⁸ ≈ 0.43

Key properties:
- Level 0 is ground level (no introspection possible)
- Introspection requires proof that m < n
- Löb discount: introspectWithLoeb applies c → c²
- Level-preserving operations: map, derive, aggregate, defeat
- Well-foundedness via Nat.lt
- Anti-bootstrapping theorem: no_confidence_bootstrap

See: notes/exploration-2026-01-29-minimal-spec.md
     notes/reassessment-2026-01-29.md
-/

import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut
import CLAIR.Belief.Basic

namespace CLAIR

open Confidence

/-!
## Meta Type

The Meta wrapper represents metadata about a belief's content.
Used when introspecting a lower-level belief.
-/

/-- Metadata about a value, used when introspecting beliefs.
    Wraps the original value with optional descriptive information. -/
structure Meta (α : Type*) where
  /-- The original value being introspected -/
  original : α
  /-- Optional description for reflection -/
  description : Option String := none

namespace Meta

variable {α β : Type*}

/-- Map over the wrapped value -/
def map (f : α → β) (m : Meta α) : Meta β :=
  ⟨f m.original, m.description⟩

/-- Extract the original value -/
def unwrap (m : Meta α) : α := m.original

end Meta

/-!
## Stratified Belief Type

A stratified belief is indexed by an introspection level n.
Level-n beliefs can introspect level-m beliefs only when m < n.
Level 0 is the ground level where no introspection is possible.
-/

/-- A stratified belief at introspection level n.
    The level parameter enforces Tarski's hierarchy, preventing
    self-referential paradoxes like the Liar.

    - Level 0: Ground-level beliefs (cannot introspect anything)
    - Level n > 0: Can introspect beliefs at levels 0, 1, ..., n-1 -/
structure StratifiedBelief (level : Nat) (α : Type*) where
  /-- The value being believed -/
  value : α
  /-- Confidence in [0,1] representing epistemic commitment -/
  confidence : Confidence

namespace StratifiedBelief

variable {α β γ : Type*} {n m : Nat}

/-!
## Basic Operations
-/

/-- Extract the value from a stratified belief -/
def getValue (b : StratifiedBelief n α) : α := b.value

/-- Extract the confidence from a stratified belief -/
def getConfidence (b : StratifiedBelief n α) : Confidence := b.confidence

/-- Create a stratified belief with full confidence at any level -/
def certain (v : α) : StratifiedBelief n α := ⟨v, 1⟩

/-- Create a stratified belief with zero confidence -/
def uncertain (v : α) : StratifiedBelief n α := ⟨v, 0⟩

/-- Create a stratified belief with specified confidence -/
def withConfidence (v : α) (c : Confidence) : StratifiedBelief n α := ⟨v, c⟩

/-!
## Introspection

The critical operation that requires level increase.
Introspection produces a belief about a lower-level belief.
The proof obligation h : m < n ensures well-foundedness.
-/

/-- Introspect a lower-level belief from a higher level (WITHOUT Löb discount).
    This is the basic operation enforcing Tarski's hierarchy.

    NOTE: For meta-beliefs (beliefs about beliefs), use `introspectWithLoeb`
    which applies the Löb discount to prevent confidence bootstrapping.

    - Source: belief at level m
    - Target: belief about that belief, at level n where n > m
    - The proof h : m < n is required and checked at compile time

    This prevents Liar-like paradoxes: a belief cannot introspect itself
    because that would require m < m, which is impossible. -/
def introspect (_h : m < n) (b : StratifiedBelief m α) : StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, none⟩
    confidence := b.confidence }

/-- Introspect with a description (WITHOUT Löb discount) -/
def introspectWithDesc (_h : m < n) (b : StratifiedBelief m α) (desc : String) :
    StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, some desc⟩
    confidence := b.confidence }

/-!
### Löb Discount

The Löb discount prevents confidence bootstrapping through meta-levels.
When reasoning about one's own beliefs (introspection), confidence must decrease.

Formula: c → c² (squaring)

This ensures that confidence strictly decreases through meta-levels:
- Level 0: c = 0.9
- Level 1 (about L0): c² = 0.81
- Level 2 (about L1): c⁴ ≈ 0.65
- Level 3 (about L2): c⁸ ≈ 0.43

No finite chain of meta-reasoning can bootstrap confidence back up.
-/

/-- Apply the Löb discount: c → c²
    This is the confidence penalty for meta-level reasoning. -/
def loebDiscount (c : Confidence) : Confidence :=
  ⟨(c : ℝ) * (c : ℝ), mul_mem' c c⟩

/-- Löb discount reduces confidence (unless already at 0 or 1) -/
theorem loebDiscount_le (c : Confidence) : (loebDiscount c : ℝ) ≤ (c : ℝ) :=
  mul_le_left c c

/-- Löb discount of 1 is 1 -/
theorem loebDiscount_one : loebDiscount 1 = 1 := by
  apply Subtype.ext
  simp only [loebDiscount, Subtype.coe_mk, coe_one, mul_one]

/-- Löb discount of 0 is 0 -/
theorem loebDiscount_zero : loebDiscount 0 = 0 := by
  apply Subtype.ext
  simp only [loebDiscount, Subtype.coe_mk, coe_zero, mul_zero]

/-- Löb discount is strictly decreasing for 0 < c < 1 -/
theorem loebDiscount_strict_lt (c : Confidence) (h0 : 0 < (c : ℝ)) (h1 : (c : ℝ) < 1) :
    (loebDiscount c : ℝ) < (c : ℝ) := by
  simp only [loebDiscount, Subtype.coe_mk]
  have : (c : ℝ) * (c : ℝ) < (c : ℝ) * 1 := by
    apply mul_lt_mul_of_pos_left h1 h0
  linarith

/-- Introspect with Löb discount (RECOMMENDED for meta-beliefs).
    Applies c → c² to prevent confidence bootstrapping.

    Use this when forming beliefs about beliefs to ensure
    that meta-reasoning cannot inflate confidence. -/
def introspectWithLoeb (_h : m < n) (b : StratifiedBelief m α) : StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, none⟩
    confidence := loebDiscount b.confidence }

/-- Introspect with Löb discount and description -/
def introspectWithLoebDesc (_h : m < n) (b : StratifiedBelief m α) (desc : String) :
    StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, some desc⟩
    confidence := loebDiscount b.confidence }

/-!
### Introspection Theorems
-/

/-- Basic introspection preserves confidence -/
theorem introspect_confidence (h : m < n) (b : StratifiedBelief m α) :
    (introspect h b).confidence = b.confidence := rfl

/-- Löb introspection squares confidence -/
theorem introspectWithLoeb_confidence (h : m < n) (b : StratifiedBelief m α) :
    (introspectWithLoeb h b).confidence = loebDiscount b.confidence := rfl

/-- Löb introspection reduces confidence -/
theorem introspectWithLoeb_le (h : m < n) (b : StratifiedBelief m α) :
    ((introspectWithLoeb h b).confidence : ℝ) ≤ (b.confidence : ℝ) :=
  loebDiscount_le b.confidence

/-- Level 0 cannot be introspected from (no m < 0 exists) -/
theorem level_zero_cannot_introspect_from (h : m < 0) : False :=
  Nat.not_lt_zero m h

/-- Convenient constructor for introspecting to the next level (without Löb) -/
def introspectSucc (b : StratifiedBelief n α) : StratifiedBelief (n + 1) (Meta α) :=
  introspect (Nat.lt_succ_self n) b

/-- Convenient constructor for introspecting to the next level WITH Löb discount -/
def introspectSuccWithLoeb (b : StratifiedBelief n α) : StratifiedBelief (n + 1) (Meta α) :=
  introspectWithLoeb (Nat.lt_succ_self n) b

/-!
### Anti-Bootstrapping Theorem

The combination of stratification and Löb discount prevents confidence bootstrapping.

Key insight: An agent cannot increase its confidence in X by reasoning about
its own reliability, because:
1. Reasoning about reliability requires going to a higher level
2. Going to a higher level applies the Löb discount (c → c²)
3. c² ≤ c for all c ∈ [0,1], with strict inequality for 0 < c < 1
-/

/-- Chain of k Löb discounts: c^(2^k)
    After k levels of meta-reasoning, confidence is c^(2^k) -/
def loebChain (c : Confidence) : Nat → Confidence
  | 0 => c
  | k + 1 => loebDiscount (loebChain c k)

/-- Löb chain is monotonically decreasing -/
theorem loebChain_decreasing (c : Confidence) (k : Nat) :
    (loebChain c (k + 1) : ℝ) ≤ (loebChain c k : ℝ) := by
  simp only [loebChain]
  exact loebDiscount_le (loebChain c k)

/-- Anti-bootstrapping: No finite chain of meta-reasoning can increase confidence.
    For any starting confidence c and any depth k of meta-reasoning,
    the final confidence is at most c. -/
theorem no_confidence_bootstrap (c : Confidence) (k : Nat) :
    (loebChain c k : ℝ) ≤ (c : ℝ) := by
  induction k with
  | zero => simp only [loebChain]; rfl
  | succ k ih =>
    calc (loebChain c (k + 1) : ℝ)
      _ ≤ (loebChain c k : ℝ) := loebChain_decreasing c k
      _ ≤ (c : ℝ) := ih

/-!
## Level-Preserving Operations

These operations work within a single level.
They mirror the basic Belief operations but respect stratification.
-/

/-- Map a function over the value, preserving level and confidence -/
def map (f : α → β) (b : StratifiedBelief n α) : StratifiedBelief n β :=
  ⟨f b.value, b.confidence⟩

/-- Functor identity law -/
theorem map_id (b : StratifiedBelief n α) : map id b = b := rfl

/-- Functor composition law -/
theorem map_comp (f : β → γ) (g : α → β) (b : StratifiedBelief n α) :
    map f (map g b) = map (f ∘ g) b := rfl

/-- Map preserves confidence exactly -/
theorem map_confidence (f : α → β) (b : StratifiedBelief n α) :
    (map f b).confidence = b.confidence := rfl

/-!
### Derivation (Level-Preserving)
-/

/-- Derive a new belief at the same level.
    Confidence multiplies (conjunctive derivation). -/
def derive₂ (f : α → β → γ)
    (b₁ : StratifiedBelief n α) (b₂ : StratifiedBelief n β) : StratifiedBelief n γ :=
  ⟨f b₁.value b₂.value,
   ⟨(b₁.confidence : ℝ) * (b₂.confidence : ℝ),
    mul_mem' b₁.confidence b₂.confidence⟩⟩

/-- Derivation cannot increase confidence beyond first premise -/
theorem derive₂_le_left (f : α → β → γ)
    (b₁ : StratifiedBelief n α) (b₂ : StratifiedBelief n β) :
    ((derive₂ f b₁ b₂).confidence : ℝ) ≤ (b₁.confidence : ℝ) :=
  mul_le_left b₁.confidence b₂.confidence

/-- Derivation cannot increase confidence beyond second premise -/
theorem derive₂_le_right (f : α → β → γ)
    (b₁ : StratifiedBelief n α) (b₂ : StratifiedBelief n β) :
    ((derive₂ f b₁ b₂).confidence : ℝ) ≤ (b₂.confidence : ℝ) :=
  mul_le_right b₁.confidence b₂.confidence

/-!
### Aggregation (Level-Preserving)
-/

/-- Aggregate two beliefs about the same value at the same level.
    Uses ⊕ (probabilistic OR) for confidence combination. -/
def aggregate (b₁ b₂ : StratifiedBelief n α) (combine : α → α → α) :
    StratifiedBelief n α :=
  ⟨combine b₁.value b₂.value, Confidence.oplus b₁.confidence b₂.confidence⟩

/-- Aggregation increases confidence: result ≥ first premise -/
theorem aggregate_ge_left (b₁ b₂ : StratifiedBelief n α) (combine : α → α → α) :
    (b₁.confidence : ℝ) ≤ ((aggregate b₁ b₂ combine).confidence : ℝ) := by
  simp only [aggregate]
  exact Confidence.le_oplus_left b₁.confidence b₂.confidence

/-- Aggregation increases confidence: result ≥ second premise -/
theorem aggregate_ge_right (b₁ b₂ : StratifiedBelief n α) (combine : α → α → α) :
    (b₂.confidence : ℝ) ≤ ((aggregate b₁ b₂ combine).confidence : ℝ) := by
  simp only [aggregate]
  exact Confidence.le_oplus_right b₁.confidence b₂.confidence

/-!
### Defeat (Level-Preserving)
-/

/-- Apply undercutting defeat at the same level.
    Undercut attacks the inference that produced the belief. -/
def applyUndercut (b : StratifiedBelief n α) (d : Confidence) : StratifiedBelief n α :=
  ⟨b.value, undercut b.confidence d⟩

/-- Undercut reduces confidence -/
theorem undercut_le (b : StratifiedBelief n α) (d : Confidence) :
    ((applyUndercut b d).confidence : ℝ) ≤ (b.confidence : ℝ) :=
  Confidence.undercut_le b.confidence d

/-- No undercut means no change -/
theorem undercut_zero (b : StratifiedBelief n α) :
    applyUndercut b 0 = b := by
  simp only [applyUndercut]
  congr 1
  exact Confidence.undercut_zero b.confidence

/-!
## Coercion to Basic Belief

A StratifiedBelief can be "forgotten" to a basic Belief by dropping the level.
-/

/-- Convert a stratified belief to a basic belief (forget the level) -/
def toBelief (b : StratifiedBelief n α) : Belief α :=
  ⟨b.value, b.confidence⟩

/-- Conversion preserves value -/
theorem toBelief_value (b : StratifiedBelief n α) :
    (toBelief b).value = b.value := rfl

/-- Conversion preserves confidence -/
theorem toBelief_confidence (b : StratifiedBelief n α) :
    (toBelief b).confidence = b.confidence := rfl

/-!
## Ground Level (Level 0)

Level 0 is special: it's the base of the hierarchy.
No introspection targets level 0 as source.
-/

/-- Type alias for ground-level beliefs -/
abbrev GroundBelief := StratifiedBelief 0

/- Ground beliefs cannot be the source of introspection (level 0 has no predecessors).
   Note: Ground beliefs CAN be introspected BY higher levels.
   This is captured by level_zero_cannot_introspect_from. -/

/- Section: Monadic Structure (Graded, Level-Preserving)

StratifiedBelief forms a graded monad at each level.
-/

/-- Monadic bind at the same level -/
def bind (b : StratifiedBelief n α) (f : α → StratifiedBelief n β) : StratifiedBelief n β :=
  let result := f b.value
  ⟨result.value,
   ⟨(b.confidence : ℝ) * (result.confidence : ℝ),
    mul_mem' b.confidence result.confidence⟩⟩

/-- Monadic return at any level -/
def pure (v : α) : StratifiedBelief n α := certain v

/-- Pure has full confidence -/
theorem pure_confidence (v : α) : (pure (n := n) v).confidence = 1 := rfl

/-- Left identity for confidence -/
theorem bind_pure_left_confidence (v : α) (f : α → StratifiedBelief n β) :
    ((bind (pure v) f).confidence : ℝ) = ((f v).confidence : ℝ) := by
  simp only [bind, pure, certain, Subtype.coe_mk]
  simp only [coe_one, one_mul]

/-- Right identity for confidence -/
theorem bind_pure_right_confidence (b : StratifiedBelief n α) :
    ((bind b pure).confidence : ℝ) = (b.confidence : ℝ) := by
  simp only [bind, pure, certain, Subtype.coe_mk]
  simp only [coe_one, mul_one]

end StratifiedBelief

/-!
## The Key Safety Property

The stratification system prevents paradoxical self-reference:

1. **No same-level introspection**: There is no `introspect` operation
   from level n to level n, because it would require a proof of n < n.

2. **No circular introspection**: If belief A at level n introspects
   belief B at level m < n, then B cannot (transitively) introspect A,
   because that would require n < m, contradicting m < n.

3. **Well-foundedness**: The chain of introspection terminates at level 0,
   which has no predecessors.

This captures Tarski's resolution of the Liar paradox:
"This sentence is false" cannot be formalized because the truth
predicate for level-n sentences is only defined at level n+1.
-/

/-- No natural number is less than itself -/
theorem no_self_introspection (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

/-- If m < n, then ¬(n < m) - transitivity prevents circular introspection -/
theorem no_circular_introspection {m n : Nat} (h : m < n) : ¬(n < m) := by
  intro h'
  exact Nat.lt_irrefl m (Nat.lt_trans h h')

end CLAIR
