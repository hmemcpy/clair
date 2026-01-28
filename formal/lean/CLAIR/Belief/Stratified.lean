/-
CLAIR Stratified Belief Type - Level-Indexed Beliefs

Stratified beliefs add an introspection level parameter to the basic Belief type.
This formalizes Tarski's hierarchy: level-n beliefs can only reference level-m
beliefs where m < n, preventing Liar-like paradoxes.

Design approach (Thread 8.11, Session 49):
- Phase 3 of belief formalization
- Extends Phase 1 (basic Belief) with level indexing
- Implements Layer 1 of Thread 3.19's anti-bootstrapping design
- Layer 2 (finite confidence caps) deferred to future work

Key properties:
- Level 0 is ground level (no introspection possible)
- Introspection requires proof that m < n
- Level-preserving operations: map, derive, aggregate, defeat
- Well-foundedness via Nat.lt

See: exploration/thread-8.11-stratified-belief-lean.md
     exploration/thread-3.19-type-anti-bootstrapping.md
     exploration/thread-3-self-reference.md
-/

import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut

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
  deriving Repr

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
  deriving Repr

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

/-- Introspect a lower-level belief from a higher level.
    This is the key operation enforcing Tarski's hierarchy.

    - Source: belief at level m
    - Target: belief about that belief, at level n where n > m
    - The proof h : m < n is required and checked at compile time

    This prevents Liar-like paradoxes: a belief cannot introspect itself
    because that would require m < m, which is impossible. -/
def introspect (h : m < n) (b : StratifiedBelief m α) : StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, none⟩
    confidence := b.confidence }

/-- Introspect with a description -/
def introspectWithDesc (h : m < n) (b : StratifiedBelief m α) (desc : String) :
    StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, some desc⟩
    confidence := b.confidence }

/-!
### Introspection Theorems
-/

/-- Introspection preserves confidence -/
theorem introspect_confidence (h : m < n) (b : StratifiedBelief m α) :
    (introspect h b).confidence = b.confidence := rfl

/-- Level 0 cannot be introspected from (no m < 0 exists) -/
theorem level_zero_cannot_introspect_from (h : m < 0) : False :=
  Nat.not_lt_zero m h

/-- Convenient constructor for introspecting to the next level -/
def introspectSucc (b : StratifiedBelief n α) : StratifiedBelief (n + 1) (Meta α) :=
  introspect (Nat.lt_succ_self n) b

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
  ⟨combine b₁.value b₂.value, b₁.confidence ⊕ b₂.confidence⟩

/-- Aggregation increases confidence: result ≥ first premise -/
theorem aggregate_ge_left (b₁ b₂ : StratifiedBelief n α) (combine : α → α → α) :
    (b₁.confidence : ℝ) ≤ ((aggregate b₁ b₂ combine).confidence : ℝ) :=
  le_oplus_left b₁.confidence b₂.confidence

/-- Aggregation increases confidence: result ≥ second premise -/
theorem aggregate_ge_right (b₁ b₂ : StratifiedBelief n α) (combine : α → α → α) :
    (b₂.confidence : ℝ) ≤ ((aggregate b₁ b₂ combine).confidence : ℝ) :=
  le_oplus_right b₁.confidence b₂.confidence

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

/-- Ground beliefs cannot be the source of introspection (level 0 has no predecessors).
    Note: Ground beliefs CAN be introspected BY higher levels. -/
-- This is captured by level_zero_cannot_introspect_from

/-!
## Monadic Structure (Graded, Level-Preserving)

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
  simp only [unitInterval.coe_one, one_mul]

/-- Right identity for confidence -/
theorem bind_pure_right_confidence (b : StratifiedBelief n α) :
    ((bind b pure).confidence : ℝ) = (b.confidence : ℝ) := by
  simp only [bind, pure, certain, Subtype.coe_mk]
  simp only [unitInterval.coe_one, mul_one]

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
