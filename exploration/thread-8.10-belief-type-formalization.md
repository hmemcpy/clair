# Thread 8.10: Formalize Belief Type with Confidence Component

> **Status**: Active exploration (Session 48)
> **Task**: 8.10 Formalize Belief type with confidence component in Lean 4
> **Question**: How should we formalize CLAIR's full Belief type in Lean 4, integrating confidence, provenance, justification, and invalidation?

---

## 1. The Problem

CLAIR's central abstraction is the **Belief type**. From `formal/syntax.md`:

```clair
Belief<a>               -- Belief about a value of type a

-- A Belief<Int> contains:
--   value: Int
--   confidence: Float in [0,1]
--   provenance: Provenance
--   justification: Justification
--   invalidation: Set<Condition>
```

The challenge: How do we formalize this in Lean 4 in a way that:
1. Integrates with the existing Confidence formalization
2. Captures the DAG structure of justification (Thread 2)
3. Supports stratification for self-reference safety (Thread 3)
4. Enables proofs about belief operations (type safety, confidence propagation)
5. Remains tractable for machine verification

---

## 2. Dependencies and Prior Work

### 2.1 Existing Lean 4 Infrastructure (Session 31)

The `formal/lean/` directory already contains:
- `Confidence` type as `abbrev Confidence := unitInterval`
- Four operations: multiplication (inherited), `oplus`, `undercut`, `rebut`, `min`
- Key theorems: boundedness preservation, monoid structures, composition laws

### 2.2 Theoretical Foundations

From the exploration threads:
- **Thread 1**: Confidence is epistemic commitment, not probability
- **Thread 2**: Justification is a DAG with labeled edges (support/undercut/rebut)
- **Thread 3**: Beliefs should be stratified by introspection level
- **Thread 3.19**: Type-level anti-bootstrapping via finite confidence caps

### 2.3 Design Requirements from derivation-calculus.md

A belief `b = ⟨v, c, p, j, I⟩` has:
- `v`: The value being believed
- `c`: Confidence in [0,1]
- `p`: Provenance (derived from inputs + rule)
- `j`: Justification (DAG node)
- `I`: Invalidation conditions (set of conditions)

---

## 3. Design Options Analysis

### Option A: Monolithic Structure

```lean4
structure Belief (α : Type*) where
  value : α
  confidence : Confidence
  provenance : Provenance
  justification : JustificationId
  invalidation : Set InvalidationCondition
```

**Advantages**:
- Simple, direct translation from syntax specification
- Easy to understand and use

**Disadvantages**:
- Doesn't capture stratification
- No type-level confidence bounds
- Provenance and justification need separate definitions

### Option B: Indexed by Introspection Level

```lean4
structure Belief (n : ℕ) (α : Type*) where
  value : α
  confidence : Confidence
  provenance : Provenance n
  justification : JustificationGraph n
  invalidation : Set (InvalidationCondition n)
```

**Advantages**:
- Captures stratification at the type level
- Level-n beliefs can only reference level-(m<n) beliefs
- Aligns with Thread 3's design

**Disadvantages**:
- More complex type signatures
- Need level-indexed provenance and justification

### Option C: Indexed by Level and Confidence Cap (Full Thread 3.19)

```lean4
structure Belief (n : ℕ) (cap : FiniteConf) (α : Type*) where
  value : α
  confidence : { c : Confidence // c ≤ cap }
  provenance : Provenance n
  justification : JustificationGraph n
  invalidation : Set (InvalidationCondition n)
```

**Advantages**:
- Full type-level anti-bootstrapping
- Decidable confidence propagation checks
- Most complete formalization

**Disadvantages**:
- Most complex
- Finite confidence may be overly restrictive
- Heavy type annotations

### Option D: Minimal Core + Extensions

Start with a minimal core type, then add extensions:

```lean4
-- Core: just value + confidence
structure BeliefCore (α : Type*) where
  value : α
  confidence : Confidence

-- Extended: add justification
structure BeliefWithJust (α : Type*) extends BeliefCore α where
  justification : JustificationId

-- Full: add provenance and invalidation
structure Belief (α : Type*) extends BeliefWithJust α where
  provenance : Provenance
  invalidation : Set InvalidationCondition

-- Stratified version
structure StratifiedBelief (n : ℕ) (α : Type*) extends Belief α where
  level_valid : n > 0  -- level constraint
```

**Advantages**:
- Incremental complexity
- Can prove properties at each level
- Flexible for different use cases

**Disadvantages**:
- More types to maintain
- Inheritance may not work well in Lean 4

---

## 4. Component Analysis

### 4.1 Justification Structure

From Thread 2, justification is a DAG with labeled edges. In Lean 4:

```lean4
/-- Unique identifier for a justification node -/
def JustificationId := ℕ

/-- Edge types in the justification DAG -/
inductive EdgeType where
  | support : EdgeType     -- positive evidential contribution
  | undercut : EdgeType    -- attacks the justification link
  | rebut : EdgeType       -- attacks the conclusion directly

/-- A labeled edge to a justification node -/
structure JustificationEdge where
  target : JustificationId
  edgeType : EdgeType

/-- A node in the justification graph -/
inductive JustificationNode where
  | axiom : JustificationNode
  | assumption : String → JustificationNode  -- assumption name
  | rule : String → List JustificationEdge → JustificationNode
  | choice : List String → String → JustificationNode  -- options, reason
  | abduction : String → JustificationNode  -- observation
  | analogy : JustificationId → String → JustificationNode  -- source, similarity
  | induction : List JustificationId → JustificationNode  -- instances
  | aggregate : List JustificationEdge → JustificationNode  -- combined evidence

/-- The justification graph -/
structure JustificationGraph where
  nodes : JustificationId → Option JustificationNode
  root : JustificationId
  -- Acyclicity would require a well-foundedness proof
```

**Challenge**: Proving acyclicity is non-trivial. Options:
1. Use an inductive type that's acyclic by construction
2. Carry an acyclicity proof as a field
3. Use quotient types over raw graphs

### 4.2 Provenance

Provenance tracks how a belief was derived:

```lean4
inductive ProvenanceType where
  | literal : ProvenanceType         -- direct value
  | input : String → ProvenanceType  -- external input source
  | derived : ProvenanceType         -- derived from other beliefs

structure Provenance where
  provenanceType : ProvenanceType
  sources : List JustificationId     -- what this depends on
  rule : Option String               -- derivation rule if any
  timestamp : Option ℕ               -- optional temporal info
```

### 4.3 Invalidation Conditions

```lean4
inductive InvalidationCondition where
  | sourceChanged : String → InvalidationCondition
  | beliefInvalidated : JustificationId → InvalidationCondition
  | timeExpired : ℕ → InvalidationCondition
  | conditionFailed : String → InvalidationCondition
```

### 4.4 Stratification Level

For safe self-reference (Thread 3):

```lean4
/-- Stratification level for beliefs.
    Level-n beliefs can only introspect level-(m<n) beliefs. -/
abbrev Level := ℕ

/-- A stratified belief type -/
structure StratifiedBelief (n : Level) (α : Type*) where
  value : α
  confidence : Confidence
  justification : JustificationId
  -- Invariant: all referenced beliefs have level < n
```

---

## 5. Recommended Approach: Incremental Formalization

Given the complexity and the goal of machine-checked proofs, I recommend an **incremental approach**:

### Phase 1: Core Belief Type (This Session)

Define the minimal Belief type with just value and confidence:

```lean4
/-- Core belief type: a value with associated confidence -/
structure Belief (α : Type*) where
  value : α
  confidence : Confidence
  deriving Repr
```

This allows us to:
- Prove basic operations preserve confidence bounds
- Establish the graded monad structure
- Test the formalization approach

### Phase 2: Add Justification (Future Task)

```lean4
/-- Belief with explicit justification -/
structure JustifiedBelief (α : Type*) extends Belief α where
  justification : JustificationId
```

### Phase 3: Add Stratification (Future Task 8.11)

```lean4
/-- Stratified belief type -/
structure StratifiedBelief (n : ℕ) (α : Type*) extends JustifiedBelief α where
  -- invariant that referenced beliefs have lower level
```

### Phase 4: Full Belief Type

```lean4
/-- Complete CLAIR belief -/
structure FullBelief (n : ℕ) (α : Type*) extends StratifiedBelief n α where
  provenance : Provenance
  invalidation : Set InvalidationCondition
```

---

## 6. Phase 1 Implementation

### 6.1 Core Definitions

```lean4
/-!
# CLAIR Belief Type - Core Definitions

The Belief type is CLAIR's central abstraction: a value paired with
epistemic metadata (confidence, provenance, justification, invalidation).

This module defines the core Belief<α> type with just value and confidence,
laying the foundation for more complete versions.
-/

import CLAIR.Confidence.Basic
import CLAIR.Confidence.Oplus
import CLAIR.Confidence.Undercut

namespace CLAIR

/-- A belief is a value paired with confidence in that value.
    This is the minimal core; full beliefs add justification, provenance,
    and invalidation conditions. -/
structure Belief (α : Type*) where
  value : α
  confidence : Confidence
  deriving Repr

namespace Belief

variable {α β γ : Type*}

/-! ## Basic Operations -/

/-- Extract the value from a belief -/
def getValue (b : Belief α) : α := b.value

/-- Extract the confidence from a belief -/
def getConfidence (b : Belief α) : Confidence := b.confidence

/-- Create a belief with full confidence (1.0).
    Note: CLAIR discourages confidence 1.0 due to fallibilism. -/
def certain (v : α) : Belief α := ⟨v, 1⟩

/-- Create a belief with zero confidence.
    Represents complete lack of commitment. -/
def uncertain (v : α) : Belief α := ⟨v, 0⟩

/-- Create a belief with specified confidence -/
def withConfidence (v : α) (c : Confidence) : Belief α := ⟨v, c⟩

/-! ## Functorial Structure -/

/-- Map a function over the value, preserving confidence -/
def map (f : α → β) (b : Belief α) : Belief β :=
  ⟨f b.value, b.confidence⟩

theorem map_id (b : Belief α) : map id b = b := rfl

theorem map_comp (f : β → γ) (g : α → β) (b : Belief α) :
    map f (map g b) = map (f ∘ g) b := rfl

/-! ## Derivation: Combining Beliefs -/

/-- Derive a new belief by applying a function to two beliefs.
    Confidence is multiplied (conjunctive derivation). -/
def derive₂ (f : α → β → γ) (b₁ : Belief α) (b₂ : Belief β) : Belief γ :=
  ⟨f b₁.value b₂.value,
   ⟨(b₁.confidence : ℝ) * (b₂.confidence : ℝ),
    Confidence.mul_mem' b₁.confidence b₂.confidence⟩⟩

/-- Derive using a rule with explicit confidence factor -/
def deriveWithStrength (f : α → β → γ) (s : Confidence)
    (b₁ : Belief α) (b₂ : Belief β) : Belief γ :=
  ⟨f b₁.value b₂.value,
   ⟨s * (b₁.confidence : ℝ) * (b₂.confidence : ℝ),
    by
      have h1 := Confidence.mul_mem' s b₁.confidence
      have h2 := Confidence.mul_mem' ⟨_, h1⟩ b₂.confidence
      exact h2⟩⟩

/-! ## Aggregation: Combining Independent Evidence -/

/-- Aggregate two beliefs about the same value with independent evidence.
    Uses ⊕ (probabilistic OR) for confidence combination. -/
def aggregate (b₁ b₂ : Belief α) (combine : α → α → α) : Belief α :=
  ⟨combine b₁.value b₂.value,
   b₁.confidence ⊕ b₂.confidence⟩

/-- Aggregate two beliefs with equal values (confidence only) -/
def aggregateEq (b₁ b₂ : Belief α) (h : b₁.value = b₂.value) : Belief α :=
  ⟨b₁.value, b₁.confidence ⊕ b₂.confidence⟩

/-! ## Defeat Operations -/

/-- Apply undercutting defeat to a belief -/
def applyUndercut (b : Belief α) (d : Confidence) : Belief α :=
  ⟨b.value, Confidence.undercut b.confidence d⟩

/-- Apply rebutting defeat -/
def applyRebut (b_for b_against : Belief α) (resolve : α → α → α) : Belief α :=
  ⟨resolve b_for.value b_against.value,
   Confidence.rebut b_for.confidence b_against.confidence⟩

/-! ## Monadic Structure (Graded) -/

/-- Monadic bind for beliefs: derive using a belief-producing function.
    Confidence multiplies (the monad is graded over ([0,1], ×, 1)). -/
def bind (b : Belief α) (f : α → Belief β) : Belief β :=
  let result := f b.value
  ⟨result.value,
   ⟨(b.confidence : ℝ) * (result.confidence : ℝ),
    Confidence.mul_mem' b.confidence result.confidence⟩⟩

/-- Monadic return: create a belief with full confidence -/
def pure (v : α) : Belief α := certain v

-- Note: Monad laws hold up to provenance equivalence (see Thread 1)

end Belief

end CLAIR
```

### 6.2 Key Theorems to Prove

1. **Derivation preserves bounds**:
   ```lean4
   theorem derive_confidence_bounded (b₁ : Belief α) (b₂ : Belief β) (f : α → β → γ) :
       let result := Belief.derive₂ f b₁ b₂
       0 ≤ (result.confidence : ℝ) ∧ (result.confidence : ℝ) ≤ 1
   ```

2. **Derivation can only decrease confidence**:
   ```lean4
   theorem derive_confidence_le (b₁ : Belief α) (b₂ : Belief β) (f : α → β → γ) :
       let result := Belief.derive₂ f b₁ b₂
       (result.confidence : ℝ) ≤ (b₁.confidence : ℝ) ∧
       (result.confidence : ℝ) ≤ (b₂.confidence : ℝ)
   ```

3. **Aggregation increases confidence**:
   ```lean4
   theorem aggregate_confidence_ge (b₁ b₂ : Belief α) (combine : α → α → α) :
       let result := Belief.aggregate b₁ b₂ combine
       (b₁.confidence : ℝ) ≤ (result.confidence : ℝ) ∧
       (b₂.confidence : ℝ) ≤ (result.confidence : ℝ)
   ```

4. **Undercut reduces confidence**:
   ```lean4
   theorem undercut_confidence_le (b : Belief α) (d : Confidence) :
       let result := Belief.applyUndercut b d
       (result.confidence : ℝ) ≤ (b.confidence : ℝ)
   ```

5. **Functor laws**:
   ```lean4
   theorem map_id (b : Belief α) : Belief.map id b = b
   theorem map_comp (f : β → γ) (g : α → β) (b : Belief α) :
       Belief.map f (Belief.map g b) = Belief.map (f ∘ g) b
   ```

6. **Monad-like properties** (up to provenance equivalence):
   ```lean4
   theorem bind_pure_left (v : α) (f : α → Belief β) :
       Belief.bind (Belief.pure v) f = f v  -- if f v has confidence 1

   theorem bind_pure_right (b : Belief α) :
       Belief.bind b Belief.pure = b  -- confidence multiplies by 1
   ```

---

## 7. Findings and Recommendations

### 7.1 Key Insight: Confidence Bounds Are Preserved by Construction

The existing Confidence formalization already proves that all operations preserve [0,1] bounds. The Belief type simply carries Confidence values, so boundedness is inherited.

### 7.2 The Graded Monad Structure

From Thread 1: Belief forms a **graded monad** over `([0,1], ×, 1)`:
- Return (pure) has grade 1
- Bind composes grades multiplicatively

The monad laws hold **up to provenance equivalence**, not strict equality. This should be documented but doesn't prevent useful formalizations.

### 7.3 Stratification Deferred

Full stratification (Task 8.11) requires:
- Level-indexed types
- Well-foundedness proofs for the justification graph
- Type-level introspection constraints

This is substantial additional work and should be a separate task.

### 7.4 Justification Graph Complexity

Formalizing the full justification DAG with labeled edges and acyclicity is complex. Options:
1. Use an inductive representation (acyclic by construction)
2. Use a graph with explicit acyclicity proof (more flexible but harder)
3. Defer full justification to a later phase

For Phase 1, we defer justification graph formalization.

---

## 8. Implementation Status

**Completed in this exploration**:
- Design analysis of four options
- Component breakdown (justification, provenance, invalidation)
- Incremental approach recommended
- Phase 1 Lean 4 code designed (core Belief type)
- Key theorems identified

**To be implemented**:
- Create `CLAIR/Belief/Basic.lean` with Phase 1 definitions
- Prove the key theorems
- Connect to existing Confidence infrastructure

**Deferred to future tasks**:
- Task 8.11: Stratified belief levels
- Justification graph formalization
- Full provenance tracking
- Invalidation condition handling

---

## 9. Confidence Assessment

- Phase 1 design is sound: 0.90
- Core theorems are provable: 0.85
- Incremental approach will succeed: 0.80
- Full Belief type (all four phases) achievable: 0.70
- Justification DAG formalization is complex: 0.85

---

## 10. Next Steps

1. **Create `formal/lean/CLAIR/Belief/Basic.lean`** with Phase 1 definitions
2. **Prove key theorems** about derivation, aggregation, and defeat
3. **Mark Task 8.10 as substantially complete** for Phase 1
4. **Create follow-up tasks** for Phases 2-4

---

## 11. Prior Art Surveyed

- **Mathlib's unitInterval**: Provides exactly the Confidence type infrastructure needed
- **Dependent type systems (Coq, Agda)**: Indexed types for stratification
- **Graded monads (Orchard et al. 2019)**: Theoretical foundation for belief composition
- **Refinement types (Liquid Haskell)**: Predicates on types for confidence bounds
- **Information flow types (JFlow)**: Lattice-based constraint propagation

The CLAIR Belief type is a novel synthesis: values with epistemic metadata, supporting graded composition, defeat, and aggregation—formalized in a proof assistant.
