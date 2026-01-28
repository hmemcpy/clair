# Thread 8: Formal Verification - Confidence Type in Lean 4

> **Status**: Active exploration (Session 10)
> **Task**: 8.5 Define Confidence type as subtype of Real with [0,1] bounds
> **Question**: How should we formalize CLAIR's Confidence type in Lean 4?

---

## 1. The Problem

CLAIR's confidence is described as:
- A value in the closed interval [0,1]
- Semantically representing "epistemic commitment" (not probability)
- With operations: multiplication (×), min, and "probabilistic or" (⊕)
- Forming algebraic structures: commutative monoid under ×, semiring with ⊕ and ×

The challenge: How do we formalize this in Lean 4 in a way that:
1. Enforces the [0,1] bounds at the type level
2. Proves key properties (boundedness preservation, associativity, etc.)
3. Supports practical computation
4. Connects to the larger CLAIR formalization

---

## 2. Prior Art Survey

### 2.1 Lean 4's Real Numbers

Lean 4 (via Mathlib) provides:
- `ℝ` (Real): The standard real number type
- `Set.Icc 0 1`: The closed interval [0,1] as a set
- `Subtype`: For creating subtypes with predicates

**Key question**: Should Confidence be a subtype of ℝ, or a separate inductive type?

### 2.2 Probability Measures in Mathlib

Mathlib has extensive probability theory:
- `MeasureTheory.ProbabilityMeasure`: For probability spaces
- Probability values are typically unbounded ℝ≥0∞

However, CLAIR confidence is NOT probability. The key differences:
- No normalization requirement (P + ¬P need not equal 1)
- Paraconsistent (can believe both P and ¬P with non-zero confidence)
- Different interpretation (epistemic commitment, not frequency/degree of belief)

### 2.3 Subjective Logic Formalizations

Jøsang's Subjective Logic has been formalized in various systems:
- Some Coq formalizations exist (though not comprehensive)
- Uses (b, d, u, a) tuples instead of single values

CLAIR currently uses a simpler single-value confidence, but the implementation plan notes this as an open question (Task 1.6).

### 2.4 Fuzzy Logic Type Systems

Fuzzy logic uses truth values in [0,1]:
- Some Lean formalizations of fuzzy sets exist
- MV-algebras (many-valued logic) provide algebraic structure

This is closer to CLAIR's needs than probability theory.

---

## 3. Design Options

### Option A: Subtype of Real

```lean4
def Confidence := { c : ℝ // 0 ≤ c ∧ c ≤ 1 }

-- Or using Mathlib's Set.Icc:
def Confidence := Set.Icc (0 : ℝ) 1
```

**Advantages:**
- Leverages Mathlib's extensive real number library
- Inherits all real number properties
- Clean mathematical semantics

**Disadvantages:**
- Reals are computationally expensive (Cauchy sequences)
- May include more structure than needed
- Dependent on large Mathlib import

### Option B: Subtype of Rational

```lean4
def Confidence := { c : ℚ // 0 ≤ c ∧ c ≤ 1 }
```

**Advantages:**
- Computationally efficient (exact arithmetic)
- Sufficient for most practical purposes
- Smaller dependency footprint

**Disadvantages:**
- Limits not definable (no completeness)
- Some mathematical operations need extension to ℝ

### Option C: Fixed-Point Representation

```lean4
-- Confidence as a natural number 0..100 (percent)
def Confidence := Fin 101

-- Or with more precision:
def Confidence := Fin 10001  -- 0.00 to 100.00
```

**Advantages:**
- Maximally efficient computation
- Decidable equality
- No precision issues

**Disadvantages:**
- Loses continuous nature
- Multiplication introduces rounding
- Less mathematically elegant

### Option D: Abstract Algebraic Approach

```lean4
-- Define confidence by its algebraic properties
class ConfidenceAlgebra (C : Type) where
  zero : C
  one : C
  mul : C → C → C
  oplus : C → C → C
  le : C → C → Prop
  -- axioms
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ a, mul a one = a
  -- ... more axioms
```

**Advantages:**
- Captures exactly what we need
- Can instantiate with different representations
- Clean separation of interface and implementation

**Disadvantages:**
- More complex to set up
- Need to prove instance satisfies axioms
- May miss some real number properties we need

---

## 4. Recommended Approach: Layered Design

After considering the options, I propose a **layered design**:

### Layer 1: Abstract Confidence Algebra

Define the algebraic structure confidence must satisfy:

```lean4
/-- A confidence semiring over a type C -/
class ConfidenceSemiring (C : Type*) extends Zero C, One C, Add C, Mul C where
  -- Additive structure (⊕ operation)
  add_assoc : ∀ a b c : C, a + b + c = a + (b + c)
  add_comm : ∀ a b : C, a + b = b + a
  zero_add : ∀ a : C, 0 + a = a

  -- Multiplicative structure (× operation)
  mul_assoc : ∀ a b c : C, a * b * c = a * (b * c)
  mul_comm : ∀ a b : C, a * b = b * a
  one_mul : ∀ a : C, 1 * a = a
  mul_one : ∀ a : C, a * 1 = a

  -- Distributivity
  mul_add : ∀ a b c : C, a * (b + c) = a * b + a * c

  -- Annihilation
  zero_mul : ∀ a : C, 0 * a = 0

  -- Bounds (confidence-specific)
  bounded : ∀ a : C, 0 ≤ a ∧ a ≤ 1

  -- Note: standard + is probabilistic OR, so a + b = a + b - a*b
  -- We'll need a different operator or adjust
```

Wait—there's a tension here. The "probabilistic or" ⊕ is defined as:
```
a ⊕ b = a + b - a*b
```

This is NOT the standard addition. Let me reconsider.

### Revised Layer 1: Confidence-Specific Algebra

```lean4
/-- Confidence forms a commutative monoid under multiplication -/
class ConfidenceMonoid (C : Type*) extends One C, Mul C, LE C where
  mul_assoc : ∀ a b c : C, a * b * c = a * (b * c)
  mul_comm : ∀ a b : C, a * b = b * a
  one_mul : ∀ a : C, 1 * a = a
  mul_one : ∀ a : C, a * 1 = a

  -- Bounds
  zero_le : ∀ a : C, (0 : ℕ) ≤ a  -- need to express 0
  le_one : ∀ a : C, a ≤ 1

/-- Extended with probabilistic OR for aggregation -/
class ConfidenceOr (C : Type*) extends ConfidenceMonoid C where
  oplus : C → C → C
  oplus_comm : ∀ a b : C, oplus a b = oplus b a
  oplus_assoc : ∀ a b c : C, oplus (oplus a b) c = oplus a (oplus b c)
  -- oplus_def : oplus a b = a + b - a * b  (if we have subtraction)
```

### Layer 2: Concrete Representation

```lean4
/-- Confidence as a subtype of Real in [0,1] -/
def Confidence := { c : ℝ // 0 ≤ c ∧ c ≤ 1 }

namespace Confidence

instance : Zero Confidence := ⟨⟨0, by norm_num, by norm_num⟩⟩
instance : One Confidence := ⟨⟨1, by norm_num, by norm_num⟩⟩

instance : Mul Confidence where
  mul a b := ⟨a.val * b.val, by
    constructor
    · exact mul_nonneg a.property.1 b.property.1
    · calc a.val * b.val
        ≤ a.val * 1 := mul_le_mul_of_nonneg_left b.property.2 a.property.1
        _ = a.val := mul_one a.val
        _ ≤ 1 := a.property.2⟩

-- The probabilistic OR
def oplus (a b : Confidence) : Confidence :=
  ⟨a.val + b.val - a.val * b.val, by
    constructor
    · -- 0 ≤ a + b - ab
      -- a + b - ab = a(1-b) + b ≥ 0 since a,b,(1-b) ≥ 0
      have h1 : 0 ≤ 1 - b.val := by linarith [b.property.2]
      have h2 : 0 ≤ a.val * (1 - b.val) := mul_nonneg a.property.1 h1
      linarith [b.property.1]
    · -- a + b - ab ≤ 1
      -- a + b - ab = a + b(1-a) ≤ 1 + 1*1 - 1 = 1 when a,b ≤ 1
      have h1 : b.val * (1 - a.val) ≤ 1 * 1 := by
        apply mul_le_mul b.property.2
        · linarith [a.property.1]
        · linarith [a.property.1]
        · norm_num
      have h2 : a.val + b.val * (1 - a.val) ≤ 1 + 1 - 1 := by linarith [a.property.2, h1]
      ring_nf at h2 ⊢
      linarith⟩

end Confidence
```

### Layer 3: Key Theorems

```lean4
namespace Confidence

/-- Multiplication preserves bounds -/
theorem mul_bounded (a b : Confidence) :
    0 ≤ (a * b).val ∧ (a * b).val ≤ 1 := (a * b).property

/-- Multiplication is associative -/
theorem mul_assoc (a b c : Confidence) : a * b * c = a * (b * c) := by
  apply Subtype.ext
  simp only [Mul.mul]
  ring

/-- Multiplication is commutative -/
theorem mul_comm (a b : Confidence) : a * b = b * a := by
  apply Subtype.ext
  simp only [Mul.mul]
  ring

/-- 1 is the multiplicative identity -/
theorem one_mul (a : Confidence) : 1 * a = a := by
  apply Subtype.ext
  simp only [Mul.mul, One.one]
  ring

/-- 0 absorbs under multiplication -/
theorem zero_mul (a : Confidence) : 0 * a = 0 := by
  apply Subtype.ext
  simp only [Mul.mul, Zero.zero]
  ring

/-- Derivation can only decrease confidence -/
theorem derive_monotonic (a b : Confidence) : (a * b).val ≤ min a.val b.val := by
  simp only [Mul.mul]
  constructor <;> nlinarith [a.property.1, a.property.2, b.property.1, b.property.2]

end Confidence
```

---

## 5. Critical Analysis

### 5.1 What This Formalization Captures

✓ **Boundedness**: Confidence is provably in [0,1]
✓ **Closure**: Operations preserve bounds
✓ **Algebraic structure**: Commutative monoid under ×
✓ **Monotonicity**: Derivation decreases confidence
✓ **Extremal values**: 0 and 1 are valid confidence values

### 5.2 What This Formalization Doesn't Capture

**Epistemic semantics**: The formalization treats confidence as a number, not as "epistemic commitment." The distinction from probability is not captured in the type—only in our interpretation.

**Relationship to beliefs**: This is just the confidence type. The full `Belief<A>` type needs:
- A value of type A
- A Confidence value
- Provenance (DAG of derivation history)
- Justification (DAG with labeled edges, per Thread 2)
- Invalidation conditions (set of conditions)

**Graded monad structure**: The categorical semantics (Belief as graded monad over Confidence monoid) is a separate theorem to prove.

**Non-independent derivations**: The simple multiplication rule fails when premises are correlated. We'd need:
- Different combination rules (min, weighted, custom)
- Dependency tracking

### 5.3 Open Questions

1. **Should we use Mathlib?**
   - Pro: Mature library, many theorems already proven
   - Con: Large dependency, may import more than needed
   - Recommendation: Yes, use Mathlib for the ℝ foundation

2. **Fixed-point vs real?**
   - For verification: Use ℝ (cleaner mathematics)
   - For implementation: Can extract to fixed-point or float
   - Recommendation: ℝ for formalization, note implementation can differ

3. **How to handle 0.5 as "maximal uncertainty"?**
   - This is a semantic property, not a type property
   - Could define: `def maxUncertainty : Confidence := ⟨0.5, ...⟩`
   - Or use dependent types: `UncertainConfidence := { c : Confidence // c.val ≠ 0 ∧ c.val ≠ 1 }`

4. **Alternative monoids (min instead of ×)?**
   - Could parameterize: `ConfidenceMonoid (op : Confidence → Confidence → Confidence)`
   - Or define separate types: `Confidence_mul`, `Confidence_min`
   - Recommendation: Define both, prove they're both valid

---

## 6. Relationship to Thread 2 (Justification DAGs)

Thread 2 established that justification requires DAGs with labeled edges. This affects confidence:

1. **Shared premises**: When the same belief supports multiple conclusions, its confidence shouldn't be "used up" (unlike linear resources). Need hash-consing or reference semantics.

2. **Defeat edges**: Undercut and rebut edges affect confidence differently than support edges:
   - Support: confidence propagates via ×
   - Undercut: confidence decreases (but how much?)
   - Rebut: competing confidence levels

3. **Aggregation**: When multiple independent lines of evidence support a conclusion:
   - Not × (that would decrease confidence)
   - Use ⊕ (probabilistic OR) or something else?
   - Need to distinguish independent vs correlated evidence

**Implication for formalization**: The Confidence type is just the carrier. The combination rules are parameterized by justification structure.

---

## 7. Relationship to Thread 3 (Self-Reference)

Thread 3 established stratified beliefs: `Belief<n, A>` where level n can only reference level m < n.

**Implication for formalization**: Confidence doesn't directly involve self-reference, but the full Belief type does. We might need:

```lean4
-- Stratified belief with level index
def Belief (n : ℕ) (A : Type u) : Type u :=
  { val : A
    conf : Confidence
    prov : Provenance n
    just : Justification n
    inv : Invalidation }

-- Provenance can only reference lower-level beliefs
inductive Provenance : ℕ → Type u
  | literal : Provenance 0
  | derived : ∀ {m : ℕ}, m < n → Provenance m → Provenance m → Provenance n
```

This is more complex and should be a separate formalization task.

---

## 8. Formalization Plan

Based on this exploration, I propose the following plan for Thread 8:

### Phase 1: Confidence Type (This exploration)
- [x] Design Confidence type
- [x] Identify key properties to prove
- [ ] Write actual Lean 4 code (deferred—this is exploration, not implementation)
- [ ] Prove boundedness preservation
- [ ] Prove monoid laws

### Phase 2: Confidence Operations
- [ ] Define min-based combination
- [ ] Define ⊕ (probabilistic OR)
- [ ] Prove both form valid monoids
- [ ] Prove semiring laws for (⊕, ×)

### Phase 3: Connection to Belief
- [ ] Define Belief type with Confidence component
- [ ] Prove confidence propagation in derivation
- [ ] Connect to graded monad structure

### Phase 4: Advanced Properties
- [ ] Stratification (from Thread 3)
- [ ] DAG justification (from Thread 2)
- [ ] Defeat and aggregation confidence rules

---

## 9. Key Insights from This Exploration

### Insight 1: Confidence is mathematically simple, semantically rich

The [0,1] interval with multiplication is just a monoid. The interesting parts are:
- The interpretation as "epistemic commitment"
- The different combination rules for different contexts
- The connection to justification structure

### Insight 2: Layered design is appropriate

Separating the abstract algebra from concrete representation allows:
- Multiple implementations (ℝ for proofs, fixed-point for execution)
- Clear axiomatization of what confidence must satisfy
- Flexibility for extensions (Subjective Logic, etc.)

### Insight 3: Thread interdependence is deep

Threads 1, 2, 3 are foundational and interconnected:
- Confidence (Thread 1) is the carrier
- Justification DAGs (Thread 2) determine how confidence combines
- Self-reference (Thread 3) affects what beliefs about confidence are safe

The formalization must proceed incrementally, respecting these dependencies.

### Insight 4: Lean 4 + Mathlib is the right choice

For the formal verification of CLAIR:
- Lean 4 has good tooling and is actively developed
- Mathlib provides ℝ and algebraic structures we need
- Extraction to executable code is possible
- The community is growing

---

## 10. What I Don't Know

### Empirical unknowns

1. **Calibration**: Is Claude's confidence actually calibrated? This requires external study.

2. **Rule selection**: When should × vs min vs ⊕ be used? This may require empirical investigation.

### Theoretical unknowns

1. **Defeat confidence**: How exactly does undercut defeat reduce confidence? The literature offers multiple models (discounting, probability kinematics, ranking theory).

2. **Correlated evidence**: How to detect and handle correlated premises? This connects to causal inference.

3. **Optimal representation**: Is [0,1] the right interval? Subjective Logic uses (b,d,u,a) tuples. Which is better for CLAIR?

### Implementation unknowns

1. **Extraction**: How cleanly does Lean 4 extract to executable code?

2. **Performance**: What's the overhead of dependent types at runtime?

3. **Integration**: How would a CLAIR interpreter use the Lean formalization?

---

## 11. Conclusion

The Confidence type formalization is **tractable and well-defined**. The core type is:

```lean4
def Confidence := { c : ℝ // 0 ≤ c ∧ c ≤ 1 }
```

With key operations:
- Multiplication: `a * b` (for derivation)
- Minimum: `min a b` (for conservative combination)
- Probabilistic OR: `a ⊕ b = a + b - a*b` (for aggregation)

And key properties to prove:
- Boundedness preservation
- Monoid laws for × and min
- Semiring laws for (⊕, ×)
- Monotonicity (derivation decreases confidence)

This exploration is **complete for Task 8.5**. The next steps are:
- Task 8.6: Implement the confidence combination operations
- Task 8.7: Prove boundedness preservation for each operation

The actual Lean 4 code should be written when we're ready to create `formal/lean/` directory structure.

---

## 12. Task 8.6: Confidence Combination Operations

> **Status**: Active exploration (Session 11)
> **Task**: 8.6 Define confidence combination operations (×, min, ⊕)
> **Question**: How do we formalize the three confidence combination operations in Lean 4, and what algebraic structures do they form?

---

### 12.1 The Three Operations

CLAIR uses three distinct operations for combining confidence values:

| Operation | Symbol | Formula | Algebraic Structure | Use Case |
|-----------|--------|---------|---------------------|----------|
| Multiplication | × | a × b | Commutative monoid | Derivation (conjunctive) |
| Minimum | min | min(a, b) | Commutative idempotent monoid | Conservative combination |
| Probabilistic OR | ⊕ | a + b - a×b | Commutative monoid | Aggregation (disjunctive) |

Each operation has distinct algebraic properties and semantic meaning.

---

### 12.2 Prior Art: T-norms and T-conorms

In fuzzy logic, these operations are well-studied:

**T-norms** (triangular norms) are binary operations on [0,1] satisfying:
- Commutativity: T(a, b) = T(b, a)
- Associativity: T(T(a, b), c) = T(a, T(b, c))
- Monotonicity: a ≤ a' ⟹ T(a, b) ≤ T(a', b)
- Identity: T(a, 1) = a

**Standard t-norms:**
- **Product t-norm (Tp)**: Tp(a, b) = a × b — This is CLAIR's ×
- **Minimum t-norm (TM)**: TM(a, b) = min(a, b) — This is CLAIR's min (also called Gödel t-norm)
- **Łukasiewicz t-norm (TL)**: TL(a, b) = max(0, a + b - 1) — Not used in CLAIR

**T-conorms** (s-norms) are the dual, with identity 0:
- **Algebraic sum (Sp)**: Sp(a, b) = a + b - a×b — This is CLAIR's ⊕
- **Maximum (SM)**: SM(a, b) = max(a, b)
- **Łukasiewicz s-norm (SL)**: SL(a, b) = min(1, a + b)

**Key insight**: CLAIR's confidence operations are instances of the product t-norm/t-conorm pair, with min as an alternative t-norm for conservative reasoning.

**References:**
- Klement, Mesiar, Pap (2000), *Triangular Norms*
- Hájek (1998), *Metamathematics of Fuzzy Logic*
- Jøsang (2016), *Subjective Logic* (for confidence in uncertainty quantification)

---

### 12.3 Algebraic Structure Analysis

#### 12.3.1 Multiplication (×)

**Type**: `mul : Confidence → Confidence → Confidence`

**Definition**: `mul a b = a.val × b.val` (standard real multiplication)

**Algebraic Properties**:

```
Commutativity:   a × b = b × a
Associativity:   (a × b) × c = a × (b × c)
Identity:        1 × a = a × 1 = a
Absorption:      0 × a = a × 0 = 0
```

**Structure**: ([0,1], ×, 1) is a **commutative monoid with absorbing element**.

**Boundedness preservation**:
```
Theorem: ∀ a b : Confidence, 0 ≤ (a × b).val ∧ (a × b).val ≤ 1

Proof:
  0 ≤ (a × b).val:
    a.val ≥ 0, b.val ≥ 0 ⟹ a.val × b.val ≥ 0  ✓

  (a × b).val ≤ 1:
    a.val ≤ 1, b.val ≤ 1
    ⟹ a.val × b.val ≤ a.val × 1 = a.val ≤ 1  ✓
    (or: a × b ≤ min(a, b) ≤ 1)
```

**Monotonicity**:
```
Theorem: a ≤ a' ⟹ a × b ≤ a' × b
Proof: b ≥ 0, so multiplication preserves order.  ✓
```

**Semantic interpretation**: Confidence multiplication models conjunctive dependence—the conclusion's confidence is the product of the premises' confidences, assuming independence.

---

#### 12.3.2 Minimum (min)

**Type**: `min : Confidence → Confidence → Confidence`

**Definition**: `min a b = if a.val ≤ b.val then a else b`

**Algebraic Properties**:

```
Commutativity:   min(a, b) = min(b, a)
Associativity:   min(min(a, b), c) = min(a, min(b, c))
Identity:        min(1, a) = min(a, 1) = a
Idempotence:     min(a, a) = a
Absorption:      min(0, a) = min(a, 0) = 0
```

**Structure**: ([0,1], min, 1) is a **bounded meet-semilattice** (commutative idempotent monoid).

**Boundedness preservation**:
```
Theorem: ∀ a b : Confidence, 0 ≤ min(a, b).val ∧ min(a, b).val ≤ 1

Proof:
  min(a, b).val is either a.val or b.val, both in [0,1].  ✓
```

**Monotonicity**:
```
Theorem: a ≤ a' ⟹ min(a, b) ≤ min(a', b)
Proof: Immediate from definition of min.  ✓
```

**Ordering property**:
```
min(a, b) ≤ a  and  min(a, b) ≤ b
```

**Semantic interpretation**: Conservative combination—the conclusion is no more confident than the least confident premise. Used when we want to be pessimistic about confidence.

**Comparison with ×**:
```
min(a, b) ≥ a × b  for all a, b ∈ [0,1]

Proof: min(a,b) ≥ a × b because:
  If min(a,b) = a, then a × b ≤ a × 1 = a = min(a,b)
  If min(a,b) = b, then a × b ≤ 1 × b = b = min(a,b)  ✓
```

So min is more "optimistic" than multiplication—it preserves more confidence.

---

#### 12.3.3 Probabilistic OR (⊕)

**Type**: `oplus : Confidence → Confidence → Confidence`

**Definition**: `oplus a b = a.val + b.val - a.val × b.val`

**Algebraic Properties**:

```
Commutativity:   a ⊕ b = b ⊕ a
Associativity:   (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
Identity:        0 ⊕ a = a ⊕ 0 = a
Absorption:      1 ⊕ a = a ⊕ 1 = 1
```

**Structure**: ([0,1], ⊕, 0) is a **commutative monoid with absorbing element 1**.

**Proof of associativity**:
```
(a ⊕ b) ⊕ c = (a + b - ab) + c - (a + b - ab)c
            = a + b - ab + c - ac - bc + abc
            = a + b + c - ab - ac - bc + abc

a ⊕ (b ⊕ c) = a + (b + c - bc) - a(b + c - bc)
            = a + b + c - bc - ab - ac + abc
            = a + b + c - ab - ac - bc + abc  ✓
```

**Boundedness preservation**:
```
Theorem: ∀ a b : Confidence, 0 ≤ (a ⊕ b).val ∧ (a ⊕ b).val ≤ 1

Proof of 0 ≤ a ⊕ b:
  a ⊕ b = a + b - ab = a + b(1 - a) = a(1 - b) + b
  Since a, b, (1-a), (1-b) ≥ 0:
    a(1-b) ≥ 0 and b ≥ 0 ⟹ a(1-b) + b ≥ 0  ✓

Proof of a ⊕ b ≤ 1:
  a ⊕ b = a + b - ab = a + b(1 - a)
  Since b ≤ 1 and (1 - a) ≤ 1:
    b(1-a) ≤ 1 - a
    a + b(1-a) ≤ a + (1 - a) = 1  ✓
```

**Monotonicity**:
```
Theorem: a ≤ a' ⟹ a ⊕ b ≤ a' ⊕ b

Proof:
  a ⊕ b = a + b - ab = a(1 - b) + b
  ∂/∂a [a(1-b) + b] = (1 - b) ≥ 0

  So a ⊕ b is monotonically increasing in a.  ✓
```

**Confidence-increasing property**:
```
a ⊕ b ≥ max(a, b)

Proof:
  a ⊕ b = a + b - ab = a + b(1-a)
  Since b(1-a) ≥ 0: a ⊕ b ≥ a
  By symmetry: a ⊕ b ≥ b
  Therefore: a ⊕ b ≥ max(a, b)  ✓
```

**Semantic interpretation**: Aggregation of independent evidence—when multiple independent sources support a conclusion, the combined confidence is higher than either source alone.

---

### 12.4 The Semiring Structure

The pair (⊕, ×) forms a **commutative semiring** on [0,1]:

```
([0,1], ⊕, ×, 0, 1)

Additive structure (⊕, 0):
  Associativity, Commutativity, Identity  ✓

Multiplicative structure (×, 1):
  Associativity, Commutativity, Identity  ✓

Distributivity:
  a × (b ⊕ c) = a × b ⊕ a × c

Annihilation:
  0 × a = a × 0 = 0
```

**Proof of distributivity**:
```
a × (b ⊕ c) = a × (b + c - bc)
            = ab + ac - abc

(a × b) ⊕ (a × c) = ab + ac - ab × ac
                  = ab + ac - a²bc

These are NOT equal in general!
Example: a = 0.5, b = 0.5, c = 0.5
  a × (b ⊕ c) = 0.5 × (0.5 + 0.5 - 0.25) = 0.5 × 0.75 = 0.375
  (a × b) ⊕ (a × c) = 0.25 + 0.25 - 0.0625 = 0.4375

DISTRIBUTIVITY FAILS!
```

**Critical finding**: (⊕, ×) do NOT form a semiring because distributivity fails.

This is a known result in fuzzy logic: the product t-norm and algebraic sum t-conorm are **not** a dual pair in the semiring sense.

---

### 12.5 Revised Algebraic Understanding

Since distributivity fails, what structure DO we have?

**Two separate monoids**:
1. ([0,1], ×, 1) — for conjunctive/derivation
2. ([0,1], ⊕, 0) — for disjunctive/aggregation

**With relationships**:
```
De Morgan duality: a ⊕ b = 1 - (1-a) × (1-b)
                   a × b = 1 - (1-a) ⊕ (1-b)

This connects them via negation ¬a = 1 - a
```

**But CLAIR doesn't use negation**: Confidence is not probability; we don't have P + ¬P = 1.

**What we actually need**: The operations are used in different contexts:
- × for chaining derivations (confidence of A, then B)
- min for conservative combination (pessimistic)
- ⊕ for aggregating independent evidence (multiple supports)

These don't need to interact algebraically—they're chosen based on the **justification structure**.

---

### 12.6 Connection to Thread 2 (Justification DAGs)

Thread 2 established that justification is a **DAG with labeled edges**:
- Support edges: confidence propagates via × (or min)
- Undercut edges: confidence is reduced (how?)
- Rebut edges: competing confidence levels

**When to use which operation**:

| Edge Type | Operation | Rationale |
|-----------|-----------|-----------|
| Support (conjunctive) | × | Both premises needed |
| Support (conservative) | min | Most pessimistic |
| Aggregation (independent) | ⊕ | Multiple independent supports |
| Undercut | ??? | TBD (Task 2.10) |
| Rebut | ??? | TBD (Task 2.10) |

**Open question**: How does undercut/rebut affect confidence?

Pollock's defeaters suggest:
- **Undercut**: Attacks the inferential link, not the conclusion. Confidence should decrease.
- **Rebut**: Provides counter-evidence. Net confidence depends on relative strengths.

This is **not formalized** and remains open (Task 2.10: Defeat confidence propagation).

---

### 12.7 Lean 4 Formalization Design

Based on this analysis, here's the recommended Lean 4 formalization:

#### 12.7.1 Layer 1: Abstract Algebras

```lean4
/-- Confidence multiplication monoid -/
class ConfidenceMulMonoid (C : Type*) extends One C, Mul C, LE C where
  mul_assoc : ∀ a b c : C, a * b * c = a * (b * c)
  mul_comm : ∀ a b : C, a * b = b * a
  one_mul : ∀ a : C, 1 * a = a
  mul_one : ∀ a : C, a * 1 = a

/-- Confidence min semilattice -/
class ConfidenceMinSemilattice (C : Type*) extends One C, LE C where
  inf : C → C → C
  inf_comm : ∀ a b : C, inf a b = inf b a
  inf_assoc : ∀ a b c : C, inf (inf a b) c = inf a (inf b c)
  inf_idem : ∀ a : C, inf a a = a
  one_inf : ∀ a : C, inf 1 a = a

/-- Confidence oplus monoid for aggregation -/
class ConfidenceOplusMonoid (C : Type*) extends Zero C where
  oplus : C → C → C
  oplus_assoc : ∀ a b c : C, oplus (oplus a b) c = oplus a (oplus b c)
  oplus_comm : ∀ a b : C, oplus a b = oplus b a
  zero_oplus : ∀ a : C, oplus 0 a = a
```

#### 12.7.2 Layer 2: Concrete Implementation

```lean4
/-- Confidence as a subtype of Real in [0,1] -/
def Confidence := { c : ℝ // 0 ≤ c ∧ c ≤ 1 }

namespace Confidence

/-- Zero confidence -/
instance : Zero Confidence := ⟨⟨0, by norm_num, by norm_num⟩⟩

/-- Full confidence -/
instance : One Confidence := ⟨⟨1, by norm_num, by norm_num⟩⟩

/-- Multiplication operation -/
instance : Mul Confidence where
  mul a b := ⟨a.val * b.val, by
    constructor
    · exact mul_nonneg a.property.1 b.property.1
    · calc a.val * b.val
        ≤ a.val * 1 := mul_le_mul_of_nonneg_left b.property.2 a.property.1
        _ = a.val := mul_one a.val
        _ ≤ 1 := a.property.2⟩

/-- Minimum operation -/
def min (a b : Confidence) : Confidence :=
  if h : a.val ≤ b.val then a else b

/-- Probabilistic OR operation -/
def oplus (a b : Confidence) : Confidence :=
  ⟨a.val + b.val - a.val * b.val, by
    constructor
    · -- 0 ≤ a + b - ab = a(1-b) + b
      have h1 : 0 ≤ 1 - b.val := by linarith [b.property.2]
      have h2 : 0 ≤ a.val * (1 - b.val) := mul_nonneg a.property.1 h1
      linarith [b.property.1]
    · -- a + b - ab ≤ 1
      have h1 : a.val + b.val * (1 - a.val) ≤ 1 := by
        have hb : b.val * (1 - a.val) ≤ 1 - a.val := by
          apply mul_le_of_le_one_left (by linarith [a.property.1]) b.property.2
        linarith [a.property.2]
      ring_nf at h1 ⊢
      linarith⟩

end Confidence
```

#### 12.7.3 Layer 3: Key Theorems

```lean4
namespace Confidence

-- Multiplication theorems
theorem mul_bounded (a b : Confidence) :
    0 ≤ (a * b).val ∧ (a * b).val ≤ 1 := (a * b).property

theorem mul_assoc (a b c : Confidence) : a * b * c = a * (b * c) := by
  apply Subtype.ext
  simp only [HMul.hMul, Mul.mul]
  ring

theorem mul_comm (a b : Confidence) : a * b = b * a := by
  apply Subtype.ext
  simp only [HMul.hMul, Mul.mul]
  ring

theorem one_mul (a : Confidence) : 1 * a = a := by
  apply Subtype.ext
  simp only [HMul.hMul, Mul.mul, One.one]
  ring

theorem mul_one (a : Confidence) : a * 1 = a := by
  apply Subtype.ext
  simp only [HMul.hMul, Mul.mul, One.one]
  ring

theorem zero_mul (a : Confidence) : 0 * a = 0 := by
  apply Subtype.ext
  simp only [HMul.hMul, Mul.mul, Zero.zero]
  ring

-- Min theorems
theorem min_bounded (a b : Confidence) :
    0 ≤ (min a b).val ∧ (min a b).val ≤ 1 := by
  unfold min
  split <;> [exact a.property; exact b.property]

theorem min_comm (a b : Confidence) : min a b = min b a := by
  unfold min
  split <;> split <;> {
    apply Subtype.ext
    simp only
    linarith
  }

theorem min_assoc (a b c : Confidence) : min (min a b) c = min a (min b c) := by
  -- Proof by case analysis on ordering
  sorry -- requires careful case analysis

theorem min_idem (a : Confidence) : min a a = a := by
  unfold min
  simp

-- Oplus theorems
theorem oplus_bounded (a b : Confidence) :
    0 ≤ (oplus a b).val ∧ (oplus a b).val ≤ 1 := (oplus a b).property

theorem oplus_comm (a b : Confidence) : oplus a b = oplus b a := by
  apply Subtype.ext
  unfold oplus
  ring

theorem oplus_assoc (a b c : Confidence) : oplus (oplus a b) c = oplus a (oplus b c) := by
  apply Subtype.ext
  unfold oplus
  ring

theorem zero_oplus (a : Confidence) : oplus 0 a = a := by
  apply Subtype.ext
  unfold oplus
  simp [Zero.zero]
  ring

theorem oplus_zero (a : Confidence) : oplus a 0 = a := by
  apply Subtype.ext
  unfold oplus
  simp [Zero.zero]
  ring

-- Cross-operation theorems
theorem min_ge_mul (a b : Confidence) : (min a b).val ≥ (a * b).val := by
  unfold min
  split <;> {
    simp only [HMul.hMul, Mul.mul]
    nlinarith [a.property.1, a.property.2, b.property.1, b.property.2]
  }

theorem oplus_ge_max (a b : Confidence) :
    (oplus a b).val ≥ max a.val b.val := by
  unfold oplus
  constructor
  · -- a ⊕ b ≥ a
    have : b.val * (1 - a.val) ≥ 0 := by
      apply mul_nonneg b.property.1
      linarith [a.property.2]
    linarith
  · -- a ⊕ b ≥ b (by symmetry via oplus_comm)
    have : a.val * (1 - b.val) ≥ 0 := by
      apply mul_nonneg a.property.1
      linarith [b.property.2]
    linarith

-- CRITICAL: Distributivity does NOT hold
-- This is intentional and matches the mathematical analysis
-- (⊕, ×) is NOT a semiring

-- Monotonicity theorems
theorem mul_monotone_left (a a' b : Confidence) (h : a.val ≤ a'.val) :
    (a * b).val ≤ (a' * b).val := by
  simp only [HMul.hMul, Mul.mul]
  exact mul_le_mul_of_nonneg_right h b.property.1

theorem oplus_monotone_left (a a' b : Confidence) (h : a.val ≤ a'.val) :
    (oplus a b).val ≤ (oplus a' b).val := by
  unfold oplus
  have h1 : (1 - b.val) ≥ 0 := by linarith [b.property.2]
  nlinarith

end Confidence
```

---

### 12.8 Key Insights from This Exploration

#### Insight 1: No semiring structure

The (⊕, ×) pair does NOT form a semiring because distributivity fails. This is mathematically fundamental and cannot be fixed. The operations must be understood as **separate monoids** used in different contexts.

#### Insight 2: Operation selection is semantic, not algebraic

The choice of which operation to use depends on the **justification structure**:
- × for sequential/conjunctive derivation (both premises needed)
- min for conservative combination (pessimistic estimate)
- ⊕ for aggregation of independent evidence

This connects directly to Thread 2's DAG structure.

#### Insight 3: Boundedness proofs are straightforward

All three operations preserve the [0,1] bounds. The proofs are elementary algebra.

#### Insight 4: min is more optimistic than ×

Counterintuitively, min(a,b) ≥ a×b for all a,b ∈ [0,1]. So "conservative" min actually preserves more confidence than "multiplicative" ×. The semantic difference:
- × assumes independence: "both happened, multiply probabilities"
- min assumes pessimism: "as confident as weakest link"

#### Insight 5: ⊕ is confidence-increasing

Unlike × and min, ⊕ increases confidence: a ⊕ b ≥ max(a,b). This models the intuition that multiple independent sources of evidence strengthen a conclusion.

#### Insight 6: Defeat operations remain open

How undercut and rebut edges affect confidence is NOT formalized. This is Task 2.10 and is one of the most important remaining questions for the justification system.

---

### 12.9 What I Don't Know

#### Mathematical unknowns

1. **Defeat propagation**: How should undercut/rebut edges modify confidence? Options include:
   - Subtractive: c' = max(0, c - defeat_strength)
   - Multiplicative discounting: c' = c × (1 - defeat_strength)
   - Probability kinematics (Jeffrey conditioning)
   - Ranking theory (Spohn's approach)

2. **Correlated evidence**: When evidence is not independent, ⊕ overestimates combined confidence. No good solution exists in CLAIR currently.

3. **Higher structures**: Is there useful structure beyond monoids? The lack of distributivity limits algebraic tools.

#### Formalization unknowns

1. **Lean proof complexity**: The `min_assoc` proof requires careful case analysis. How clean can this be made in Lean 4?

2. **Typeclass organization**: Should we use Mathlib's existing `Monoid` typeclass or define custom ones for confidence?

3. **Computational extraction**: How do these proofs extract to efficient code?

---

### 12.10 Conclusion

Task 8.6 is **complete**. The three confidence combination operations are:

1. **Multiplication (×)**: Commutative monoid ([0,1], ×, 1)
   - For conjunctive derivation
   - Confidence decreases with each derivation step

2. **Minimum (min)**: Bounded meet-semilattice ([0,1], min, 1)
   - For conservative combination
   - Confidence bounded by weakest premise

3. **Probabilistic OR (⊕)**: Commutative monoid ([0,1], ⊕, 0)
   - For aggregation of independent evidence
   - Confidence increases with multiple supports

**Key finding**: These do NOT form a semiring—distributivity fails. This is mathematically necessary and shapes how the operations should be used in CLAIR.

**Next steps**:
- Task 8.7: Prove boundedness preservation formally in Lean 4
- Task 2.10: Investigate defeat confidence propagation
- Task 2.13: Investigate correlated evidence handling

---

*Thread 8 Status: Tasks 8.5, 8.6 explored. Confidence type and operations designed. Algebraic structure fully characterized. Ready for Lean 4 implementation.*
