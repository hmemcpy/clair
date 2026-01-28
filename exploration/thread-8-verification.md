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

*Thread 8 Status: Task 8.5 explored. Confidence type design complete. Ready for implementation.*
