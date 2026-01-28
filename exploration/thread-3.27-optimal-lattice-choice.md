# Thread 3.27: Optimal Lattice Choice for CPL-finite

> **Status**: Active exploration (Session 63)
> **Task**: 3.27 Is L₅ the right finite lattice? Trade-offs with L₃, L₁₀, L₁₀₀?
> **Question**: What is the optimal finite confidence lattice for CLAIR's type-level checks?
> **Prior Threads**: Thread 3.20 (CPL-finite formalization), Thread 3.19 (type anti-bootstrapping)

---

## 1. The Problem

### 1.1 Context

CPL-finite (Confidence-Bounded Provability Logic with finite values) requires a discrete lattice of confidence values. Thread 3.20 proposed L₅ = {0, 0.25, 0.5, 0.75, 1} as the default. But is this optimal?

**The core question**: Given the trade-offs between expressiveness, computational efficiency, algebraic properties, and cognitive ergonomics, what is the best finite lattice for CLAIR?

### 1.2 Why This Matters

The lattice choice affects:
1. **Type checking complexity**: More values = larger state space = slower checking
2. **User expressiveness**: More values = finer-grained confidence distinctions
3. **Algebraic closure**: Different lattices close differently under operations
4. **Löb discount behavior**: The g(c) = c² function interacts differently with different lattices
5. **Human interpretability**: Users must understand and work with these values

### 1.3 Constraints from CLAIR's Design

From the existing exploration, any lattice L must satisfy:
1. **Includes 0 and 1**: For certainty and impossibility
2. **Closed under ⊗ (multiplication)**: With floor rounding
3. **Closed under ⊕ (probabilistic OR)**: With ceiling rounding
4. **Löb discount g_L(c) = floor_L(c²) must prevent bootstrapping**: g_L(c) ≤ c for all c ∈ L
5. **Supports undercut and rebut**: Operations must remain meaningful

---

## 2. Candidate Lattices

### 2.1 L₃ (Three-Valued)

```
L₃ = {0, 0.5, 1}
    = {None, Maybe, Certain}
```

**Multiplication table (⊗)**:
| ⊗ | 0 | 0.5 | 1 |
|---|---|-----|---|
| 0 | 0 | 0 | 0 |
| 0.5 | 0 | 0 | 0.5 |
| 1 | 0 | 0.5 | 1 |

Note: 0.5 × 0.5 = 0.25 → floor to 0

**Probabilistic OR table (⊕)**:
| ⊕ | 0 | 0.5 | 1 |
|---|---|-----|---|
| 0 | 0 | 0.5 | 1 |
| 0.5 | 0.5 | 1 | 1 |
| 1 | 1 | 1 | 1 |

Note: 0.5 ⊕ 0.5 = 0.75 → ceiling to 1

**Löb discount**:
- g(0) = 0
- g(0.5) = floor(0.25) = 0
- g(1) = 1

**Problem**: L₃ is too coarse. Any derivation from two Maybe premises gives None confidence. This is excessively pessimistic.

### 2.2 L₅ (Five-Valued) - Current Default

```
L₅ = {0, 0.25, 0.5, 0.75, 1}
    = {None, Low, Medium, High, Certain}
```

Full operation tables in Thread 3.20. Key properties:

**Löb discount**:
- g(0) = 0
- g(0.25) = 0 (0.0625 → 0)
- g(0.5) = 0.25
- g(0.75) = 0.5 (0.5625 → 0.5)
- g(1) = 1

**Strengths**:
- Human-interpretable (Low/Medium/High/Certain maps to natural language)
- Reasonable precision for most epistemic distinctions
- Not too large for efficient type checking

**Weaknesses**:
- 0.25 ⊗ 0.25 = 0 (loses precision at low end)
- Löb discount collapses Low → None (aggressive)

### 2.3 L₇ (Seven-Valued)

```
L₇ = {0, 0.167, 0.333, 0.5, 0.667, 0.833, 1}
   ≈ {0, 1/6, 2/6, 3/6, 4/6, 5/6, 1}
```

Alternatively, using eighths:
```
L₇' = {0, 0.125, 0.25, 0.5, 0.75, 0.875, 1}
    = {0, 1/8, 1/4, 1/2, 3/4, 7/8, 1}
```

**Löb discount for L₇' (eighths)**:
- g(0) = 0
- g(0.125) = floor(0.015625) = 0
- g(0.25) = floor(0.0625) = 0
- g(0.5) = floor(0.25) = 0.25
- g(0.75) = floor(0.5625) = 0.5
- g(0.875) = floor(0.765625) = 0.75
- g(1) = 1

**Observation**: L₇' captures 0.25² = 0.0625 as 0 (same as L₅) but gains the advantage that 0.875² ≈ 0.77 → 0.75, giving a smoother decay at the high end.

### 2.4 L₉ (Nine-Valued) - Quarters with Midpoints

```
L₉ = {0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1}
    = {0, 1/8, 1/4, 3/8, 1/2, 5/8, 3/4, 7/8, 1}
```

**Löb discount for L₉**:
| c | c² | floor_L₉(c²) |
|---|-----|--------------|
| 0 | 0 | 0 |
| 0.125 | 0.015625 | 0 |
| 0.25 | 0.0625 | 0 |
| 0.375 | 0.140625 | 0.125 |
| 0.5 | 0.25 | 0.25 |
| 0.625 | 0.390625 | 0.375 |
| 0.75 | 0.5625 | 0.5 |
| 0.875 | 0.765625 | 0.75 |
| 1 | 1 | 1 |

**Key insight**: L₉ has "nice" properties:
- 0.375² = 0.140625 → 0.125 (doesn't collapse to 0)
- Smoother degradation of confidence at all levels

### 2.5 L₁₀ (Decimal)

```
L₁₀ = {0, 0.1, 0.2, ..., 0.9, 1}
     = 11 values total
```

**Löb discount for L₁₀**:
| c | c² | floor_L₁₀(c²) |
|---|-----|--------------|
| 0 | 0 | 0 |
| 0.1 | 0.01 | 0 |
| 0.2 | 0.04 | 0 |
| 0.3 | 0.09 | 0 |
| 0.4 | 0.16 | 0.1 |
| 0.5 | 0.25 | 0.2 |
| 0.6 | 0.36 | 0.3 |
| 0.7 | 0.49 | 0.4 |
| 0.8 | 0.64 | 0.6 |
| 0.9 | 0.81 | 0.8 |
| 1 | 1 | 1 |

**Strengths**:
- Decimal percentages are familiar (0.7 = "70% confident")
- Smoothest decay of any small lattice

**Weaknesses**:
- 11 values starts to feel like "almost continuous"
- 0.1, 0.2, 0.3 all square to 0 (aggressive collapse at low end)

### 2.6 L₁₀₀ (Percentages)

```
L₁₀₀ = {0, 0.01, 0.02, ..., 0.99, 1}
      = 101 values
```

**Analysis**: At this granularity, we're essentially approximating continuous [0,1] with 1% precision. This has been explicitly considered and rejected because:
1. Vidal (2019) suggests undecidability concerns kick in as we approach continuous values
2. The type-checking state space grows with |L|²
3. Loses the cognitive benefit of discrete categories

---

## 3. Evaluation Criteria

### 3.1 Algebraic Properties

**Criterion 1: Multiplication closure quality**

How much information is lost when a × b is floored?

Define *distortion* as: d(L) = max_{a,b ∈ L} |a × b - floor_L(a × b)|

| Lattice | Max Distortion |
|---------|----------------|
| L₃ | 0.25 (at 0.5 × 0.5) |
| L₅ | 0.0625 (at 0.25 × 0.25) |
| L₇' | 0.0625 (same) |
| L₉ | 0.015625 (at 0.125 × 0.125) |
| L₁₀ | 0.01 (at 0.1 × 0.1) |

**Observation**: Distortion decreases with lattice size, but diminishing returns after L₉.

**Criterion 2: Löb discount behavior**

How aggressive is the anti-bootstrapping mechanism?

Define *Löb drop* as: δ_L(c) = c - g_L(c) for c ∈ (0,1)

| c | L₃ drop | L₅ drop | L₉ drop | L₁₀ drop |
|---|---------|---------|---------|----------|
| 0.5 | 0.5 | 0.25 | 0.25 | 0.3 |
| 0.75 | N/A | 0.25 | 0.25 | N/A |
| 0.875 | N/A | N/A | 0.125 | N/A |
| 0.9 | N/A | N/A | N/A | 0.1 |

L₃ is excessively aggressive (Medium → None). L₅ and L₉ are comparable in their Löb behavior.

**Criterion 3: ⊕ closure quality**

How much error is introduced by ceiling?

Define *⊕-distortion* as: e(L) = max_{a,b ∈ L} |ceiling_L(a ⊕ b) - (a ⊕ b)|

This is symmetric to multiplication distortion. Finer lattices have lower distortion.

### 3.2 Computational Properties

**Criterion 4: Type-checking complexity**

The type checker must track confidence bounds through derivations. State space scales with |L|.

For PSPACE-complete algorithms, the practical difference between |L| = 5 and |L| = 11 is noticeable but manageable. The critical threshold is around |L| = 100 where enumeration becomes impractical.

**Recommendation**: Keep |L| ≤ 20 for practical type checking.

**Criterion 5: Decision procedure size**

The explicit operation tables grow as |L|². This affects:
- Code size
- Cache efficiency
- Verification complexity

| Lattice | Table entries for one operation |
|---------|---------------------------------|
| L₃ | 9 |
| L₅ | 25 |
| L₉ | 81 |
| L₁₀ | 121 |

L₅ hits a sweet spot: tables fit in cache, verification tractable.

### 3.3 Cognitive Properties

**Criterion 6: Human interpretability**

Users must understand confidence values. Natural language mappings:

**L₃**:
- 0 = "definitely not"
- 0.5 = "maybe"
- 1 = "definitely"

Too coarse for most epistemic work.

**L₅**:
- 0 = "definitely not"
- 0.25 = "unlikely"
- 0.5 = "uncertain"
- 0.75 = "likely"
- 1 = "definitely"

Natural mapping to everyday reasoning.

**L₁₀**:
- Maps to "X% confident"
- Familiar from probability education

**Observation**: L₅ has optimal cognitive mapping. Humans naturally distinguish ~5-7 categories (Miller's Law). L₁₀ is familiar but loses categorical thinking benefits.

**Criterion 7: Teachability**

How easy is the lattice to explain to new users?

L₃: Trivial but limited
L₅: "Think None/Low/Medium/High/Certain"
L₁₀: "Think percentages with 10% granularity"
L₁₀₀: "Just use percentages"

L₅ is most pedagogically natural for an epistemic type system.

### 3.4 Domain-Specific Properties

**Criterion 8: Alignment with CLAIR's dual-monoid structure**

CLAIR uses both × (derivation) and ⊕ (aggregation). The lattice should support both meaningfully.

**Test case**: Two Medium (0.5) beliefs aggregated then derived from.

In L₅:
- aggregate(Medium, Medium) = ceiling(0.75) = High
- derive(High, something) uses High

This feels right: two independent pieces of medium-strength evidence combine to high confidence.

In L₃:
- aggregate(Maybe, Maybe) = ceiling(0.75) = Certain
- derive(Certain, anything) = that thing

This is too optimistic! Two "maybe"s shouldn't give certainty.

**Conclusion**: L₃ fails this test. L₅ passes.

---

## 4. Mathematical Analysis: The c² Closure Problem Revisited

### 4.1 No Perfect Lattice Exists

**Theorem (Thread 3.20, restated)**: No finite subset of (0,1) is closed under c ↦ c².

**Proof**: For any c ∈ (0,1), the sequence c, c², c⁴, c⁸, ... converges to 0 but never equals 0 (unless c = 0). So any finite set containing c ∈ (0,1) is not closed under squaring.

**Corollary**: All finite lattices require rounding for the Löb discount.

### 4.2 Rounding Strategies

Given that rounding is necessary, which direction?

**Floor (g_L(c) = max{l ∈ L : l ≤ c²})**:
- Conservative: discounted confidence is never overestimated
- Sound for anti-bootstrapping: g_L(c) ≤ c² ≤ c
- May be overly pessimistic

**Ceiling (g_L(c) = min{l ∈ L : l ≥ c²})**:
- Aggressive: discounted confidence may be overestimated
- Could violate anti-bootstrapping if ceiling(c²) > c
- NOT acceptable for CLAIR

**Nearest (g_L(c) = argmin_{l ∈ L}|l - c²|)**:
- Minimizes distortion on average
- But ceiling cases could violate anti-bootstrapping
- NOT acceptable for CLAIR

**Conclusion**: Floor rounding is the only semantically correct choice for g_L. This is what CLAIR uses.

### 4.3 Finding Lattices Where Floor Rounding Is "Nice"

A lattice has *nice squaring* if for all c ∈ L, floor_L(c²) is exactly c² whenever c² happens to be in L.

**L₅ analysis**:
- 0² = 0 ✓ (exact)
- 0.25² = 0.0625 → 0 (rounded)
- 0.5² = 0.25 ✓ (exact!)
- 0.75² = 0.5625 → 0.5 (rounded)
- 1² = 1 ✓ (exact)

L₅ gets 0.5 exactly right!

**L₉ analysis**:
- 0.375² = 0.140625 → 0.125 (rounded)
- 0.5² = 0.25 ✓ (exact!)
- 0.625² = 0.390625 → 0.375 (rounded)
- 0.75² = 0.5625 → 0.5 (rounded)

L₉ also gets 0.5 exactly.

**Key insight**: Any lattice containing both c and c² (for any c) will have exact Löb discount at that point. The lattice {0, 0.5, 0.25, 1} contains 0.5 and 0.5² = 0.25, but not 0.25² = 0.0625.

### 4.4 The "Löb-Friendly" Lattice Construction

**Definition**: A lattice L is *n-Löb-friendly* if it is closed under n applications of squaring from any element.

**Observation**: No finite L is ∞-Löb-friendly (by the closure impossibility theorem).

**Construction**: For a base set S ⊂ (0,1), the 1-Löb-friendly closure is S ∪ {s² : s ∈ S} ∪ {0, 1}.

Starting from {0.5, 0.75}:
- Step 1: Add 0.5² = 0.25, 0.75² = 0.5625
- Step 2: Add 0.25² = 0.0625, 0.5625² = 0.31640625
- This explodes quickly...

**Conclusion**: Don't try to achieve Löb-closure. Accept floor rounding.

---

## 5. Practical Recommendations

### 5.1 Default Choice: L₅

L₅ = {0, 0.25, 0.5, 0.75, 1} should be CLAIR's default for:

1. **Cognitive ergonomics**: Maps perfectly to "None/Low/Medium/High/Certain"
2. **Computational efficiency**: 25-entry operation tables
3. **Reasonable precision**: Catches the key confidence distinctions
4. **Tested**: Extensively explored in Threads 3.19 and 3.20

### 5.2 Alternative for High-Precision Domains: L₉

L₉ = {0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1} for domains requiring finer gradations:

1. **Scientific reasoning**: Where 75% vs 87.5% matters
2. **Risk assessment**: Finer granularity for critical decisions
3. **Formal verification**: When precise confidence tracking is needed

### 5.3 Avoid L₃ (Too Coarse)

L₃ = {0, 0.5, 1} is unsuitable:

1. Medium × Medium = None is too aggressive
2. Loses important epistemic distinctions
3. Violates intuitions about evidence combination

### 5.4 Avoid L₁₀₀ (Overkill)

L₁₀₀ = percentages is unsuitable:

1. Approaches undecidability concerns from continuous case
2. No cognitive benefit over L₁₀
3. Large state space for type checking
4. False precision (humans can't reliably distinguish 83% from 84% confidence)

### 5.5 Consider L₁₀ for Teaching

L₁₀ = {0, 0.1, 0.2, ..., 1} might be useful for:

1. **Educational contexts**: Familiar percentage system
2. **Gradual transition**: Users comfortable with percentages before switching to L₅

But L₅ should remain the production default.

---

## 6. Configuration Strategy

### 6.1 Proposal: Lattice as Type Parameter

CLAIR could parameterize by lattice choice:

```clair
-- Type-level lattice specification
type ConfidenceLattice = L3 | L5 | L9 | L10 | Custom(Set<Rational>)

-- Parameterized belief type
type Belief<level : Nat, content : Type, lat : ConfidenceLattice, cap : lat.Value>

-- Default: L5
type Belief<n, A, c> = Belief<n, A, L5, c>
```

### 6.2 Lattice Interoperability

When combining beliefs from different lattice contexts:

```clair
-- Coercion: finer to coarser (lossless)
coerce : Belief<n, A, L9, c> → Belief<n, A, L5, floor_L5(c)>

-- Coercion: coarser to finer (no information gained)
embed : Belief<n, A, L5, c> → Belief<n, A, L9, c>
```

### 6.3 Pragmatic Default

For simplicity, CLAIR should:
1. Use L₅ as the universal default
2. Allow domain-specific override via module-level annotation
3. Require explicit coercion when mixing lattices

---

## 7. Implementation Details for L₅

### 7.1 Lean 4 Definition

```lean
-- The canonical five-valued lattice
inductive L5 where
  | none    -- 0
  | low     -- 0.25
  | medium  -- 0.5
  | high    -- 0.75
  | certain -- 1
  deriving Repr, DecidableEq, Ord

namespace L5

def toRat : L5 → ℚ
  | .none    => 0
  | .low     => 1/4
  | .high    => 3/4
  | .medium  => 1/2
  | .certain => 1

def mul : L5 → L5 → L5
  | .certain, x => x
  | x, .certain => x
  | .none, _    => .none
  | _, .none    => .none
  | .high, .high   => .medium     -- 0.5625 → 0.5
  | .high, .medium => .low        -- 0.375 → 0.25
  | .medium, .high => .low
  | .medium, .medium => .low      -- 0.25
  | .low, _        => .none       -- < 0.25
  | _, .low        => .none

def oplus : L5 → L5 → L5
  | .none, x => x
  | x, .none => x
  | .certain, _ => .certain
  | _, .certain => .certain
  | .low, .low       => .medium   -- 0.4375 → 0.5
  | .low, .medium    => .high     -- 0.625 → 0.75
  | .medium, .low    => .high
  | .low, .high      => .high     -- 0.8125 → 0.75
  | .high, .low      => .high
  | .medium, .medium => .high     -- 0.75
  | .medium, .high   => .certain  -- 0.875 → 1
  | .high, .medium   => .certain
  | .high, .high     => .certain  -- 0.9375 → 1

def loebDiscount : L5 → L5
  | .none    => .none
  | .low     => .none     -- 0.0625 → 0
  | .medium  => .low      -- 0.25
  | .high    => .medium   -- 0.5625 → 0.5
  | .certain => .certain  -- 1

end L5
```

### 7.2 Verification Properties

Key theorems to prove:

```lean
-- Anti-bootstrapping: discount never increases
theorem loeb_le : ∀ c : L5, c ≠ .none → loebDiscount c < c ∨ c = .certain := by
  intro c hne
  cases c <;> simp [loebDiscount]

-- Multiplication is monotonic
theorem mul_mono : ∀ a b c : L5, a ≤ b → mul a c ≤ mul b c := by
  sorry -- case analysis

-- ⊕ is monotonic
theorem oplus_mono : ∀ a b c : L5, a ≤ b → oplus a c ≤ oplus b c := by
  sorry -- case analysis

-- Key identity: Medium is exactly preserved
theorem medium_square_exact : loebDiscount L5.medium = L5.low := by
  rfl
```

---

## 8. Open Questions Remaining

### 8.1 Resolved by This Exploration

1. **Is L₅ optimal?** → Yes, for the default use case. It balances all criteria well.
2. **When to use alternatives?** → L₉ for high-precision domains, L₁₀ for teaching.
3. **Why not L₃?** → Too coarse; multiplication is excessively lossy.
4. **Why not L₁₀₀?** → False precision, computational overhead, no cognitive benefit.

### 8.2 New Questions Discovered

1. **Domain-specific lattices**: Should CLAIR support custom lattices (e.g., {0, 0.1, 0.5, 0.9, 1} for risk assessment)?

2. **Lattice refinement types**: Can we express "at least Low confidence" at the type level?
   ```clair
   type AtLeast(c : L5) = {x : L5 | x >= c}
   ```

3. **Mixed-lattice operations**: What are the exact semantics when combining L₅ and L₉ beliefs?

4. **Empirical validation**: Has anyone studied what granularity humans actually use when reasoning about confidence?

---

## 9. Confidence Assessment

| Finding | Confidence | Justification |
|---------|------------|---------------|
| L₅ is optimal default | 0.85 | Balances all criteria, well-tested in prior threads |
| L₃ is too coarse | 0.95 | Clear counterexamples (Medium × Medium = None) |
| L₁₀₀ is overkill | 0.90 | Computational and cognitive arguments |
| L₉ is best high-precision alternative | 0.75 | Reasonable but less explored |
| Floor rounding is correct | 0.95 | Semantic soundness argument |
| Parameterized lattice is feasible | 0.70 | Design sketch, needs implementation |

---

## 10. Summary

### 10.1 Main Conclusion

**L₅ = {0, 0.25, 0.5, 0.75, 1} is the optimal finite confidence lattice for CLAIR's default use.**

This conclusion rests on:
1. **Cognitive fit**: Maps to natural language categories (None/Low/Medium/High/Certain)
2. **Computational tractability**: 25-entry tables, efficient type checking
3. **Algebraic reasonableness**: 0.5² = 0.25 is exact; other roundings are acceptable
4. **Miller's Law alignment**: 5 categories matches human cognitive capacity
5. **Prior validation**: Extensively tested in Threads 3.19 and 3.20

### 10.2 Alternatives

- **L₃**: Rejected (too coarse, aggressive multiplication)
- **L₉**: Acceptable for high-precision domains
- **L₁₀**: Acceptable for teaching (familiar percentage system)
- **L₁₀₀**: Rejected (false precision, computational overhead)

### 10.3 Recommendations for CLAIR

1. Use L₅ as the fixed default lattice
2. Do not parameterize by lattice (complexity outweighs benefit for most users)
3. Document L₉ as an optional "high precision mode" for future consideration
4. The Lean formalization should prove key properties for L₅

---

## 11. References

### CLAIR Internal
- exploration/thread-3.20-cpl-finite-formalization.md — CPL-finite design
- exploration/thread-3.19-type-anti-bootstrapping.md — Type-level constraints
- exploration/thread-3.18-loeb-discount.md — g(c) = c² derivation

### External
- Miller, G. A. (1956). "The magical number seven, plus or minus two"
- Bou, F., Esteva, F., Godo, L. (2011). "On the Minimum Many-Valued Modal Logic over a Finite Residuated Lattice"
- Standard fuzzy logic references for t-norm properties

---

*Thread 3.27 Status: Substantially explored. L₅ confirmed as optimal default. L₃ rejected, L₁₀₀ rejected. L₉ identified as high-precision alternative. Ready for integration.*
