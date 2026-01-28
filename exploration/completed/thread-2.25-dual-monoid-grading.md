# Thread 2.25: Dual-Monoid Grading for CLAIR

> **Status**: Active exploration (Session 55)
> **Task**: 2.25 Formalize the two-sorted grading structure for × and ⊕
> **Question**: What algebraic structure properly characterizes CLAIR's confidence operations?
> **Prior Work**: Thread 2.22 (Curry-Howard), Thread 8 (Lean formalization), formal/lean/CLAIR/Confidence/

---

## 1. The Problem

### 1.1 The Non-Distributivity Discovery

Session 11 (Thread 8) discovered a fundamental algebraic fact about CLAIR:

**CLAIR's confidence operations (×, ⊕) do NOT form a semiring.**

Distributivity fails:
```
a × (b ⊕ c) ≠ (a × b) ⊕ (a × c)
```

**Counterexample** (a = b = c = 0.5):
- Left side: 0.5 × (0.5 ⊕ 0.5) = 0.5 × 0.75 = 0.375
- Right side: (0.5 × 0.5) ⊕ (0.5 × 0.5) = 0.25 ⊕ 0.25 = 0.4375

This is not a CLAIR limitation—it's mathematically fundamental. The product t-norm and algebraic sum t-conorm don't distribute over each other.

### 1.2 Why This Matters

Standard **graded type theory** (Orchard et al. 2019, Gaboardi et al. 2016) assumes grades form a **semiring**:
- Addition (+) for combining uses in branches
- Multiplication (·) for composition
- Distributivity ensures coherent grade propagation

CLAIR has:
- **×** (multiplication) for derivation: combining premises
- **⊕** (probabilistic OR) for aggregation: combining independent evidence

These serve fundamentally different purposes and don't distribute. We need a different algebraic foundation.

### 1.3 The Question

**What algebraic structure properly characterizes CLAIR's confidence operations?**

Options to explore:
1. Two separate monoids (current approach)
2. Double Residuated Lattice (DRL)
3. Linearly Distributive Category
4. Two-sorted graded type theory
5. Bimonoid without distributivity

---

## 2. Prior Art Survey

### 2.1 Standard Graded Type Theory

**Quantitative Program Reasoning with Graded Modal Types** (Orchard, Liepelt, Eades 2019):

Grades form a preordered semiring (R, +, ·, 0, 1):
- (R, +, 0) is a commutative monoid (branching)
- (R, ·, 1) is a monoid (composition)
- · distributes over + (coherence)

**Granule** implementation uses various semirings:
- Natural numbers (N, +, ×, 0, 1)
- Security lattices (with + as join)
- Usage tracking

**Problem for CLAIR**: We have two monoids but no distributivity.

### 2.2 Double Residuated Lattices

**Orłowska & Radzikowska (2002)** introduced Double Residuated Lattices (DRLs):

> "There is no primitive operation in a residuated lattice that properly accounts for a strong disjunction playing the role of a t-conorm... To remedy this situation, [we] expand residuated lattices with an extra monoidal operator."

A DRL has:
- A residuated lattice structure for conjunction (t-norm)
- An additional monoidal operator for disjunction (t-conorm)
- Dual residua for both

**Relevance to CLAIR**: DRLs capture exactly our situation—two monoidal operations that don't distribute. However, they focus on the *logical* operations (implication via residua), not type-theoretic grading.

**Key insight**: The failure of distributivity between t-norms and t-conorms is well-known:
> "Any t-conorm distributes over the minimum [t-norm], but not over any other t-norm."

This confirms CLAIR's non-distributivity is mathematically expected.

### 2.3 Linearly Distributive Categories

**Cockett & Seely (1997)** introduced Linearly Distributive Categories (LDCs):

An LDC has:
- Two monoidal structures (⊗, ⊤) and (⊕, ⊥)
- Linear distributors: δ : A ⊗ (B ⊕ C) → (A ⊗ B) ⊕ C

**Key point**: The distributor δ is *not* an isomorphism in general. This is "linear" distributivity—weaker than full distributivity.

**Warning from nLab**:
> "A distributive category cannot be made into a linearly distributive category with ⊗ = × and ⊕ = + unless it is a partial order."

**Relevance to CLAIR**:
- LDCs provide categorical semantics for linear logic's multiplicative fragment
- They handle two tensor products that don't fully distribute
- However, CLAIR's operations don't even have linear distributors

**Assessment**: LDCs are relevant but may be overkill for CLAIR's needs. We don't need full categorical semantics—we need a grading structure for types.

### 2.4 Graded Monads

**nLab** defines an M-graded monad as a lax monoidal functor from a monoidal category M to the endofunctor category:
```
(M, ⊗, I) → ([C, C], ∘, id_C)
```

**Fujii, Katsumata, Melliès (2016)** developed a formal theory of graded monads showing every graded monad can be factored as a strict action transported along a left adjoint.

**Category-graded monads** (Orchard, Wadler, Eades 2020) generalize to indexing by morphisms of a category, not just elements of a monoid.

**Relevance to CLAIR**: CLAIR's Belief type is already characterized as a graded monad over ([0,1], ×, 1). The question is how to incorporate ⊕ into the grading structure.

### 2.5 Bimonoids

A **bimonoid** is a set with two monoid operations that satisfy *compatibility conditions* but not necessarily distributivity.

From the semiring literature:
> "Semirings arise as the special case of bimonoids where multiplication fully distributes over addition... bimonoids allow for broader algebraic behaviors [without] full distributivity."

**Relevance**: CLAIR's confidence algebra is precisely a bimonoid:
- ([0,1], ×, 1) — derivation monoid
- ([0,1], ⊕, 0) — aggregation monoid
- No distributivity requirement

---

## 3. CLAIR's Algebraic Structure

### 3.1 What We Have: Two Commutative Monoids

CLAIR has two distinct algebraic structures on [0,1]:

**Derivation Monoid** ([0,1], ×, 1):
- Models sequential/conjunctive derivation
- Confidence can only decrease: c₁ × c₂ ≤ min(c₁, c₂)
- Identity 1 = "no confidence loss"
- Zero 0 absorbs (complete defeat)

**Aggregation Monoid** ([0,1], ⊕, 0):
- Models combining independent evidence
- Confidence increases: c₁ ⊕ c₂ ≥ max(c₁, c₂)
- Identity 0 = "no evidence"
- One 1 absorbs (complete confidence)

### 3.2 What We Don't Have: Distributivity

**Theorem**: × and ⊕ do not distribute over each other.

**Proof** (by counterexample):
Let a = b = c = 0.5.
- a × (b ⊕ c) = 0.5 × (0.5 + 0.5 - 0.25) = 0.5 × 0.75 = 0.375
- (a × b) ⊕ (a × c) = 0.25 + 0.25 - 0.0625 = 0.4375
- 0.375 ≠ 0.4375 ∎

This failure is *semantically correct*:
- Deriving then aggregating is not the same as aggregating then deriving
- The operations have different epistemic meanings

### 3.3 Additional Structure: Ordering and Duality

**Ordering**: [0,1] has a natural total order compatible with both monoids:
- a ≤ b implies a × c ≤ b × c (× monotone)
- a ≤ b implies a ⊕ c ≤ b ⊕ c (⊕ monotone)

**De Morgan Duality**:
```
a ⊕ b = 1 - (1-a) × (1-b)
```

The operations are De Morgan duals via the symm operation (1 - x).

**Complementation**: The symm function connects the monoids:
- symm : [0,1] → [0,1]
- symm(x) = 1 - x
- symm is an involution: symm(symm(x)) = x
- symm swaps the identities: symm(0) = 1, symm(1) = 0
- symm relates the operations: a ⊕ b = symm(symm(a) × symm(b))

### 3.4 Formal Definition: CLAIR Confidence Algebra

**Definition** (CLAIR Confidence Algebra):
A CLAIR Confidence Algebra is a tuple (C, ×, ⊕, ¬, 0, 1) where:
1. (C, ×, 1) is a commutative monoid with absorbing element 0
2. (C, ⊕, 0) is a commutative monoid with absorbing element 1
3. ¬ : C → C is an involution (¬¬a = a)
4. ¬ exchanges identities: ¬0 = 1 and ¬1 = 0
5. De Morgan law: a ⊕ b = ¬(¬a × ¬b)
6. (C, ≤) is a bounded lattice with 0 as bottom and 1 as top
7. Both × and ⊕ are monotone with respect to ≤

**Note**: Distributivity is explicitly NOT required.

### 3.5 Comparison with Known Structures

| Structure | × | ⊕ | Distributivity | CLAIR? |
|-----------|---|---|----------------|--------|
| Semiring | ✓ | ✓ | × over ⊕ | ✗ |
| DRL | ✓ | ✓ | × over ⊕ (partial) | Close |
| Bimonoid | ✓ | ✓ | Not required | ✓ |
| LDC | ✓ | ✓ | Linear only | Overkill |
| Boolean algebra | ∧ | ∨ | Full | ✗ (graded) |
| MV-algebra | ⊗ | ⊕ | Full | ✗ |

CLAIR's confidence algebra is closest to a **De Morgan bimonoid with order**.

---

## 4. Implications for Type System

### 4.1 The Two-Sorted Grading Approach

Since × and ⊕ serve different purposes, we should track them separately in the type system:

**Graded Types with Two Grades**:
```
Belief<A>[c_deriv, c_agg]
```

Where:
- `c_deriv` is the derivation-path confidence (composed via ×)
- `c_agg` is the aggregation-path confidence (composed via ⊕)

**Alternative**: Single confidence with operation-specific typing rules that prevent mixing contexts inappropriately.

### 4.2 Typing Rules with Dual Grading

**Derivation** (uses ×):
```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ ⊢ e₂ : Belief<A → B>[c₂]
─────────────────────────────────────────────────────── [→E]
        Γ, Δ ⊢ e₂ e₁ : Belief<B>[c₁ × c₂]
```

**Aggregation** (uses ⊕):
```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ ⊢ e₂ : Belief<A>[c₂]    independent(e₁, e₂)
─────────────────────────────────────────────────────────────────────── [Agg]
            Γ, Δ ⊢ aggregate(e₁, e₂) : Belief<A>[c₁ ⊕ c₂]
```

**Key constraint**: We never need to distribute × over ⊕ or vice versa because:
- Derivation chains never branch into independent evidence
- Aggregation never applies within a single derivation path

The type system naturally keeps the operations separate.

### 4.3 Context Operations

In standard graded type theory, contexts are combined using semiring operations:
- Branching: Γ + Δ (pointwise addition)
- Composition: r · Γ (scalar multiplication)

For CLAIR's dual-monoid structure:

**Derivation contexts** (composition within a derivation):
- Context multiplication: Γ ×_ctx Δ applies × to shared variables
- Scalar multiplication: c ×_ctx Γ scales all grades by c

**Aggregation contexts** (independent evidence):
- Context aggregation: Γ ⊕_ctx Δ applies ⊕ to shared variables
- Only valid when evidence is independent

**Crucially**: We never need Γ ×_ctx (Δ ⊕_ctx Θ) because derivation and aggregation operate at different levels.

### 4.4 Well-Formedness Condition

A CLAIR typing derivation is well-formed if:
1. × is only used to combine confidences along derivation paths
2. ⊕ is only used to combine confidences from independent evidence
3. No derivation mixes × and ⊕ on the same confidence value

This structural constraint makes distributivity irrelevant.

---

## 5. Formal Characterization

### 5.1 Definition: Graded Type Theory over a De Morgan Bimonoid

**Definition** (De Morgan Bimonoid):
A De Morgan bimonoid is a tuple (R, ⊗, ⊕, ¬, 1_⊗, 0_⊕) where:
- (R, ⊗, 1_⊗) is a commutative monoid (derivation)
- (R, ⊕, 0_⊕) is a commutative monoid (aggregation)
- ¬ : R → R is an involution
- ¬1_⊗ = 0_⊕ and ¬0_⊕ = 1_⊗
- a ⊕ b = ¬(¬a ⊗ ¬b) (De Morgan law)

**Note**: No distributivity required.

### 5.2 Standard Model

The standard model is ([0,1], ×, ⊕, symm, 1, 0) where:
- × is standard multiplication
- ⊕ is probabilistic OR: a ⊕ b = a + b - ab
- symm(x) = 1 - x

This satisfies all De Morgan bimonoid axioms.

### 5.3 Finite Models

For decidable type checking (CPL-finite), we need finite models.

**L₅ Model**: ({0, 0.25, 0.5, 0.75, 1}, ×_L, ⊕_L, symm, 1, 0)

Operations with floor/ceiling:
- a ×_L b = floor_L(a × b)
- a ⊕_L b = ceil_L(a ⊕ b)

The De Morgan law must be verified for discrete operations.

### 5.4 Categorical Semantics

**Claim**: CLAIR types form a graded category over a De Morgan bimonoid.

Objects: Types A, B, C, ...
Morphisms: Graded functions f : A →[c] B (meaning f transforms type A to Belief<B>[c])
Composition: f ∘ g : A →[c₁ × c₂] C (derivation chains multiply)
Parallel: f ⊕ g : A →[c₁ ⊕ c₂] B (independent evidence aggregates)

The key is that composition and parallel combination are separate operations—they never need to interact via distributivity.

---

## 6. Lean Formalization Design

### 6.1 Current State

The Lean formalization (formal/lean/CLAIR/Confidence/) already captures:
- Confidence as unitInterval
- × via Mathlib's monoid structure
- ⊕ via CLAIR.Confidence.Oplus
- De Morgan duality (theorem oplus_eq_one_sub_mul_symm)
- Non-distributivity (documented but not proven as theorem)

### 6.2 Proposed Additions

**1. De Morgan Bimonoid typeclass**:
```lean
class DeMorganBimonoid (R : Type*) extends
    CommMonoid R,     -- (R, ⊗, 1)
    AddCommMonoid R,  -- (R, ⊕, 0)
    Inv R where       -- ¬
  inv_inv : ∀ a : R, a⁻¹⁻¹ = a
  inv_one : (1 : R)⁻¹ = 0
  inv_zero : (0 : R)⁻¹ = 1
  de_morgan : ∀ a b : R, a + b = (a⁻¹ * b⁻¹)⁻¹
```

**2. Non-distributivity theorem**:
```lean
theorem not_distrib : ¬∀ a b c : Confidence,
    a * (b ⊕ c) = (a * b) ⊕ (a * c) := by
  push_neg
  use ⟨0.5, by norm_num⟩, ⟨0.5, by norm_num⟩, ⟨0.5, by norm_num⟩
  norm_num [oplus]
```

**3. Ordering compatibility**:
```lean
instance : OrderedCommMonoid Confidence := ...
theorem oplus_mono : Monotone₂ (· ⊕ ·) := ...
```

### 6.3 Integration with Belief Type

The Belief type (CLAIR/Belief/Basic.lean) already uses × for derivation. To add aggregation:

```lean
/-- Aggregate independent beliefs -/
def aggregate (b₁ b₂ : Belief α) : Belief α :=
  ⟨b₁.value,  -- assume same value for aggregation
   b₁.confidence ⊕ b₂.confidence⟩

theorem aggregate_confidence (b₁ b₂ : Belief α) :
    (aggregate b₁ b₂).confidence = b₁.confidence ⊕ b₂.confidence := rfl
```

---

## 7. Open Questions

### 7.1 Theoretical Questions

1. **Is De Morgan bimonoid the right abstraction?**
   - It captures ×, ⊕, and their duality
   - But is there a more natural categorical characterization?

2. **Connection to linear logic**:
   - Is CLAIR a fragment of multiplicative-additive linear logic?
   - Can we use linear logic's proof nets for CLAIR derivations?

3. **Other t-norm/t-conorm pairs**:
   - Would Łukasiewicz (a ⊗ b = max(0, a+b-1), a ⊕ b = min(1, a+b)) work better?
   - Trade-offs with product t-norm

### 7.2 Practical Questions

1. **Type inference**:
   - Can confidence grades be inferred when × and ⊕ are separate?
   - What's the decidability of type checking?

2. **Subtyping**:
   - Should Belief<A>[c] be subtype of Belief<A>[c'] when c ≥ c'?
   - Does dual-monoid grading affect subtyping rules?

3. **Error messages**:
   - How to report errors when operations are mixed inappropriately?

---

## 8. Conclusions

### 8.1 Key Findings

1. **Non-distributivity is fundamental**: CLAIR's × and ⊕ don't distribute, and this is mathematically expected for t-norm/t-conorm pairs.

2. **De Morgan bimonoid is the right structure**: CLAIR's confidence algebra is a De Morgan bimonoid—two monoids connected by an involution but without distributivity.

3. **Type system naturally separates operations**: Derivation and aggregation operate at different levels, so distributivity is never needed in practice.

4. **Prior art supports this approach**: Double Residuated Lattices, linearly distributive categories, and bimonoids all address similar non-distributive structures.

5. **Lean formalization is straightforward**: The current formalization already has the pieces; we just need to add the De Morgan bimonoid structure explicitly.

### 8.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Non-distributivity is fundamental | 0.95 | Mathematical proof, t-norm theory |
| De Morgan bimonoid characterizes CLAIR | 0.85 | Captures all operations and duality |
| Type system doesn't need distributivity | 0.90 | Structural separation of operations |
| Lean formalization is straightforward | 0.80 | Pieces exist, integration needed |
| This is novel for graded type theory | 0.70 | Not found in standard literature |

### 8.3 Recommendations

1. **Add De Morgan bimonoid to Lean formalization** as a typeclass
2. **Prove non-distributivity** as a formal theorem
3. **Document the two-operation separation** in typing rules
4. **Explore connection to linear logic** for deeper categorical semantics
5. **Consider alternative t-norm pairs** for different applications

---

## 9. Impact on Other Threads

### Thread 8 (Formal Verification)
- Add DeMorganBimonoid typeclass
- Prove not_distrib theorem
- Extend Belief type with aggregation

### Thread 7 (Implementation)
- Runtime can use separate tracking for × and ⊕ compositions
- No distributivity simplifies confidence computation

### Thread 2.23 (Subtyping)
- Dual-monoid structure affects how subtyping interacts with confidence bounds

### Thread 2.24 (Type Inference)
- Separation of operations may simplify inference
- Each operation has clear propagation rules

---

## 10. References

### Primary Sources

- **Orłowska, E. & Radzikowska, A.M.** (2002). "Double Residuated Lattices and Their Applications." *Relational Methods in Computer Science*, LNCS 2561.

- **Cockett, R. & Seely, R.** (1997). "Weakly Distributive Categories." *J. Pure Appl. Algebra* 114(2), 133-173.

- **Orchard, D., Liepelt, V., & Eades, H.** (2019). "Quantitative Program Reasoning with Graded Modal Types." *ICFP 2019*.

- **Gaboardi, M., Katsumata, S., Orchard, D., Breuvart, F., & Uustalu, T.** (2016). "Combining Effects and Coeffects via Grading." *ICFP 2016*.

- **Klement, E.P., Mesiar, R., & Pap, E.** (2000). *Triangular Norms*. Springer.

### nLab Entries

- [Graded monad](https://ncatlab.org/nlab/show/graded+monad)
- [Linearly distributive category](https://ncatlab.org/nlab/show/linearly+distributive+category)
- [Graded monoid](https://ncatlab.org/nlab/show/graded+monoid)

### CLAIR Internal

- Thread 2.22: exploration/thread-2.22-curry-howard-terms.md
- Thread 8: exploration/thread-8-verification.md
- Lean formalization: formal/lean/CLAIR/Confidence/

---

*Thread 2.25 Status: Substantially explored. De Morgan bimonoid identified as the right algebraic structure. Ready for Lean formalization.*
