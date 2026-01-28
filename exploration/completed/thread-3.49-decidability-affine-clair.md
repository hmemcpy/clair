# Thread 3.49: Decidability of Affine CLAIR Type Checking

> **Status**: Active exploration (Session 74)
> **Task**: 3.49 Prove decidability of type checking for CLAIR with affine evidence types
> **Question**: Is it decidable whether a CLAIR expression is well-typed under affine evidence discipline?
> **Prior Work**: Thread 3.46 (epistemic linearity), Thread 3.48 (linearity × defeat), Thread 3.16 (CPL decidability)

---

## 1. The Question Precisely

### 1.1 What We're Asking

Given:
- A CLAIR expression `e`
- A typing context `Γ` (unrestricted) and `Δ` (affine)
- A claimed type `A`
- A claimed confidence bound `c`

**Question**: Is it decidable whether `Γ; Δ ⊢ e : A @c` holds?

This is the **type checking problem** for affine CLAIR. A stronger question is **type inference**: given `e`, can we compute `Γ`, `Δ`, `A`, and `c` (or determine none exist)?

### 1.2 Why This Matters

Decidability of type checking is foundational:
- If undecidable, CLAIR cannot be implemented as a practical language
- Even partial decidability (decidable fragments) would constrain the design
- Undecidability results tell us what features interact dangerously

### 1.3 Scope Clarification

We're asking about **type checking**, not:
- **Validity checking** in CPL (already known likely undecidable per Thread 3.16)
- **Semantic questions** like "does this belief track truth?"
- **Runtime properties** like termination

Type checking is syntactic: can we verify the typing derivation?

---

## 2. Background: What Makes Type Checking Decidable?

### 2.1 Simply Typed Lambda Calculus

The simply typed lambda calculus (STLC) has decidable type checking:

**Algorithm**:
1. For each subexpression, compute or check its type
2. For application `e₁ e₂`, check `e₁ : A → B` and `e₂ : A`
3. For abstraction `λx:A. e`, check `e : B` under extended context
4. All operations are structural recursion over the syntax tree

**Complexity**: O(n) where n is expression size (assuming constant-time type comparisons).

### 2.2 Linear/Affine Type Checking

Linear type systems add resource tracking but remain decidable:

**Key mechanism**: Context splitting
- When type checking `(e₁, e₂)`, split context: `Δ = Δ₁ ⊎ Δ₂`
- Check `Δ₁ ⊢ e₁ : A` and `Δ₂ ⊢ e₂ : B`
- The split must be **disjoint** (affine resources used at most once)

**Challenge**: Non-determinism in context splitting
- Multiple ways to split context
- Need to find a valid split or prove none exists

**Solution**: Bidirectional type checking with resource tracking
- Track which resources each subterm uses
- Propagate usage information bottom-up
- Check consistency at sharing points

**Complexity**: O(n²) or O(n³) depending on algorithm (Walker 2005)

### 2.3 What Can Make Type Checking Undecidable?

Known sources of undecidability:

1. **Unrestricted recursion in types**: If types can be infinitely recursive without bounds, type equality becomes undecidable

2. **Dependent types with strong computation**: Checking `e : A` may require evaluating `A`, which may not terminate

3. **Subtyping with self-reference**: Certain subtyping rules with recursive types are undecidable (Amadio & Cardelli 1993)

4. **Higher-order unification**: Type inference with higher-order types requires higher-order unification, which is undecidable (Huet 1973)

5. **Intersection/union types without restrictions**: Full intersection types make type checking undecidable

---

## 3. CLAIR's Type System Features

Let me catalog CLAIR's features that could affect decidability:

### 3.1 Affine Evidence Contexts

From Thread 3.46:
```
Γ; Δ ⊢ e : A @c
```

- `Γ`: Unrestricted context (evidence marked with !)
- `Δ`: Affine context (each evidence used at most once)

**Context splitting rule** (for aggregation):
```
Γ; Δ₁ ⊢ e₁ : Belief<A> @c₁    Γ; Δ₂ ⊢ e₂ : Belief<A> @c₂    Δ₁ ∩ Δ₂ = ∅
─────────────────────────────────────────────────────────────────────────
        Γ; Δ₁ ∪ Δ₂ ⊢ aggregate(e₁, e₂) : Belief<A> @(c₁ ⊕ c₂)
```

**Analysis**: This is standard affine type checking. The disjointness check `Δ₁ ∩ Δ₂ = ∅` is decidable (finite contexts).

### 3.2 Confidence Bounds

Confidence appears in types: `Belief<A>[c]` where `c ∈ [0,1]`.

**Operations on confidence**:
- Derivation: `c₁ × c₂`
- Aggregation: `c₁ ⊕ c₂ = c₁ + c₂ - c₁×c₂`
- Undercut: `c × (1 - d)`
- Rebut: `c_for / (c_for + c_against)`

**Key design decision**: CLAIR uses **rational numbers** (ℚ) for confidence:
```lean
-- From Lean formalization
structure ConfBound where
  val : ℚ
  h_nonneg : 0 ≤ val
  h_le_one : val ≤ 1
```

**Analysis**: All confidence operations on ℚ are computable:
- Addition, multiplication, subtraction: exact in ℚ
- Division (for rebut): exact in ℚ (except division by zero, handled specially)
- Comparison (for subtyping): exact in ℚ

If CLAIR used real numbers ℝ, confidence comparisons might be undecidable. With ℚ, they're decidable.

### 3.3 Confidence Subtyping

```
c ≥ c'
─────────────────────────────────────────
Belief<A>[c] <: Belief<A>[c']
```

Higher confidence is a subtype (can be weakened to lower).

**Analysis**: Subtype checking reduces to rational comparison, which is decidable.

### 3.4 Stratification Levels

From Thread 3's stratification:
```
Meta<A>[n][c]  -- Belief about A at level n with confidence c
```

**Introspection rule**:
```
Γ; Δ ⊢ b : StratifiedBelief<m, A> @c    m < n
───────────────────────────────────────────────
Γ; Δ ⊢ introspect(b) : StratifiedBelief<n, Meta<A>> @g(c)
```

**Analysis**: Level comparison `m < n` is decidable (natural numbers). The Löb discount `g(c) = c²` is computable in ℚ.

### 3.5 Defeat Operations

**Undercut**:
```
Γ; Δ₁ ⊢ D : Belief<A> @c    Γ; Δ₂ ⊢ d : AffEvidence<Attacks(D)> @d_conf
────────────────────────────────────────────────────────────────────────
Γ; Δ₁, Δ₂ ⊢ undercut(D, d) : Belief<A> @(c × (1 - d_conf))
```

**Analysis**: Requires:
1. Type checking the belief D and defeater d
2. Checking that d's type is `AffEvidence<Attacks(D)>` — but `Attacks(D)` is a type-level predicate

**Potential issue**: What is `Attacks(D)`? If it requires semantic analysis, could be undecidable. If syntactic, decidable.

**Resolution**: In CLAIR's design, `Attacks` should be a **syntactic** type family:
```
Attacks(Belief<A>) = UndercutsA | RebutsA
```
The attack relationship is determined by the type structure, not semantic content.

### 3.6 Summary Table

| Feature | Decidability Impact |
|---------|---------------------|
| Affine contexts | Decidable (standard linear checking) |
| Context splitting | Decidable (finite contexts) |
| Confidence bounds (ℚ) | Decidable (rational arithmetic) |
| Confidence subtyping | Decidable (rational comparison) |
| Stratification levels | Decidable (natural number comparison) |
| Defeat operations | Decidable (if Attacks is syntactic) |
| Exponential (!) | Decidable (standard linear logic) |

---

## 4. The Type Checking Algorithm

### 4.1 Bidirectional Approach

Following standard practice (Pierce & Turner 2000), use bidirectional type checking:

**Two modes**:
- **Checking**: Given `Γ; Δ ⊢ e : A @c`, verify the judgment
- **Synthesis**: Given `Γ; Δ` and `e`, compute `A` and `c`

**Key rules**:

```
SYNTHESIS:
─────────────────────────────────────────
Γ; Δ, x : A @c ⊢_synth x : A @c ⇒ uses {x}

Γ; Δ ⊢_synth e₁ : (A → B) @c₁ ⇒ U₁    Γ; Δ ⊢_check e₂ : A @c₂ ⇒ U₂
U₁ ∩ U₂ = ∅   (affine disjointness)
──────────────────────────────────────────────────────────────────────
Γ; Δ ⊢_synth (e₁ e₂) : B @(c₁ × c₂) ⇒ U₁ ∪ U₂

CHECKING:
Γ; Δ, x : A @c ⊢_check e : B @c' ⇒ U
────────────────────────────────────────
Γ; Δ ⊢_check (λx. e) : (A → B) @c' ⇒ U \ {x}

Γ; Δ ⊢_synth e : A' @c'    A' <: A    c' ≥ c
────────────────────────────────────────────────
Γ; Δ ⊢_check e : A @c ⇒ U
```

### 4.2 Resource Tracking

The algorithm tracks **usage sets** U ⊆ dom(Δ):
- Each variable in Δ is used at most once
- At sharing points (pair, application), check disjointness
- At the end, all required variables should be used (if relevant) or unused is OK (affine)

### 4.3 Pseudocode

```
typecheck(Γ, Δ, e, A, c):
  match e with
  | var(x) →
      if (x : A' @c') ∈ Δ:
        check A' <: A and c' ≥ c
        return {x}
      elif (x : A' @c') ∈ Γ:
        check A' <: A and c' ≥ c
        return {}
      else fail

  | app(e₁, e₂) →
      (A₁ @c₁, U₁) ← synth(Γ, Δ, e₁)
      match A₁ with
      | Arrow(A_arg, A_res) →
          check A_res <: A and c₁ ≥ c
          U₂ ← check(Γ, Δ, e₂, A_arg, 1)  -- require c=1 for argument
          if U₁ ∩ U₂ ≠ ∅: fail "affine violation"
          return U₁ ∪ U₂
      | _ → fail "expected function type"

  | belief(v, c_val, j) →
      match A with
      | Belief(A', c_bound) →
          check c_val ≥ c_bound
          U ← check(Γ, Δ, v, A', 1)
          return U
      | _ → fail "expected belief type"

  | aggregate(e₁, e₂) →
      match A with
      | Belief(A', c_bound) →
          (Belief(A'₁, c₁), U₁) ← synth(Γ, Δ, e₁)
          (Belief(A'₂, c₂), U₂) ← synth(Γ, Δ, e₂)
          check A'₁ = A'₂ = A'
          check (c₁ ⊕ c₂) ≥ c_bound
          if U₁ ∩ U₂ ≠ ∅: fail "evidence used twice"
          return U₁ ∪ U₂
      | _ → fail "expected belief type"

  | undercut(D, d) →
      match A with
      | Belief(A', c_bound) →
          (Belief(A'', c_D), U_D) ← synth(Γ, Δ, D)
          check A'' = A'
          (_, c_d), U_d) ← synth(Γ, Δ, d)  -- d : Evidence<Attacks(D)>
          check (c_D × (1 - c_d)) ≥ c_bound
          if U_D ∩ U_d ≠ ∅: fail "evidence conflict"
          return U_D ∪ U_d
      | _ → fail "expected belief type"

  | introspect(b, n) →
      match A with
      | StratifiedBelief(n', Meta(A')) →
          check n = n'
          (StratifiedBelief(m, A''), c_b), U) ← synth(Γ, Δ, b)
          check A' = A''
          check m < n  -- stratification constraint
          check g(c_b) ≥ c  -- Löb discount
          return U
      | _ → fail "expected stratified belief"
```

### 4.4 Complexity Analysis

**Claim**: Type checking is O(n² × m) where:
- n = size of expression
- m = size of type annotations

**Breakdown**:
- Traversal: O(n)
- At each node:
  - Type comparison: O(m)
  - Confidence arithmetic: O(1) for fixed-precision ℚ
  - Usage set operations: O(|Δ|) = O(n)
- Total: O(n × (m + n)) = O(n²) assuming m = O(n)

**Subtyping**: Each subtype check is O(m). At most O(n) checks. Total O(n × m).

**Resource tracking**: Usage sets are at most size |Δ| ≤ n. Set operations (union, intersection, difference) are O(n). At most O(n) operations. Total O(n²).

---

## 5. Potential Obstacles to Decidability

### 5.1 Could Confidence Arithmetic Be Undecidable?

**Concern**: If confidence were real numbers ℝ, comparisons might be undecidable (computing whether two reals are equal is undecidable in general).

**Resolution**: CLAIR uses ℚ. All required operations are decidable:
- Rational arithmetic: decidable (exact)
- Rational comparison: decidable (exact)

**Note**: The Lean formalization uses Mathlib's `unitInterval` which is based on ℝ, but all CLAIR operations produce rational results when given rational inputs. The type system could be specified over ℚ explicitly.

### 5.2 Could Subtyping Be Undecidable?

**Concern**: Some subtyping systems are undecidable (e.g., F<: with some extensions).

**CLAIR's subtyping**:
```
c ≥ c' → Belief<A>[c] <: Belief<A>[c']
A <: A' → A' → B <: A → B  (contravariant)
B <: B' → A → B <: A → B'  (covariant)
```

**Analysis**: CLAIR's subtyping is:
- Based on numerical comparison (decidable for ℚ)
- Structurally recursive (decidable)
- No recursive types or impredicative polymorphism

**Conclusion**: Subtyping is decidable, O(m) per check.

### 5.3 Could Context Splitting Be Undecidable?

**Concern**: Finding the right context split could be NP-hard or worse.

**Analysis**: For affine types, context splitting is local to each syntactic construct:
- Each variable is used by exactly one subexpression (or none)
- The split is determined by which subexpression uses which variable
- Propagate usage information bottom-up

**Resolution**: Context splitting doesn't require search; it's computed deterministically bottom-up.

### 5.4 Could Stratification Levels Cause Problems?

**Concern**: Level constraints might interact badly.

**Analysis**: Levels are natural numbers with simple constraints:
- `introspect` requires `m < n`
- All other operations preserve levels

No arithmetic on levels beyond comparison. No level polymorphism. Decidable.

### 5.5 Could Type-Level Computation Be Undecidable?

**Concern**: Some dependent type systems require computation during type checking.

**CLAIR's type-level operations**:
- Confidence: arithmetic (+, ×, ⊕), but only on constants
- Stratification: comparison (<), but only on constants
- No type-level functions, no type-level recursion

**Analysis**: CLAIR has **indexed types** (like `Belief<A>[c]`), not **full dependent types**. The indices are computed at term level and checked at type level, but no unbounded computation at type level.

**Conclusion**: No type-level computation issues.

---

## 6. Formal Decidability Argument

### 6.1 Theorem Statement

**Theorem (Decidability of Affine CLAIR Type Checking)**:
Given:
- Expression `e` over CLAIR syntax
- Unrestricted context `Γ`
- Affine context `Δ`
- Type `A`
- Confidence bound `c ∈ ℚ ∩ [0,1]`

It is decidable whether `Γ; Δ ⊢ e : A @c` holds.

### 6.2 Proof Strategy

**Approach**: Structural induction on the expression `e`, showing each case reduces to decidable subproblems.

### 6.3 Proof Sketch

**Base cases**:

*Variables*:
- Check if `x` is in `Γ` or `Δ` with appropriate type
- Context lookup: decidable (finite lists)
- Subtype check: decidable (structural recursion + rational comparison)

*Literals*:
- Type is determined: `Nat`, `Bool`, etc.
- Confidence is 1
- Trivially decidable

**Inductive cases**:

*Application (e₁ e₂)*:
- IH: type checking `e₁` and `e₂` is decidable
- Need: `e₁ : A → B` and `e₂ : A`
- Type matching: decidable (structural equality)
- Confidence computation: c₁ × c₂, decidable in ℚ
- Disjointness check: U₁ ∩ U₂ = ∅, decidable (finite sets)

*Abstraction (λx:A. e)*:
- IH: type checking `e` under extended context is decidable
- Extension: add `x : A` to context, decidable
- Form result type: A → B, decidable

*Belief construction*:
- IH: type checking value is decidable
- Confidence comparison: decidable in ℚ

*Aggregation*:
- IH: type checking both arguments is decidable
- Confidence computation: c₁ ⊕ c₂ = c₁ + c₂ - c₁×c₂, decidable in ℚ
- Disjointness: decidable

*Undercut/Rebut*:
- IH: type checking operands is decidable
- Confidence computation: c × (1 - d), decidable in ℚ
- Attack relationship: syntactically determined, decidable

*Introspection*:
- IH: type checking inner belief is decidable
- Level constraint: m < n, decidable in ℕ
- Löb discount: g(c) = c², decidable in ℚ

**All cases reduce to**:
1. Recursive type checking (IH)
2. Type/context operations (finite, structural)
3. Rational arithmetic (decidable)
4. Set operations on finite sets (decidable)

**QED** (sketch). ∎

### 6.4 Complexity

**Theorem (Polynomial Complexity)**:
Type checking affine CLAIR expressions is in **PTIME**, specifically O(n² × m) where n = |e| and m = max type size.

**Proof sketch**:
- Single traversal of expression: O(n)
- Each node: O(n + m) operations (usage tracking + type comparison)
- No exponential blowup (no backtracking required for context splitting)
- All arithmetic is polynomial in representation size

---

## 7. Comparison to CPL Decidability

### 7.1 Why CPL is (Likely) Undecidable

Thread 3.16 established that CPL (Confidence-bounded Provability Logic) is likely undecidable because:
- It combines transitivity (axiom 4) with continuous [0,1] values
- This matches Vidal (2019)'s undecidability pattern for modal many-valued logics

### 7.2 Why Type Checking is Different

**Key distinction**: CPL asks about **validity**—is a formula true in all models? Type checking asks about **derivability**—can we construct a typing derivation?

| Aspect | CPL Validity | Type Checking |
|--------|-------------|---------------|
| Question | Is φ valid? | Is Γ; Δ ⊢ e : A derivable? |
| Method | Check all models | Construct derivation |
| Infinity | Infinitely many models | Finite derivation tree |
| Arithmetic | Continuous comparisons | Discrete rational checks |

**Why this matters**:
- CPL validity requires reasoning about all possible worlds with continuous confidence
- Type checking only examines the given expression and context
- Type derivations are finite (bounded by expression size)
- Confidence values in type checking are finitely many (from the expression)

### 7.3 The Decidability Gap

```
CPL Validity:      Likely Undecidable
                       |
                       | (different problems)
                       v
Type Checking:     Decidable (proven above)
```

This is analogous to:
- First-order arithmetic validity: Undecidable
- First-order type checking: Decidable

The type system enforces constraints but doesn't require solving arbitrary arithmetic formulas.

---

## 8. Extensions and Boundaries

### 8.1 What Extensions Preserve Decidability?

**Polymorphism (System F style)**:
- Rank-1 polymorphism: Decidable with Hindley-Milner
- Higher-rank: Requires annotations, but checking is decidable
- Impredicative: Can become undecidable

**Recommendation**: CLAIR can safely add rank-1 polymorphism.

**Recursive types (iso-recursive)**:
- With explicit fold/unfold: Decidable
- Equi-recursive: Type equality becomes co-induction, still decidable

**Recommendation**: CLAIR can add iso-recursive types.

**Gradual typing**:
- Adds dynamic type casts
- Type checking remains decidable (casts checked at runtime)

**Recommendation**: Aligns with Task 3.50 (gradual linearity).

### 8.2 What Extensions Would Break Decidability?

**Full dependent types**:
- Type checking requires evaluation
- Evaluation may not terminate
- Would need termination checking (like Agda) or stratification (like Lean)

**Recommendation**: Avoid full dependent types, or require totality.

**Type-level computation with ⊕ and ×**:
- If types could include `c₁ ⊕ c₂` where c₁, c₂ are computed at type level
- Would need to solve equations over (⊕, ×) algebra
- Potentially undecidable (encodes arithmetic)

**Recommendation**: Confidence in types should be literals or variables, not computed expressions.

**Infinite contexts**:
- If Γ or Δ could be infinite (e.g., quantified over all evidence)
- Finiteness is essential for decidability

**Recommendation**: Keep contexts finite (syntactically bounded).

### 8.3 The Safety Boundary

```
DECIDABLE:
  - Affine/linear types
  - Confidence bounds (ℚ literals)
  - Stratification (ℕ literals)
  - Rank-1 polymorphism
  - Iso-recursive types
  - Gradual typing

POTENTIALLY UNDECIDABLE:
  - Full dependent types
  - Type-level confidence arithmetic
  - Impredicative polymorphism
  - Infinite contexts
```

---

## 9. Implementation Considerations

### 9.1 Lean Formalization Status

The current Lean formalization (formal/lean/CLAIR/) includes:
- Type syntax with confidence bounds
- Typing judgment `HasType Γ e A c`
- Subtyping relation `Subtype A B`

**Not yet formalized**:
- Affine context splitting explicitly
- Decidability proof as a computable function
- Type checking algorithm returning `Decidable (HasType Γ e A c)`

### 9.2 Decidability in Lean 4

To prove decidability in Lean 4, we would:

```lean
-- Decidability instance for type checking
instance : Decidable (HasType Γ Δ e A c) := by
  -- Case analysis on e
  induction e with
  | var x =>
    -- Check if x is in context with appropriate type
    exact decidable_of_iff (∃ A' c', lookup Δ x = some (A', c') ∧ Subtype A' A ∧ c' ≥ c) sorry
  | app e₁ e₂ ih₁ ih₂ =>
    -- Use induction hypotheses
    sorry
  -- ... other cases
```

This would be the content of Task 3.47 (Affine types in Lean).

### 9.3 Error Messages

A good implementation should produce helpful error messages:

```
Error: Affine evidence 'witness_testimony' used twice
  First use: line 12, in derivation of 'suspect_guilty'
  Second use: line 15, in derivation of 'suspect_present'

  Consider:
  - Mark as exponential (!witness_testimony) if genuinely reusable
  - Split evidence if it contains multiple independent claims
```

---

## 10. Open Questions

### 10.1 Optimal Complexity

**Question**: Is O(n²) optimal, or can we achieve O(n log n) or O(n)?

Linear type checking for simple linear lambda calculus can be O(n) with careful implementation. CLAIR's additional features (confidence, stratification) might add overhead.

### 10.2 Inference vs. Checking

**Question**: How much can be inferred vs. required as annotations?

- Type annotations on λ-binders: Required (standard)
- Confidence bounds: Could potentially be inferred (compute from leaves)
- Stratification levels: Could be inferred (propagate constraints)

Full inference would be nice for ergonomics but adds complexity.

### 10.3 Incremental Type Checking

**Question**: Can we type check incrementally when code changes?

For IDE integration, incremental checking would be valuable. The bottom-up nature of the algorithm suggests it's amenable to memoization.

---

## 11. Connections to Prior Work

### 11.1 Walker (2005) - Substructural Type Systems

Walker's comprehensive treatment of substructural types in "Advanced Topics in Types and Programming Languages" establishes that:
- Linear type checking is decidable
- Affine type checking is decidable
- The algorithms are polynomial time

CLAIR's affine evidence follows this pattern directly.

### 11.2 Pierce & Turner (2000) - Local Type Inference

Bidirectional type checking provides a practical framework:
- Checking mode: verify given type
- Synthesis mode: compute type
- Local annotations sufficient for decidability

CLAIR can adopt this approach.

### 11.3 Cervesato & Pfenning (2002) - Linear Logic Programming

Their work on linear logic programming (Lolli, LLF) shows:
- Resource tracking can be done efficiently
- Context splitting is deterministic with proper bookkeeping

CLAIR's evidence tracking follows similar principles.

### 11.4 Vidal (2019) - Many-Valued Modal Logic

Crucially, Vidal's undecidability result for transitive many-valued modal logic does NOT apply to type checking because:
- Type checking is derivation construction, not validity checking
- We don't need to check all models, just the given expression
- Confidence values are finitely given, not universally quantified

---

## 12. Conclusions

### 12.1 Summary

**Task 3.49 is substantially answered: Affine CLAIR type checking is decidable.**

The key findings:

1. **Decidability holds** because:
   - Affine type checking is fundamentally structural
   - Confidence arithmetic over ℚ is decidable
   - Stratification uses decidable constraints
   - No unbounded type-level computation

2. **Complexity is polynomial**: O(n²) in expression size

3. **This is distinct from CPL decidability**: Type checking ≠ validity checking

4. **Safe extension boundary identified**: Rank-1 polymorphism and iso-recursive types are safe; full dependent types are not

### 12.2 Key Theorem

**Theorem (Decidability of Affine CLAIR Type Checking)**:
For any CLAIR expression e, contexts Γ and Δ, type A, and rational confidence bound c, it is decidable whether Γ; Δ ⊢ e : A @c holds. The decision procedure runs in polynomial time.

### 12.3 Confidence Table

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Affine type checking is decidable | 0.95 | Standard result, extended to CLAIR |
| Complexity is O(n²) | 0.85 | Analysis above, not fully formalized |
| ℚ confidence is essential | 0.90 | ℝ would introduce undecidability |
| Distinct from CPL decidability | 0.95 | Different problems entirely |
| Safe extensions identified correctly | 0.80 | Based on literature, not exhaustive |

### 12.4 Impact on CLAIR

This exploration:
- **Confirms CLAIR is implementable** as a practical language
- **Justifies the ℚ design choice** for confidence bounds
- **Provides algorithm outline** for implementation
- **Identifies safe extension boundary** for future development

### 12.5 New Questions Raised

- **3.47 (clarified)**: The Lean formalization should include a computable `decide` function
- **9.X**: What is the practical performance of type checking on realistic programs?
- **9.Y**: Can we achieve better than O(n²) complexity?

---

## 13. References

### CLAIR Internal

- Thread 3.46: exploration/completed/thread-3.46-epistemic-linearity.md
- Thread 3.48: exploration/completed/thread-3.48-linearity-defeat-interaction.md
- Thread 3.16: exploration/completed/thread-3.16-cpl-decidability.md
- Lean formalization: formal/lean/CLAIR/

### External

**Substructural Types**:
- Walker, D. (2005). "Substructural Type Systems." In *Advanced Topics in Types and Programming Languages*, Pierce (ed.)
- [Harvard course notes on substructural types](https://groups.seas.harvard.edu/courses/cs152/2019sp/lectures/lec17-substructural.pdf)

**Bidirectional Type Checking**:
- Pierce, B.C. & Turner, D.N. (2000). "Local Type Inference." *ACM TOPLAS*.
- Dunfield, J. & Krishnaswami, N. (2021). "Bidirectional Typing." *ACM Computing Surveys*.

**Linear Logic Programming**:
- Cervesato, I. & Pfenning, F. (2002). "A Linear Logical Framework." *Information and Computation*.

**Many-Valued Modal Logic (for contrast)**:
- Vidal, A. (2019). "On Transitive Modal Many-Valued Logics." [arXiv:1904.01407](https://arxiv.org/abs/1904.01407)

**Type Checking Complexity**:
- Amadio, R.M. & Cardelli, L. (1993). "Subtyping Recursive Types." *ACM TOPLAS*.

---

*Thread 3.49 Status: Substantially explored. Affine CLAIR type checking is decidable in polynomial time. The key insight is that type checking is structural derivation construction, not semantic validity checking, avoiding the undecidability of CPL. Safe extension boundaries identified. Ready for Lean formalization in Task 3.47.*
