# Thread 3.12: Fixed-Point Computation Complexity

> **Status**: Active exploration (Session 67)
> **Task**: 3.12 How expensive is fixed-point computation? Can some cases be decided at compile time?
> **Question**: What is the computational complexity of CLAIR's fixed-point computation for self-referential beliefs, and which classes of self-reference admit static analysis?
> **Prior Work**: Thread 3 (Safe self-reference characterization), Thread 5.11 (Defeat chain fixed points)

---

## 1. The Problem

### 1.1 Context

Thread 3 established that CLAIR uses **stratification + escape hatch** for self-reference:
- Default: Tarski-style stratification (statically safe)
- Escape hatch: `self_ref_belief` combinator with runtime fixed-point computation

The escape hatch returns:
- `WellFormed(belief)` if a unique fixed point exists
- `Ill_formed(NoFixedPoint)` if no fixed point exists
- `Underdetermined(points)` if multiple fixed points exist

### 1.2 The Questions

1. **Complexity**: What is the computational cost of the fixed-point computation?
2. **Decidability**: Is fixed-point existence decidable? In what fragment?
3. **Static Analysis**: Which cases can be resolved at compile time vs. runtime?
4. **Approximation**: When exact computation is infeasible, what approximations work?

### 1.3 Why This Matters

If fixed-point computation is expensive:
- The `self_ref_belief` escape hatch becomes a performance hazard
- Programs with self-reference might be unpredictably slow
- Type checking could become undecidable in certain fragments

If it's cheap (or decidable in useful fragments):
- CLAIR can offer compile-time guarantees for common patterns
- Runtime overhead is predictable
- Self-reference becomes a practical language feature

---

## 2. The Mathematical Landscape

### 2.1 Different Kinds of Fixed Points

CLAIR needs fixed-point computation in several contexts:

| Context | Domain | Function | Relevant Theory |
|---------|--------|----------|-----------------|
| Defeat chains | [0,1]^n (confidence vectors) | Multiplicative/divisive | Brouwer, Banach (Thread 5.11) |
| Self-referential content | Arbitrary types | User-defined | Kleene, Tarski, Rice |
| Self-referential confidence | [0,1] | Confidence computation | Specialized analysis |
| Type checking | Type environments | Unification | Undecidable in general |

The key distinction is between:
- **Continuous fixed points** on [0,1]^n (guaranteed by Brouwer, computable by iteration)
- **Discrete fixed points** on arbitrary domains (often undecidable)
- **Symbolic fixed points** (may or may not be computable)

### 2.2 Kleene's Fixed-Point Theorems

**Theorem (Kleene's First Recursion Theorem)**: For any continuous function f on a complete partial order (CPO), the least fixed point exists and equals ⊔_n f^n(⊥).

**Theorem (Kleene's Second Recursion Theorem)**: For any total computable function f, there exists an index e such that φ_e = φ_{f(e)}. (Self-referential programs can be constructed.)

**Relevance to CLAIR**:
- The first theorem guarantees existence of fixed points in suitable domains
- The second theorem explains *why* self-reference is powerful (and dangerous)
- Neither theorem gives decidability or complexity bounds

### 2.3 Rice's Theorem and Undecidability

**Theorem (Rice)**: Any non-trivial semantic property of programs is undecidable.

**Corollary**: The following are undecidable for general `self_ref_belief`:
- Does a fixed point exist?
- Is the fixed point unique?
- What is the fixed point value?

**Implication**: CLAIR's `self_ref_belief` with arbitrary user-defined functions is fundamentally undecidable. We must either:
- Restrict the language of self-reference
- Accept runtime approximation
- Provide timeouts/bounds

### 2.4 Tarski's Fixed-Point Theorem

**Theorem (Knaster-Tarski)**: Every monotone function on a complete lattice has a fixed point. The set of fixed points forms a complete lattice (with greatest and least elements).

**Key insight**: Monotonicity enables constructive computation of fixed points. For monotone f:
- Least fixed point: iterate from ⊥
- Greatest fixed point: iterate from ⊤

**Relevance**: If CLAIR restricts self-reference to monotone functions on lattices, fixed points become computable (though possibly expensive).

---

## 3. Complexity Analysis

### 3.1 The Continuous Case: [0,1] Confidence

For self-referential confidence computation `f : [0,1] → [0,1]`:

**Existence**: Always exists by Brouwer (continuous f on [0,1]).

**Uniqueness**: Guaranteed if f is a contraction (|f'| < 1 everywhere).

**Complexity of finding the fixed point**:

| Condition | Algorithm | Complexity |
|-----------|-----------|------------|
| f is a contraction with L < 1 | Iteration | O(log(1/ε) / log(1/L)) for ε precision |
| f is monotone | Iteration from 0 or 1 | O(log(1/ε)) for ε precision |
| f is general continuous | Bisection | O(log(1/ε)) but may miss multiple roots |
| f has bounded variation | Numeric methods | O(1/ε) worst case |

**Key result**: For confidence computation (continuous [0,1] → [0,1]), fixed-point computation is polynomial in the precision required.

### 3.2 The Discrete Case: Finite Domains

For self-referential content over finite domain D with |D| = n:

**Existence**: f : D → D always has a fixed point (pigeonhole: iterate f^i(x) for i=1..n+1 must repeat; a cycle containing a fixed point or the cycle starts over).

Wait, that's not quite right. Let me reconsider.

**Correction**: A function f : D → D doesn't necessarily have a fixed point. Consider D = {0,1} with f(0) = 1, f(1) = 0. No fixed point.

**Existence check**: O(n) time by iterating f(x), f^2(x), ... and checking if f^i(x) = x for any i ≤ n.

**Finding a fixed point (if exists)**: O(n) time.

**Counting fixed points**: O(n) time (check f(x) = x for each x ∈ D).

**Key result**: For finite domains, fixed-point analysis is O(n) in domain size.

### 3.3 The Symbolic Case: Type-Level Computation

For self-referential type definitions or symbolic expressions:

**Example**:
```clair
self_ref_belief(λself →
  content: if confidence(self) > 0.5 then "high" else "low"
  confidence: if content(self) = "high" then 0.8 else 0.3
)
```

This is a coupled system where content depends on confidence and vice versa.

**Analysis**: The domain is finite ({high, low} × {0.8, 0.3, ...}), so enumeration is feasible.

But consider:
```clair
self_ref_belief(λself →
  content: compute_expensive(self)
  confidence: if halts(content(self)) then 1.0 else 0.0
)
```

**This is undecidable** (reduces to halting problem).

### 3.4 Complexity Summary

| Domain | Existence | Uniqueness | Finding FP | Compile-Time? |
|--------|-----------|------------|------------|---------------|
| [0,1] continuous | Always (Brouwer) | If contraction | O(log(1/ε)) | Sometimes |
| Finite D | Decidable O(n) | Decidable O(n) | O(n) | Yes |
| ℕ or infinite discrete | Undecidable | Undecidable | Undecidable | No |
| Symbolic/arbitrary | Undecidable | Undecidable | Undecidable | No |

---

## 4. Static Analysis Opportunities

### 4.1 Syntactic Classes Amenable to Compile-Time Resolution

**Class 1: Constant confidence** — Trivially decidable
```clair
self_ref_belief(λself →
  content: "I am moderately confident"
  confidence: 0.5  -- constant, doesn't depend on self
)
```
Fixed point: confidence = 0.5 always. No iteration needed.

**Class 2: Monotone predicates** — Decidable by Tarski
```clair
self_ref_belief(λself →
  content: "confidence is at least 0.4"
  confidence: if content_holds(self) then 0.6 else 0.3
)
```
Analysis:
- If content false → confidence 0.3 → content "≥0.4" is false ✓
- If content true → confidence 0.6 → content "≥0.4" is true ✓

Both 0.3 and 0.6 are fixed points! By monotonicity, choose least (0.3) or greatest (0.6).

**Class 3: Linear confidence functions** — Closed-form solution
```clair
self_ref_belief(λself →
  content: "my confidence is " ++ show(confidence(self))
  confidence: a × confidence(self) + b  -- linear in self
)
```
Fixed point: c = ac + b → c(1-a) = b → c = b/(1-a) if a ≠ 1.

**Class 4: Finite enumeration** — Decidable by exhaustive check
```clair
self_ref_belief(λself →
  content: self.content  -- identity on finite domain
  confidence: f(self.confidence)  -- finite confidence levels
)
```
If domain is finite (e.g., L₅ = {0, 0.25, 0.5, 0.75, 1}), enumerate all.

### 4.2 Syntactic Patterns That Are Dangerous

**Pattern 1: Negation (Liar-like)**
```clair
self_ref_belief(λself →
  confidence: if confidence(self) > 0.5 then 0.0 else 1.0
)
```
Oscillates between 0 and 1. No fixed point in crisp semantics.

In continuous semantics: f(c) = 1-c would have fixed point c = 0.5, but the threshold creates discontinuity.

**Pattern 2: Unbounded recursion**
```clair
self_ref_belief(λself →
  content: compute_forever(self)
  ...
)
```
Non-terminating → no fixed point (or undefined).

**Pattern 3: Halting dependency**
```clair
self_ref_belief(λself →
  confidence: if terminates(eval(self.content)) then 1.0 else 0.0
)
```
Reduces to halting problem → undecidable.

### 4.3 A Decidable Fragment: CLAIR-SelfRef-Finite

**Definition**: A self-referential belief is in CLAIR-SelfRef-Finite if:
1. Content type is finite
2. Confidence is from finite lattice L_n
3. Both `content_fn` and `confidence_fn` are total computable functions

**Theorem**: Fixed-point analysis for CLAIR-SelfRef-Finite is decidable in O(|ContentType| × |L_n|) time.

**Proof**: The state space is finite. Enumerate all (content, confidence) pairs and check which are fixed points. ∎

**Corollary**: For L₅ (5 confidence levels) and Boolean content, fixed-point analysis takes O(10) = O(1) operations.

---

## 5. Compile-Time vs. Runtime Decision

### 5.1 Decision Procedure

The CLAIR type checker can use the following procedure for `self_ref_belief(f)`:

```
1. Analyze f syntactically:
   a. If confidence function is constant → COMPILE_TIME_UNIQUE
   b. If confidence function is linear c' = a×c + b with a ≠ 1 → COMPILE_TIME_UNIQUE
   c. If contains negation/oscillation pattern → COMPILE_TIME_ERROR(Liar-like)
   d. If contains Curry pattern → COMPILE_TIME_ERROR(Curry-like)

2. Check domain:
   a. If both content and confidence domains are finite → COMPILE_TIME_ENUMERABLE
   b. If infinite but confidence is continuous → RUNTIME_CONVERGENT
   c. If arbitrary → RUNTIME_BOUNDED (with timeout)

3. For COMPILE_TIME_ENUMERABLE:
   Enumerate all states, find fixed points, return analysis.

4. For RUNTIME_CONVERGENT:
   Insert iteration code with convergence check.

5. For RUNTIME_BOUNDED:
   Insert iteration code with timeout. Return partial result or error.
```

### 5.2 Type System Integration

We can encode fixed-point computability in the type system:

```clair
-- Compile-time fixed point (constant)
self_ref_const : (A : Type) → (c : Confidence) → A → Belief<A, c>

-- Compile-time fixed point (finite enumeration)
self_ref_finite : (A : FiniteType) → (f : Belief<A> → BeliefContent<A>) →
                  FixedPointResult<A>

-- Runtime fixed point (convergent)
self_ref_convergent : (f : Belief<A> → BeliefContent<A>) →
                      {proof : IsContraction f} →
                      IO (Belief<A>)

-- Runtime fixed point (bounded)
self_ref_bounded : (f : Belief<A> → BeliefContent<A>) →
                   (timeout : Duration) →
                   IO (Result<Belief<A>, Timeout>)
```

### 5.3 Annotations for Programmer Guidance

```clair
-- Programmer asserts uniqueness (checked at runtime)
@unique_fixpoint
let b = self_ref_belief(f)

-- Programmer asserts existence (checked at runtime)
@exists_fixpoint
let b = self_ref_belief(f)

-- Programmer accepts any fixed point (if multiple exist)
@any_fixpoint
let b = self_ref_belief(f)

-- Programmer chooses least fixed point (if multiple exist)
@least_fixpoint
let b = self_ref_belief(f)
```

---

## 6. Connection to Prior Art

### 6.1 Abstract Interpretation

**Cousot & Cousot (1977)**: Fixed-point computation is central to abstract interpretation for program analysis.

Key insights:
- Widening/narrowing operators accelerate convergence
- Galois connections relate abstract and concrete domains
- Finite abstract domains guarantee termination

**Application to CLAIR**: Use abstract confidence domains (like L₅) for decidable fixed-point analysis. The finite lattice L₅ = {0, 0.25, 0.5, 0.75, 1} provides:
- Decidability: O(5) checks
- Reasonable precision: 5 levels capture uncertainty
- Closure under Löb discount: g(c) = floor(c²) stays in L₅

### 6.2 Datalog and Stratified Negation

**Van Gelder et al. (1991)**: Stratified Datalog has decidable fixed-point semantics.

Key insight: Stratification prevents negation cycles, ensuring termination.

**Application to CLAIR**: CLAIR's stratification (Belief<n> only references Belief<m> for m < n) is analogous to stratified Datalog. Within each stratum, fixed-point computation is bounded.

### 6.3 Well-Founded Semantics

**Van Gelder, Ross, Schlipf (1991)**: Well-founded semantics provides three-valued (true/false/undefined) fixed points for arbitrary Datalog with negation.

**Application to CLAIR**: For self-referential beliefs that don't have two-valued fixed points (like the truth-teller), well-founded semantics would assign "undefined"—matching CLAIR's `Underdetermined` result.

### 6.4 μ-Calculus and Model Checking

**Kozen (1983)**: The modal μ-calculus provides syntax for least and greatest fixed points. Model checking μ-calculus is decidable for finite state spaces.

**Complexity**:
- Linear in formula size, polynomial in state space size
- More precisely: O(|φ| × |S| × |R|) where φ is formula, S is states, R is transitions

**Application to CLAIR**: Self-referential beliefs can be viewed as μ-calculus formulas over the belief state space. For finite confidence lattices, model checking techniques apply.

### 6.5 Typed Fixed-Point Operators

**Plotkin & Abadi (1993)**: Call-by-name PCF with recursive types has decidable typing. The Y combinator (fixed-point operator) has type (A → A) → A.

**Application to CLAIR**: `self_ref_belief` is essentially a fixed-point operator. Restricting to certain type patterns (e.g., stratified types) preserves decidability.

---

## 7. Theoretical Boundaries

### 7.1 Lower Bounds

**Theorem**: Fixed-point computation for self-referential beliefs is at least as hard as:
- Satisfiability (NP-hard) for Boolean content
- Polynomial root-finding for polynomial confidence functions
- Model checking for modal/temporal content

**Proof sketch**: Encode these problems as fixed-point problems.

Example (SAT reduction):
```clair
self_ref_belief(λself →
  content: φ  -- SAT formula
  confidence: if satisfies(assignment(self), φ) then 1.0 else 0.0
)
```
Finding a fixed point with confidence 1.0 ≡ finding a satisfying assignment.

### 7.2 Upper Bounds

**Theorem**: For CLAIR-SelfRef-Finite, fixed-point computation is in P (polynomial time in domain size).

**Theorem**: For continuous confidence functions on [0,1], approximate fixed-point computation is in FP (function polynomial time) with error parameter ε.

**Theorem**: For arbitrary computable functions, fixed-point computation is Σ₁-complete (recursively enumerable but not recursive).

### 7.3 The Decidable/Undecidable Boundary

The boundary is characterized by:

| Decidable | Undecidable |
|-----------|-------------|
| Finite domains | Infinite discrete domains |
| Continuous functions on [0,1] | Discontinuous functions |
| Stratified self-reference | Arbitrary self-reference |
| Monotone functions on lattices | Non-monotone functions |
| Polynomial constraints | General recursive constraints |

---

## 8. Design Recommendations

### 8.1 For the Language Design

1. **Default to stratification**: Most introspection should use `Belief<n>` types with n > m for references. This is always compile-time checkable.

2. **Make escape hatch explicit**: `self_ref_belief` should be visually distinct and require justification (like `unsafe` in Rust).

3. **Require domain annotations**: Force programmers to specify finite domains when possible:
   ```clair
   self_ref_belief<FiniteContent, L5>(f)  -- compile-time
   self_ref_belief<StringContent, Real>(f)  -- runtime with warning
   ```

4. **Provide standard combinators**: For common patterns (linear, monotone, constant), provide built-in combinators that are guaranteed compile-time:
   ```clair
   const_confidence_belief : A → Confidence → Belief<A>
   linear_self_ref : (a : Confidence) → (b : Confidence) → (a ≠ 1) → Belief<A>
   ```

### 8.2 For the Type Checker

1. **Syntactic analysis first**: Detect Liar/Curry patterns before any computation.

2. **Domain analysis second**: Determine if domains are finite and enumerate if so.

3. **Contractivity check third**: For continuous functions, check if derivative bound < 1.

4. **Fallback to runtime**: For unanalyzable cases, emit a warning and generate runtime code.

### 8.3 For the Runtime

1. **Bounded iteration**: Always have a maximum iteration count (e.g., 1000).

2. **Convergence detection**: Stop early if |c_{n+1} - c_n| < ε.

3. **Cycle detection**: For discrete domains, detect cycles (no fixed point or oscillation).

4. **Timeout**: For expensive content computation, impose wall-clock timeout.

5. **Result classification**: Return structured result indicating:
   - `Unique(belief)` — single fixed point found
   - `Multiple(beliefs)` — multiple fixed points, returning least/greatest/all
   - `None(reason)` — no fixed point (with diagnostic: oscillation, contradiction, timeout)

---

## 9. Formal Statements for Lean

### 9.1 Decidability for Finite Domains

```lean
theorem fixedpoint_decidable_finite (D : Type) [Fintype D] [DecidableEq D]
    (f : D → D) : Decidable (∃ x, f x = x) := by
  -- Enumerate D and check each element
  exact Fintype.decidableExistsFintype

theorem fixedpoint_computable_finite (D : Type) [Fintype D] [DecidableEq D]
    (f : D → D) : Option D :=
  Fintype.find? (fun x => f x = x)
```

### 9.2 Convergence for Contractions

```lean
theorem contraction_converges (f : unitInterval → unitInterval)
    (L : ℝ) (hL : L < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    ∃! x : unitInterval, f x = x := by
  -- Apply Banach fixed-point theorem
  exact Metric.existsUnique_fixedPoint_of_contraction hL hf

theorem contraction_iterations (f : unitInterval → unitInterval)
    (L : ℝ) (hL : L < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y)
    (x₀ : unitInterval) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, dist ((f^[n]) x₀) (fixedPoint f) < ε ∧
             n ≤ Nat.ceil (Real.log ε / Real.log L) := by
  sorry -- Standard contraction convergence rate
```

### 9.3 Undecidability for General Case

```lean
-- This would be a reduction from the Halting Problem
theorem fixedpoint_undecidable_general :
    ¬∃ (decide : (ℕ → ℕ) → Bool),
      ∀ f, decide f = true ↔ ∃ n, f n = n := by
  -- Rice's theorem: non-trivial semantic properties are undecidable
  sorry -- Requires formalization of computability theory
```

---

## 10. Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Finite domains are decidable | 0.95 | Direct enumeration, standard result |
| Continuous functions on [0,1] converge | 0.90 | Brouwer existence + iteration |
| General case is undecidable | 0.95 | Rice's theorem |
| Stratification is always compile-time | 0.95 | Type-level check |
| L₅ is sufficient for practical use | 0.80 | Validated in Thread 3.27 |
| Syntactic pattern detection feasible | 0.75 | Conservative analysis may miss cases |
| Runtime bounded iteration is safe | 0.85 | With proper timeout/bounds |
| Complete boundary characterization | 0.60 | Approximation; edge cases uncertain |

---

## 11. Open Questions

### 11.1 Resolved by This Exploration

- **Q**: Is fixed-point computation decidable? → **A**: Depends on domain. Finite: yes. Continuous [0,1]: yes (approximation). General: no.

- **Q**: Can compile-time analysis help? → **A**: Yes, for stratified, finite, monotone, linear, or constant cases.

- **Q**: What's the complexity? → **A**: O(|domain|) for finite; O(log(1/ε)) for contractive continuous; undecidable in general.

### 11.2 New Questions Raised

- **Q3.28**: Can we detect contractivity automatically? What syntactic patterns guarantee |f'| < 1?

- **Q3.29**: Should CLAIR provide a "gradual typing" approach where self-reference starts unchecked and gets verified incrementally?

- **Q3.30**: How does fixed-point complexity interact with the Löb discount? (The discount c² is itself a fixed-point-like operation.)

- **Q3.31**: Can probabilistic/approximate methods (e.g., random sampling) give useful bounds for undecidable cases?

---

## 12. Impact on CLAIR Design

### 12.1 Type System

- Add `FiniteContent` type class for guaranteed compile-time analysis
- Add `Contractable` type class for convergent runtime analysis
- Make domain annotations mandatory for `self_ref_belief`

### 12.2 Compiler

- Implement syntactic pattern detection for Liar/Curry
- Implement domain size analysis for finite enumeration
- Emit warnings for potentially slow/unbounded cases

### 12.3 Runtime

- Implement bounded iteration with configurable limits
- Implement convergence detection for early termination
- Implement timeout mechanism for expensive computation

### 12.4 Documentation

- Clearly document the decidable/undecidable boundary
- Provide guidance on which patterns to prefer
- Warn about performance implications of general self-reference

---

## 13. Conclusion

**Task 3.12 is substantially answered.**

Key findings:

1. **Fixed-point computation complexity varies dramatically by domain**:
   - Finite domains: O(|domain|), always decidable
   - Continuous [0,1]: O(log(1/ε)), always converges
   - General: undecidable (Rice's theorem)

2. **Compile-time analysis is possible for**:
   - Constant confidence functions (trivial)
   - Linear confidence functions (closed-form)
   - Finite content × finite confidence (enumeration)
   - Monotone functions on lattices (Tarski)
   - Stratified self-reference (type-level check)

3. **Runtime is required for**:
   - General continuous functions (iteration)
   - Arbitrary self-referential content (bounded + timeout)

4. **The recommended approach**:
   - Default to stratification (always compile-time)
   - For escape hatch, require domain annotations
   - Compiler performs syntactic analysis + domain analysis
   - Runtime uses bounded iteration with convergence detection

5. **The decidability boundary is characterized by**:
   - Finite vs. infinite domains
   - Continuous vs. discontinuous functions
   - Monotone vs. non-monotone
   - Stratified vs. arbitrary reference

This analysis provides the theoretical foundation for CLAIR's self-reference implementation and type system design.

---

## 14. References

### Primary Sources

- **Kleene, S.C.** (1952). *Introduction to Metamathematics*. Chapters on recursion and fixed points.

- **Tarski, A.** (1955). "A Lattice-Theoretical Fixpoint Theorem and Its Applications." *Pacific Journal of Mathematics*, 5(2), 285-309.

- **Rice, H.G.** (1953). "Classes of Recursively Enumerable Sets and Their Decision Problems." *Transactions of the AMS*, 74(2), 358-366.

- **Brouwer, L.E.J.** (1911). "Über Abbildung von Mannigfaltigkeiten." *Mathematische Annalen*, 71, 97-115.

- **Banach, S.** (1922). "Sur les opérations dans les ensembles abstraits." *Fundamenta Mathematicae*, 3, 133-181.

### Program Analysis

- **Cousot, P. & Cousot, R.** (1977). "Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs." *POPL 1977*.

- **Van Gelder, A., Ross, K., Schlipf, J.** (1991). "The Well-Founded Semantics for General Logic Programs." *JACM*, 38(3), 620-650.

### Type Theory

- **Plotkin, G. & Abadi, M.** (1993). "A Logic for Parametric Polymorphism." *TLCA 1993*.

- **Kozen, D.** (1983). "Results on the Propositional μ-Calculus." *TCS*, 27(3), 333-354.

### CLAIR Internal

- Thread 3: exploration/thread-3-self-reference.md
- Thread 3.27: exploration/thread-3.27-optimal-lattice-choice.md
- Thread 5.11: exploration/thread-5.11-defeat-fixedpoints.md

---

*Thread 3.12 Status: Substantially explored. Complexity characterized by domain. Decidable fragments identified. Design recommendations provided. Ready for Lean formalization of finite case.*
