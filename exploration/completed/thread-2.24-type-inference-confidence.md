# Thread 2.24: Type Inference for Confidence

> **Status**: Active exploration (Session 62)
> **Task**: 2.24 Can confidence bounds be inferred automatically?
> **Question**: What algorithm infers confidence bounds, and is it decidable?
> **Prior Work**: Thread 2.23 (subtyping), Thread 2.22 (Curry-Howard), Thread 2.25 (dual-monoid grading)

---

## 1. The Problem

### 1.1 Motivation

CLAIR's type system includes graded belief types with confidence bounds:

```
Belief<A>[c]     "Belief of type A with confidence at least c"
```

Currently, these bounds must be stated explicitly. But programmers may find this burdensome:

```clair
-- Explicit confidence: tedious
f : Belief<Int>[0.9] -> Belief<Int>[0.8] -> Belief<Int>[0.72]
f x y = derive(x, y)   -- Programmer must compute 0.9 * 0.8 = 0.72

-- Inferred confidence: desired
f x y = derive(x, y)   -- Compiler infers the confidence bound
```

**The question**: Can we automatically infer confidence bounds from program structure?

### 1.2 Why This Matters

Type inference for confidence would:
1. **Reduce annotation burden**: Programmers write less, compiler computes more
2. **Catch errors earlier**: Compiler reports when required confidence is unsatisfiable
3. **Enable exploration**: "What confidence does this derivation achieve?" becomes answerable
4. **Support subtyping**: Bidirectional checking (Thread 2.23) benefits from inference

### 1.3 Challenges

Several factors make confidence inference non-trivial:

1. **Two operations**: × (derivation) and ⊕ (aggregation) with different rules
2. **No distributivity**: Cannot simplify expressions (Thread 2.25)
3. **Subtyping**: Higher confidence is subtype of lower (Thread 2.23)
4. **Defeat operations**: undercut and rebut have contravariant positions
5. **Polymorphism**: How does inference interact with type variables?
6. **Principal types**: Does every term have a most general type?

---

## 2. Prior Art Survey

### 2.1 Hindley-Milner Type Inference

The classic algorithm for ML-style languages:

1. **Algorithm W** (Damas & Milner 1982):
   - Assigns fresh type variables to unannotated terms
   - Generates equality constraints from typing rules
   - Solves constraints via unification
   - Returns most general (principal) type

2. **Key properties**:
   - Decidable in EXPTIME (polynomial in practice)
   - Principal types exist: every well-typed term has a most general type
   - Requires no type annotations (except for polymorphic recursion)

**Relevance**: CLAIR's confidence bounds are not unified like type variables—they're constrained by inequalities.

### 2.2 Liquid Types (Refinement Type Inference)

**Liquid Types** (Rondon, Kawaguchi, Jhala 2008) infer refinement predicates:

```
{x : Int | x > 0}     "positive integers"
```

Algorithm:
1. Assign fresh predicate variables (κ) at unknown positions
2. Collect subtyping constraints: {v | κ₁} <: {v | κ₂}
3. Reduce to logical implication: κ₁ ⇒ κ₂
4. Solve using abstract interpretation over a finite set of candidate predicates

**Key insight**: Inference is decidable when predicates come from a finite "template" set.

**Relevance**: CLAIR's confidence bounds are like refinement predicates (c >= 0.7), but:
- Our predicates are simple inequalities (not arbitrary formulas)
- We have two combining operations (×, ⊕)
- Subtyping is based on >= (Thread 2.23)

### 2.3 Graded Type Inference

**Granule** (Orchard et al. 2019) infers grades over semirings:

```
f : A →[r] B     "f uses A with grade r"
```

Algorithm:
1. Assign fresh grade variables at unknown positions
2. Collect constraints from typing rules (often equalities for semirings)
3. Solve via substitution and simplification

**Key property**: For semirings with decidable equality, inference is decidable.

**Relevance**: CLAIR's dual-monoid (× and ⊕) is NOT a semiring—no distributivity. Standard graded type inference doesn't directly apply.

### 2.4 Constraint-Based Type Inference

General framework (Aiken 1999):

1. **Constraint generation**: Walk the syntax tree, emit constraints
2. **Constraint solving**: Use domain-specific solver
3. **Principal solutions**: Identify most general satisfying assignment

For inequality constraints over ordered domains:
- Linear arithmetic: LP/ILP solvers
- Interval arithmetic: Constraint propagation
- Lattice constraints: Fixed-point computation

**Relevance**: CLAIR confidence constraints are over [0,1] with × and ⊕ operations. This is non-linear arithmetic, which complicates solving.

### 2.5 Subtyping with Bounded Quantification

**System F<:** (Cardelli & Wegner 1985) has bounded type variables:

```
∀X <: T. ...
```

Type inference for F<: is undecidable in general, but decidable fragments exist:
- F<:₋ (no bounded quantification at depth)
- Kernel F<: (restricted inheritance)

**Relevance**: If CLAIR has bounded confidence polymorphism (∀c >= 0.5. ...), inference complexity depends on bounds.

---

## 3. CLAIR Confidence Inference Design

### 3.1 The Inference Problem

**Input**: A CLAIR term e with some confidence annotations omitted
**Output**: Either:
- A fully-annotated term with principal confidence bounds
- An error indicating unsatisfiable constraints

**Example**:
```clair
-- Input (confidence omitted)
f : Belief<A>[?] -> Belief<A -> B>[?] -> Belief<B>[?]
f x y = derive(x, y)

-- Output (confidence inferred)
f : ∀c₁ c₂. Belief<A>[c₁] -> Belief<A -> B>[c₂] -> Belief<B>[c₁ × c₂]
```

### 3.2 Constraint Language

We need constraints over confidence values. Define:

```
Confidence variables:  α, β, γ, ...
Confidence constants:  0, 0.5, 1, etc.
Confidence expressions:
  c ::= α           -- variable
      | k           -- constant in [0,1]
      | c₁ × c₂     -- derivation composition
      | c₁ ⊕ c₂     -- aggregation composition
      | 1 - c       -- complementation (for undercut)
      | c₁ / (c₁ + c₂)  -- rebut formula

Constraints:
  C ::= c₁ = c₂     -- equality
      | c₁ >= c₂    -- lower bound (subtyping)
      | C₁ ∧ C₂     -- conjunction
```

### 3.3 Constraint Generation Rules

Given typing judgment Γ ⊢ e : T, generate constraints.

**Variable**:
```
        x : Belief<A>[α] ∈ Γ
──────────────────────────────────────
Γ ⊢ x : Belief<A>[α]    generates: ∅
```

**Derivation**:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Γ ⊢ e₂ : Belief<A → B>[c₂]
────────────────────────────────────────────────────── [Derive]
       Γ ⊢ derive(e₁, e₂) : Belief<B>[β]

generates: β = c₁ × c₂
```

**Aggregation**:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Γ ⊢ e₂ : Belief<A>[c₂]
─────────────────────────────────────────────────── [Agg]
   Γ ⊢ aggregate(e₁, e₂) : Belief<A>[β]

generates: β = c₁ ⊕ c₂
```

**Undercut**:
```
Γ ⊢ e : Belief<A>[c]    Γ ⊢ d : Belief<Defeat>[d_c]
───────────────────────────────────────────────────── [Undercut]
       Γ ⊢ undercut(e, d) : Belief<A>[β]

generates: β = c × (1 - d_c)
```

**Function application with subtyping**:
```
Γ ⊢ f : Belief<A>[c₁] → Belief<B>[c₂]    Γ ⊢ x : Belief<A>[c₃]
────────────────────────────────────────────────────────────── [App]
              Γ ⊢ f x : Belief<B>[β]

generates: c₃ >= c₁, β = c₂
```

The constraint c₃ >= c₁ comes from subtyping: the argument must have at least the required confidence.

**Let binding** (corresponds to cut):
```
Γ ⊢ e₁ : Belief<A>[c₁]    Γ, x : Belief<A>[c₁] ⊢ e₂ : Belief<B>[c₂]
───────────────────────────────────────────────────────────────────── [Let]
            Γ ⊢ let x = e₁ in e₂ : Belief<B>[β]

generates: β = c₁ × c₂
```

### 3.4 Constraint Solving

The generated constraints have the form:
- Equalities: β = c₁ × c₂, β = c₁ ⊕ c₂, etc.
- Inequalities: c₁ >= c₂ (from subtyping)

**Observation 1**: Equalities define functional dependencies.
- Given c₁ and c₂, β = c₁ × c₂ determines β uniquely
- No unification needed; just evaluate the expression

**Observation 2**: Inequalities define bounds.
- c₁ >= c₂ means "c₁ is at least as high as c₂"
- For subtyping, we want the *tightest* bound (highest confidence)

**Algorithm**:

1. **Topological sort**: Order variables by dependency
   - If β = c₁ × c₂, then β depends on c₁ and c₂
   - Process in dependency order

2. **Forward propagation**: Compute known bounds
   - If c₁ = 0.9 and c₂ = 0.8, then β = c₁ × c₂ = 0.72

3. **Constraint collection**: For inequalities c >= c', collect lower bounds
   - If we need f : Belief<A>[c] → ... and call f x where x : Belief<A>[0.7]
   - Then c <= 0.7 (the function can require at most what the argument provides)

4. **Solve**: Find assignments satisfying all constraints
   - For equalities: direct computation
   - For inequalities: compute the tightest (max or min) bound

### 3.5 Principal Types

**Question**: Does every well-typed term have a principal (most general) type?

**For confidences specifically**:
- The "most general" confidence bound is the *tightest* one (highest)
- A term with confidence 0.9 has principal bound 0.9, not any lower bound

**Theorem** (Principal Confidence Bounds): For a closed term e with no confidence annotations, if e is typeable, there exists a unique tightest confidence bound c_max such that Γ ⊢ e : Belief<A>[c_max], and for all c with Γ ⊢ e : Belief<A>[c], we have c <= c_max.

**Proof sketch**:
- Confidence propagation is deterministic: given inputs, output is determined
- × and ⊕ are monotone (Thread 2.23), so tighter inputs give tighter outputs
- The principal bound is obtained by using the tightest available input bounds
∎

**For polymorphic functions**:
```clair
f : ∀c. Belief<A>[c] -> Belief<B>[c]
```

The principal type expresses the relationship between input and output confidence. This requires bounded quantification.

---

## 4. Decidability Analysis

### 4.1 The Core Question

Is CLAIR type inference decidable?

**Factors favoring decidability**:
1. Confidence values form a bounded domain [0,1]
2. Operations (×, ⊕) are computable
3. Constraint language is quantifier-free (for monomorphic terms)
4. No recursive types in confidence bounds

**Factors complicating decidability**:
1. Real-valued confidence (not rational) may require algebraic decision procedures
2. Non-linear arithmetic: × and ⊕ are not linear operations
3. Polymorphism with bounds may introduce quantifier alternation

### 4.2 Monomorphic Case

**Theorem** (Monomorphic Decidability): Type inference for monomorphic CLAIR terms with rational confidence is decidable.

**Proof**:
1. Constraint generation produces finitely many constraints
2. Each constraint is either:
   - Equality: β = f(c₁, ..., cₙ) where f is a computable function
   - Inequality: c₁ >= c₂
3. For rational confidence, all operations are computable rationals
4. Solve equalities by substitution (topological order ensures termination)
5. Solve inequalities by checking bounds on a lattice
6. Either find satisfying assignment or report failure
∎

**Complexity**: Constraint generation is linear in term size. Solving is polynomial (for acyclic constraints).

### 4.3 Polymorphic Case

**Bounded quantification**:
```clair
∀c >= 0.5. Belief<A>[c] -> Belief<A>[c × 0.9]
```

This introduces implication constraints:
- "For all c >= 0.5, there exists a valid typing"

**Theorem** (Polymorphic Complexity): Type inference with bounded confidence polymorphism is decidable but potentially EXPTIME.

**Proof sketch**:
1. Bounded quantification over a finite lattice (L₅) is decidable
2. For continuous [0,1], requires decision procedure for polynomial inequalities
3. Tarski's theorem: first-order theory of real-closed fields is decidable (EXPTIME)
4. CLAIR constraints are within this fragment
∎

### 4.4 Special Cases

**CLAIR-finite** (confidence in finite lattice L_n):
- All operations are table lookups
- Decidable in polynomial time

**CLAIR-rational** (confidence in Q ∩ [0,1]):
- Operations are rational arithmetic
- Decidable (rational arithmetic is decidable)

**CLAIR-real** (confidence in ℝ ∩ [0,1]):
- Operations involve real multiplication
- Decidable via quantifier elimination (Tarski-Seidenberg)
- But exponential complexity

---

## 5. Inference Algorithm

### 5.1 Algorithm INFER

```
Input: Term e, context Γ with some confidences unknown
Output: Fully annotated term with principal confidences, or error

INFER(Γ, e):
  match e with
  | x ->
      let c = lookup(Γ, x)
      return (x, c)

  | derive(e₁, e₂) ->
      let (e₁', c₁) = INFER(Γ, e₁)
      let (e₂', c₂) = INFER(Γ, e₂)
      let c = c₁ × c₂
      return (derive(e₁', e₂'), c)

  | aggregate(e₁, e₂) ->
      let (e₁', c₁) = INFER(Γ, e₁)
      let (e₂', c₂) = INFER(Γ, e₂)
      let c = c₁ ⊕ c₂
      return (aggregate(e₁', e₂'), c)

  | undercut(e, d) ->
      let (e', c) = INFER(Γ, e)
      let (d', d_c) = INFER(Γ, d)
      let c' = c × (1 - d_c)
      return (undercut(e', d'), c')

  | rebut(e₁, e₂) ->
      let (e₁', c₁) = INFER(Γ, e₁)
      let (e₂', c₂) = INFER(Γ, e₂)
      let c = c₁ / (c₁ + c₂)
      return (rebut(e₁', e₂'), c)

  | λx:A. e ->
      let α = fresh_confidence_var()
      let (e', c) = INFER(Γ ∪ {x : Belief<A>[α]}, e)
      return (λx:Belief<A>[α]. e', Belief<A>[α] → Belief<B>[c])

  | f e ->
      let (f', Belief<A>[c_req] → Belief<B>[c_res]) = INFER(Γ, f)
      let (e', c_arg) = INFER(Γ, e)
      check c_arg >= c_req  -- subtyping check
      return (f' e', c_res)

  | let x = e₁ in e₂ ->
      let (e₁', c₁) = INFER(Γ, e₁)
      let (e₂', c₂) = INFER(Γ ∪ {x : Belief<A>[c₁]}, e₂)
      return (let x = e₁' in e₂', c₁ × c₂)
```

### 5.2 Handling Polymorphism

For polymorphic functions, we generalize confidence variables:

```
GENERALIZE(Γ, e, T):
  let fvs = free_confidence_vars(T) - free_confidence_vars(Γ)
  return ∀fvs. T

-- Example:
-- λx. x has inferred type Belief<A>[α] → Belief<A>[α]
-- GENERALIZE gives ∀α. Belief<A>[α] → Belief<A>[α]
```

For instantiation, we substitute fresh variables for bound confidence parameters.

### 5.3 Bidirectional Checking

Following Thread 2.23's recommendation, use bidirectional type checking:

**Synthesis mode (⇒)**: Infer the type from the term
**Checking mode (⇐)**: Check the term against an expected type

```
SYNTH(Γ, e):  -- returns (e', T) where T is synthesized type
CHECK(Γ, e, T):  -- checks e against expected T, returns annotated e'

-- Subsumption at mode switch:
CHECK(Γ, e, T_expected):
  let (e', T_inferred) = SYNTH(Γ, e)
  check T_inferred <: T_expected  -- includes c_inferred >= c_expected
  return e'
```

This approach:
- Synthesizes tightest bounds where possible
- Uses expected bounds where provided
- Reports errors when bounds can't be satisfied

---

## 6. Examples

### 6.1 Simple Derivation

```clair
-- Input
x : Belief<Nat>[0.9]
y : Belief<Nat>[0.8]
derive(x, y)

-- Inference
-- c = 0.9 × 0.8 = 0.72
-- Result: Belief<Nat>[0.72]
```

### 6.2 Aggregation

```clair
-- Input
w1 : Belief<Guilty>[0.7]
w2 : Belief<Guilty>[0.6]
aggregate(w1, w2)

-- Inference
-- c = 0.7 ⊕ 0.6 = 0.7 + 0.6 - 0.7×0.6 = 0.88
-- Result: Belief<Guilty>[0.88]
```

### 6.3 Defeat

```clair
-- Input
claim : Belief<A>[0.9]
defeat : Belief<Defeat>[0.95]
undercut(claim, defeat)

-- Inference
-- c = 0.9 × (1 - 0.95) = 0.9 × 0.05 = 0.045
-- Result: Belief<A>[0.045]
```

### 6.4 Function with Subtyping

```clair
-- Input
needs_high : Belief<A>[0.8] -> Belief<B>[0.7]
evidence : Belief<A>[0.9]
needs_high evidence

-- Inference
-- Check: 0.9 >= 0.8? Yes (subtyping satisfied)
-- Result: Belief<B>[0.7]
```

### 6.5 Failing Constraint

```clair
-- Input
needs_high : Belief<A>[0.8] -> Belief<B>[0.7]
weak_evidence : Belief<A>[0.5]
needs_high weak_evidence

-- Inference
-- Check: 0.5 >= 0.8? NO!
-- Error: Confidence 0.5 does not satisfy required bound 0.8
```

### 6.6 Polymorphic Function

```clair
-- Input
id = λx. x

-- Inference
-- Assign fresh α to x
-- λx:Belief<A>[α]. x : Belief<A>[α] → Belief<A>[α]
-- Generalize: ∀α. Belief<A>[α] → Belief<A>[α]

-- Now instantiate at call site:
id high_confidence_evidence  -- instantiates α to whatever the argument has
```

---

## 7. Interaction with Dual-Monoid Structure

### 7.1 No Mixing Required

Thread 2.25 established that × (derivation) and ⊕ (aggregation) don't distribute. Does this affect inference?

**Key observation**: The type system naturally separates these operations:
- Derivation chains use × exclusively
- Aggregation combines independent evidence using ⊕
- We never need to simplify expressions like a × (b ⊕ c)

**Consequence**: Non-distributivity doesn't complicate inference. Each expression is either a × expression or a ⊕ expression, never mixed at the same level.

### 7.2 Constraint Structure

Constraints generated by INFER have a specific structure:

```
Derivation constraints:    β = c₁ × c₂ × ... × cₙ
Aggregation constraints:   β = c₁ ⊕ c₂ ⊕ ... ⊕ cₙ
Mixed expressions:         Don't arise from typing rules
```

This structure ensures that solving remains straightforward—we never face non-distributivity issues.

### 7.3 De Morgan Duality

The complement operation (1 - c) appears in undercut. The De Morgan law:
```
a ⊕ b = 1 - (1 - a) × (1 - b)
```

This allows rewriting certain expressions, but INFER doesn't need this—it computes confidence values directly.

---

## 8. Implementation Considerations

### 8.1 Rational Arithmetic

Recommendation: Use exact rational arithmetic (as in Thread 7.1).

```haskell
-- Haskell representation
type Confidence = Ratio Integer

-- Operations
derive_conf :: Confidence -> Confidence -> Confidence
derive_conf c1 c2 = c1 * c2

aggregate_conf :: Confidence -> Confidence -> Confidence
aggregate_conf c1 c2 = c1 + c2 - c1 * c2
```

This avoids floating-point precision issues and ensures decidability.

### 8.2 Error Messages

When inference fails, provide informative errors:

```
Error at line 15, column 10:
  Cannot apply function `needs_high_confidence`
  Expected: Belief<Result>[0.8] (minimum confidence 0.8)
  Got:      Belief<Result>[0.65] (computed from derivation)

  The argument confidence 0.65 is less than required 0.8.
  Consider: aggregating with additional evidence to increase confidence
```

### 8.3 IDE Support

For tooling:
- **Confidence hover**: Show inferred confidence on hover
- **Confidence flow**: Visualize how confidence propagates through derivations
- **Constraint viewer**: Show what bounds are required and satisfied

---

## 9. Limitations and Open Questions

### 9.1 Recursive Functions

For recursive functions:
```clair
fix f. λx. ... f (derive(x, evidence)) ...
```

Confidence may change through recursion. The fixed-point semantics (Thread 5.11) ensures existence, but inference must handle this.

**Option 1**: Require confidence annotation for recursive functions
**Option 2**: Compute fixed-point of confidence (may be 0 or 1 in limit)

### 9.2 Higher-Order Functions

Functions that take and return functions:
```clair
compose : (Belief<B>[c₂] → Belief<C>[c₃])
        → (Belief<A>[c₁] → Belief<B>[c₂])
        → (Belief<A>[c₁] → Belief<C>[c₃ × c₂])
```

Inference must track confidence through higher-order types. This works with the algorithm but increases complexity.

### 9.3 Dependent Confidence Bounds

Task 3.24 asks about dependent confidence:
```clair
filter : (A → Bool) → List (Belief<A>[c]) → List (Belief<A>[c'])
-- where c' depends on how many elements pass the filter
```

This requires dependent types and is beyond current scope.

### 9.4 Real-Valued Confidence

For real (not rational) confidence:
- Tarski-Seidenberg provides decidability
- But exponential complexity
- Practical implementation may use interval arithmetic or approximation

---

## 10. Conclusions

### 10.1 Key Findings

1. **Inference is decidable**: For monomorphic terms with rational confidence, type inference is decidable in polynomial time.

2. **Algorithm structure**: Generate constraints (equalities and inequalities), solve by forward propagation and bound checking.

3. **Principal types exist**: Every well-typed term has a principal (tightest) confidence bound.

4. **Dual-monoid structure is compatible**: Non-distributivity of × and ⊕ doesn't complicate inference because the operations are naturally separated in derivations.

5. **Subtyping integrates well**: Bidirectional checking with subsumption at mode switches handles subtyping elegantly.

6. **Polymorphism works**: Bounded quantification over confidence allows expressive polymorphic types.

### 10.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Monomorphic inference decidable | 0.95 | Direct algorithm construction |
| Polynomial time (monomorphic) | 0.90 | Linear constraint generation, simple solving |
| Principal types exist | 0.90 | Deterministic propagation, monotonicity |
| Polymorphic inference decidable | 0.80 | Tarski-Seidenberg applies, but complexity |
| Algorithm is practical | 0.85 | Similar to other refinement type systems |
| Non-distributivity doesn't complicate | 0.90 | Structural separation of operations |

### 10.3 Recommendations

1. **Implement INFER**: Add type inference to the reference interpreter (Thread 7)

2. **Use bidirectional checking**: Combine synthesis and checking modes

3. **Rational arithmetic**: Use exact rationals for decidability

4. **Good error messages**: Report why confidence constraints fail

5. **Require annotations for recursion**: Simplifies fixed-point handling

6. **Support confidence elision**: Let programmers write `Belief<A>` and have the compiler infer the bound

---

## 11. Impact on Other Threads

### Thread 7 (Implementation)
- Reference interpreter should include INFER algorithm
- Runtime can skip confidence checking (types guarantee bounds)

### Thread 8 (Formal Verification)
- Lean formalization should prove INFER is sound
- Decidability theorem deserves formal proof

### Thread 2.23 (Subtyping)
- Bidirectional checking recommended there is implemented here

### Thread 2.25 (Dual-Monoid)
- Confirmed: non-distributivity doesn't affect inference

---

## 12. References

### Primary Sources

- **Damas, L. & Milner, R.** (1982). "Principal Type-Schemes for Functional Programs." *POPL 1982*.

- **Rondon, P., Kawaguchi, M., & Jhala, R.** (2008). "Liquid Types." *PLDI 2008*.

- **Orchard, D., Liepelt, V., & Eades, H.** (2019). "Quantitative Program Reasoning with Graded Modal Types." *ICFP 2019*.

- **Pierce, B.C. & Turner, D.N.** (2000). "Local Type Inference." *ACM TOPLAS* 22(1).

- **Tarski, A.** (1951). "A Decision Method for Elementary Algebra and Geometry."

### CLAIR Internal

- Thread 2.22: exploration/thread-2.22-curry-howard-terms.md
- Thread 2.23: exploration/thread-2.23-confidence-subtyping.md
- Thread 2.25: exploration/thread-2.25-dual-monoid-grading.md
- Thread 7.1: exploration/thread-7.1-reference-interpreter.md

---

*Thread 2.24 Status: Substantially explored. Type inference for confidence is decidable with a direct algorithm. Ready for implementation.*
