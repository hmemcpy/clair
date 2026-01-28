# Thread 2.23: Subtyping for Confidence

> **Status**: Active exploration (Session 60)
> **Task**: 2.23 Should Belief<A>[c] be subtype of Belief<A>[c'] when c >= c'?
> **Question**: How does subtyping interact with CLAIR's graded belief types?
> **Prior Work**: Thread 2.22 (Curry-Howard), Thread 2.25 (dual-monoid grading), formal/categorical-structure.md

---

## 1. The Problem

### 1.1 The Core Question

CLAIR's type system includes graded belief types:

```
Belief<A>[c]     "Belief of type A with confidence at least c"
```

The natural question arises: **Should a belief with higher confidence be usable where a lower confidence is expected?**

Intuitively, if I have a belief with confidence 0.9, I should be able to use it in a context expecting confidence 0.7. This suggests:

```
Belief<A>[0.9] <: Belief<A>[0.7]
```

But type theory teaches us that subtyping must be handled carefully. Let's investigate.

### 1.2 Why This Matters

Subtyping affects:
1. **Usability**: Can users pass high-confidence beliefs where low-confidence is expected?
2. **Type inference**: How do we infer confidence bounds?
3. **Implementation**: What runtime checks (if any) are needed?
4. **Soundness**: Does subtyping preserve type safety?
5. **Compositionality**: How does subtyping interact with function types and other constructors?

### 1.3 Preliminaries

Recall from Thread 2.22:
- `Belief<A>[c]` is a graded type with confidence bound c
- Confidence propagates via multiplication (×) in derivations
- Confidence aggregates via probabilistic OR (⊕) for independent evidence

From Thread 2.25:
- The confidence algebra is a De Morgan bimonoid
- × and ⊕ don't distribute (not a semiring)
- Operations are naturally separated in the type system

---

## 2. Prior Art Survey

### 2.1 Refinement Types

**Refinement types** (Rondon et al. 2008, Vazou et al. 2014) augment base types with predicates:

```
{ x : Int | x > 0 }     "positive integers"
```

Subtyping is determined by logical implication:
```
{ x : A | P(x) } <: { x : A | Q(x) }   iff   P(x) => Q(x)
```

**Relevance to CLAIR**: Confidence bounds are predicates on beliefs. A confidence bound of 0.9 implies a bound of 0.7:
```
c >= 0.9 => c >= 0.7
```

This suggests refinement-style subtyping.

### 2.2 Bounded Quantification

**System F<:** (Cardelli & Wegner 1985) adds bounded type variables:
```
∀X <: T. ...
```

Subtyping follows the "width" and "depth" rules for records:
- Width: More fields is a subtype
- Depth: Better fields is a subtype

**Relevance to CLAIR**: Confidence bounds are like "quality" bounds. Higher confidence is "better."

### 2.3 Graded Type Theory Subtyping

**Granule** (Orchard et al. 2019) handles graded types with subtyping:

```
□[r]A <: □[s]A   when   r ≤ s   (in the preorder)
```

Note: In Granule, the subtyping direction depends on interpretation:
- For resource usage: using *less* is a subtype (can be used where more is expected)
- For security: *lower* clearance is a subtype (can be used where higher is permitted)

**Relevance to CLAIR**: For confidence, *higher* is better, so:
```
Belief<A>[c] <: Belief<A>[c']   when   c >= c'
```

### 2.4 Covariance and Contravariance

Standard variance rules for type constructors:

| Constructor | Variance |
|-------------|----------|
| A → B | Contravariant in A, covariant in B |
| List<A> | Covariant |
| Ref<A> | Invariant |

**Question for CLAIR**: What is the variance of Belief<A>[c] in both A and c?

### 2.5 Effect Subtyping

**Effect systems** (Gifford & Lucassen 1986) have:
```
τ ! E₁ <: τ ! E₂   when   E₁ ⊆ E₂
```

A computation with fewer effects can substitute for one with more effects.

**Relevance**: Confidence is not exactly an effect, but the "capability" interpretation is similar—a belief with more confidence has more "epistemic capability."

---

## 3. Subtyping for Confidence Bounds

### 3.1 Basic Subtyping Rule

**Proposal**: Confidence subtyping is contravariant in the bound (higher bound = subtype):

```
      c >= c'
──────────────────────── [Sub-Conf]
Belief<A>[c] <: Belief<A>[c']
```

**Intuition**: A belief guaranteed to have confidence at least 0.9 can be used anywhere expecting confidence at least 0.7.

**Note**: This is the opposite direction from resource grading in Granule (where using *less* is a subtype), but it's consistent with CLAIR's interpretation where higher confidence is "better."

### 3.2 Subtyping in the Value Type

```
     A <: A'
──────────────────────── [Sub-Belief]
Belief<A>[c] <: Belief<A'>[c]
```

Beliefs are covariant in their value type.

### 3.3 Combined Rule

```
   A <: A'      c >= c'
────────────────────────── [Sub-Belief-Full]
Belief<A>[c] <: Belief<A'>[c']
```

### 3.4 Function Types with Beliefs

Standard contravariance applies:

```
A' <: A      Belief<B>[c] <: Belief<B'>[c']
────────────────────────────────────────────── [Sub-Fun-Belief]
(A → Belief<B>[c]) <: (A' → Belief<B'>[c'])
```

For functions returning beliefs: contravariant in argument, covariant in result (including confidence).

### 3.5 Belief-Typed Arguments

```
Belief<A'>[c'] <: Belief<A>[c]      B <: B'
────────────────────────────────────────────── [Sub-Fun-Belief-Arg]
(Belief<A>[c] → B) <: (Belief<A'>[c'] → B')
```

For functions taking belief arguments: a function accepting lower-confidence beliefs is a subtype of one expecting higher-confidence.

This seems counterintuitive at first, but it's correct: if f accepts beliefs with confidence ≥ 0.7, it can be used where a function accepting confidence ≥ 0.9 is expected, because any 0.9+ belief is also 0.7+.

---

## 4. Interaction with CLAIR Operations

### 4.1 Derivation and Subtyping

Derivation multiplies confidence. Does subtyping compose correctly?

**Scenario**:
- Have: e₁ : Belief<A>[c₁] and e₂ : Belief<A → B>[c₂]
- Want: derive(e₁, e₂) : Belief<B>[c₁ × c₂]

**With subtyping**:
- If e₁ : Belief<A>[c₁'] where c₁' >= c₁, then c₁' × c₂ >= c₁ × c₂
- So the derivation result has at least the expected confidence

**Theorem** (Derivation Monotonicity): If e₁ : Belief<A>[c₁'] with c₁' >= c₁, and e₂ : Belief<A → B>[c₂'] with c₂' >= c₂, then:
```
derive(e₁, e₂) : Belief<B>[c₁' × c₂'] where c₁' × c₂' >= c₁ × c₂
```

**Proof**: × is monotone on [0,1]. ∎

### 4.2 Aggregation and Subtyping

Aggregation combines independent evidence via ⊕.

**Scenario**:
- Have: e₁ : Belief<A>[c₁] and e₂ : Belief<A>[c₂]
- Want: aggregate(e₁, e₂) : Belief<A>[c₁ ⊕ c₂]

**With subtyping**:
- If e₁ : Belief<A>[c₁'] with c₁' >= c₁, then c₁' ⊕ c₂ >= c₁ ⊕ c₂
- So aggregation is monotone in both arguments

**Theorem** (Aggregation Monotonicity): ⊕ is monotone in both arguments.

**Proof**:
- c₁' >= c₁ implies c₁' + c₂ - c₁'c₂ >= c₁ + c₂ - c₁c₂
- Since c₁' + c₂ >= c₁ + c₂ and c₁'c₂ >= c₁c₂, need to check:
  - (c₁' - c₁) - (c₁' - c₁)c₂ = (c₁' - c₁)(1 - c₂) >= 0 ✓ ∎

### 4.3 Undercut and Subtyping

Undercut applies defeat: c' = c × (1 - d)

**Scenario**:
- Have: e : Belief<A>[c], d : Belief<Defeat>[d_c]
- Result: undercut(e, d) : Belief<A>[c × (1 - d_c)]

**With subtyping on the belief**:
- If e : Belief<A>[c'] with c' >= c, then c' × (1 - d_c) >= c × (1 - d_c) ✓

**With subtyping on the defeater**:
- If d : Belief<Defeat>[d'] with d' >= d_c, then c × (1 - d') <= c × (1 - d_c)
- The result has *lower* confidence with a *stronger* defeater

**Key insight**: Defeater subtyping works in the opposite direction! A stronger defeater (higher confidence in defeat) produces a weaker result.

**Typing rule with subtyping**:
```
e : Belief<A>[c]      d : Belief<Defeat>[d_c]
──────────────────────────────────────────── [Undercut]
  undercut(e, d) : Belief<A>[c × (1 - d_c)]
```

For subtyping to be sound:
- Higher confidence in e → higher confidence in result ✓
- Higher confidence in d → lower confidence in result (not a subtyping relation)

**Conclusion**: Undercut is covariant in the belief but *contravariant* in the defeater's effect on the result.

### 4.4 Rebut and Subtyping

Rebut compares evidence: c' = c_for / (c_for + c_against)

**With subtyping**:
- Higher c_for → higher result ✓
- Higher c_against → lower result

**Conclusion**: Similar to undercut—covariant in the "for" belief, contravariant in the "against" belief.

---

## 5. Semantic Models

### 5.1 Set-Theoretic Model

**Interpretation**:
```
⟦Belief<A>[c]⟧ = { (v, c', j, p, I) | v ∈ ⟦A⟧, c' >= c, ... }
```

A belief type denotes the set of beliefs whose confidence is at least the bound.

**Subtyping is set inclusion**:
```
⟦Belief<A>[c]⟧ ⊆ ⟦Belief<A>[c']⟧   when   c >= c'
```

Because any belief with confidence >= c also has confidence >= c' when c >= c'.

### 5.2 Categorical Model

In the category of CLAIR types (formal/categorical-structure.md):

**Objects**: Types
**Morphisms**: Typed functions

Subtyping as morphisms:
```
sub_{c,c'} : Belief<A>[c] → Belief<A>[c']   when c >= c'
```

These are "subsumption morphisms"—they don't change the underlying belief, just relax the type.

**Properties**:
- Identity: sub_{c,c} = id
- Transitivity: sub_{c',c''} ∘ sub_{c,c'} = sub_{c,c''}
- Coherence: Subtyping morphisms commute with operations

### 5.3 Kripke Model

From Thread 2.20 (completeness), CLAIR has Kripke semantics.

**Subtyping in Kripke models**:
```
M, w ⊨ Belief<A>[c]   implies   M, w ⊨ Belief<A>[c']   when c >= c'
```

The truth at a world is upward closed in the lattice of confidence bounds.

---

## 6. Type Checking and Inference

### 6.1 Subsumption Rule

The standard approach is an explicit subsumption rule:

```
Γ ⊢ e : T      T <: T'
────────────────────────── [Sub]
      Γ ⊢ e : T'
```

This allows any well-typed term to be given a supertype.

### 6.2 Bidirectional Type Checking

For better inference, use bidirectional type checking:

**Checking mode** (⇐): Given type, check term
**Synthesis mode** (⇒): Infer type from term

```
Γ ⊢ e ⇒ Belief<A>[c]      c >= c'
────────────────────────────────── [Sub-Check]
     Γ ⊢ e ⇐ Belief<A>[c']
```

Subsumption happens at mode-switching points.

### 6.3 Confidence Inference

**Question**: Can we infer confidence bounds automatically?

**Challenge**: Multiple valid bounds exist for any term.

**Approach 1**: Infer the *tightest* bound (highest confidence):
```
Γ ⊢ e ⇒ Belief<A>[c_max]
```
Then subsumption relaxes as needed.

**Approach 2**: Use constraint-based inference:
- Generate constraints: c₁ >= c₂, c₃ = c₁ × c₂, etc.
- Solve for confidence variables
- Check satisfiability

**Example**:
```
f : Belief<A>[?c₁] → Belief<B>[?c₂]
x : Belief<A>[0.8]
f(x) : Belief<B>[?c₃]

Constraints:
  ?c₁ <= 0.8  (x must satisfy f's requirement)
  ?c₃ = ?c₂   (from function application)
```

### 6.4 Principal Types

**Question**: Does every well-typed term have a principal (most general) type?

In standard type theory, principal types exist when:
- Type inference is decidable
- Types form a lattice with joins

**For CLAIR**:
- Confidence bounds form a lattice ([0,1] with ≤)
- The principal confidence is the *maximum* valid bound
- Join of bounds: max(c₁, c₂) ... but this isn't the principal for the *same* term

**Observation**: For a single term, the principal confidence is unique (the tightest valid bound). The challenge is combining terms.

### 6.5 Decidability

**Theorem** (Confidence Subtyping Decidability): For rational confidence values, subtyping is decidable.

**Proof**: Checking c >= c' for rationals is decidable. ∎

**For real confidence**: May require algebraic decision procedures, but CLAIR-finite (finite lattices) is always decidable.

---

## 7. Design Alternatives

### 7.1 No Subtyping (Explicit Coercion)

Instead of subtyping, require explicit coercions:

```
relax : Belief<A>[c] → Belief<A>[c']   when c >= c'
```

**Pros**:
- Simpler type system
- Confidence changes are explicit
- No hidden subsumption

**Cons**:
- More verbose programs
- Less natural for users

### 7.2 Structural Subtyping Only

Allow subtyping in the value type but not in confidence:

```
     A <: A'
──────────────────────── [Sub-Belief-Struct]
Belief<A>[c] <: Belief<A'][c]
```

**Pros**:
- Confidence bounds are preserved exactly
- Easier to track confidence flow

**Cons**:
- Can't use high-confidence beliefs where low is expected

### 7.3 Bounded Confidence Variables

Use bounded quantification:
```
∀c >= 0.7. Belief<A>[c] → Belief<B>[f(c)]
```

This allows polymorphism over confidence while maintaining bounds.

**Example**:
```
-- Generic confidence-preserving map
map : ∀c >= 0. (A → B) → Belief<A>[c] → Belief<B>[c]
```

### 7.4 Width vs Depth Subtyping

Consider separating:
- **Width subtyping**: Relaxing the confidence bound
- **Depth subtyping**: Subtyping in the value type

```
Belief<A>[c] ≤_width Belief<A>[c']   when c >= c'
Belief<A>[c] ≤_depth Belief<A'>[c]   when A <: A'
```

Combined: ≤ = ≤_width ∪ ≤_depth

---

## 8. Interaction with Dual-Monoid Grading

### 8.1 Subtyping and ×

When combining beliefs via derivation:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Γ ⊢ e₂ : Belief<A → B>[c₂]
────────────────────────────────────────────────────── [Derive]
        Γ ⊢ derive(e₁, e₂) : Belief<B>[c₁ × c₂]
```

With subtyping:
- e₁ : Belief<A>[c₁'] where c₁' >= c₁
- e₂ : Belief<A → B>[c₂'] where c₂' >= c₂
- Result: Belief<B>[c₁' × c₂'] where c₁' × c₂' >= c₁ × c₂

**The multiplication rule is monotone**, so subtyping composes correctly with derivation.

### 8.2 Subtyping and ⊕

When combining independent evidence:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ ⊢ e₂ : Belief<A>[c₂]
──────────────────────────────────────────────── [Agg]
   Γ, Δ ⊢ aggregate(e₁, e₂) : Belief<A>[c₁ ⊕ c₂]
```

With subtyping:
- e₁ : Belief<A>[c₁'] where c₁' >= c₁
- e₂ : Belief<A>[c₂'] where c₂' >= c₂
- Result: Belief<A>[c₁' ⊕ c₂'] where c₁' ⊕ c₂' >= c₁ ⊕ c₂

**The aggregation rule is also monotone**, so subtyping composes correctly with aggregation.

### 8.3 Non-Distributivity and Subtyping

The non-distributivity of × and ⊕ (Thread 2.25) does NOT affect subtyping soundness because:

1. Subtyping is based on the ≤ relation on [0,1]
2. Both × and ⊕ are monotone with respect to ≤
3. Distributivity would only matter if we needed to "factor out" common confidence

**Example**: Consider whether subtyping can exploit distributivity:
```
Belief<A>[a × (b ⊕ c)]  <??>  Belief<A>[(a × b) ⊕ (a × c)]
```

Since these are generally unequal (0.375 vs 0.4375 for a=b=c=0.5), there's no subtyping relationship in either direction for arbitrary values.

**Conclusion**: Non-distributivity doesn't create subtyping issues because we never need to equate these forms.

---

## 9. Formal Specification

### 9.1 Subtyping Judgment

Define the subtyping judgment `T₁ <: T₂`:

**Base types**:
```
────────── [S-Refl]
  B <: B
```

**Belief types**:
```
   A <: A'      c >= c'
────────────────────────── [S-Belief]
Belief<A>[c] <: Belief<A'>[c']
```

**Function types**:
```
  A' <: A      B <: B'
──────────────────────── [S-Fun]
  A → B <: A' → B'
```

**Product types**:
```
  A₁ <: A₁'    A₂ <: A₂'
───────────────────────── [S-Prod]
  A₁ × A₂ <: A₁' × A₂'
```

**Meta-beliefs** (stratified):
```
   A <: A'      c >= c'
────────────────────────── [S-Meta]
Meta<A>[c]ⁿ <: Meta<A'>[c']ⁿ
```

### 9.2 Properties

**Theorem** (Reflexivity): T <: T for all T.
**Proof**: By induction on T. ∎

**Theorem** (Transitivity): If T₁ <: T₂ and T₂ <: T₃, then T₁ <: T₃.
**Proof**: By induction on the derivations. For confidence: c₁ >= c₂ >= c₃ implies c₁ >= c₃. ∎

**Theorem** (Antisymmetry up to equivalence): If T <: T' and T' <: T, then T ≈ T'.
**Proof**: For confidence bounds, c >= c' and c' >= c implies c = c'. ∎

### 9.3 Subsumption Rule

```
Γ ⊢ e : T      T <: T'
──────────────────────── [Sub]
      Γ ⊢ e : T'
```

### 9.4 Type Safety with Subtyping

**Theorem** (Preservation with Subtyping): If Γ ⊢ e : T and e → e', then Γ ⊢ e' : T' for some T' <: T.

**Note**: Confidence may decrease during evaluation (as noted in Thread 2.19, 2.22). This means e' may have type T' with a *lower* confidence bound. But T' <: T fails when c' < c.

**Revised statement**: If Γ ⊢ e : T and e → e', then Γ ⊢ e' : T' where:
- The value type is preserved or subtyped: A' <: A
- The confidence may decrease: c' <= c

This is NOT standard preservation! We need a weaker property:

**Theorem** (Weak Preservation): If Γ ⊢ e : Belief<A>[c] and e →* v (reduces to value), then v has confidence c' where c' may be less than c.

**Why this is okay**: The confidence bound in the type is a *guarantee at construction time*. During evaluation (defeat, rebut), the actual confidence may decrease. The type system doesn't track this dynamically—it tracks the static bound.

### 9.5 Two Interpretations

**Interpretation 1: Static Bounds**
- `Belief<A>[c]` means "constructed with confidence at least c"
- Actual runtime confidence may be lower due to defeat
- Type safety: well-typed programs don't get stuck

**Interpretation 2: Dynamic Bounds**
- `Belief<A>[c]` means "currently has confidence at least c"
- Defeat must be reflected in the type
- Type safety: types track actual confidence

CLAIR uses **Interpretation 1** for practical reasons—tracking dynamic confidence changes in types would require dependent types and make type checking undecidable.

---

## 10. Implementation Considerations

### 10.1 Runtime Representation

With subtyping, the runtime representation doesn't change:
- A `Belief<A>[0.9]` and `Belief<A>[0.7]` have the same memory layout
- Subtyping is a compile-time (type-level) relation only
- No coercion code is generated

### 10.2 Optimization

**Dead confidence tracking**: If a belief's confidence is never inspected, the compiler could elide confidence tracking entirely. Subtyping doesn't affect this.

**Constant confidence**: If all beliefs in a function have confidence bounds that can be computed at compile time, confidence propagation can be done statically.

### 10.3 Error Messages

With subtyping, error messages should explain why subtyping failed:

```
Error: Cannot use Belief<Int>[0.5] where Belief<Int>[0.8] expected
       Confidence 0.5 is less than required 0.8
```

---

## 11. Open Questions

### 11.1 Theoretical Questions

1. **Subtyping with defeat**: Should defeaters have a special subtyping rule reflecting their contravariant effect?

2. **Polymorphism interaction**: How does confidence subtyping interact with parametric polymorphism?

3. **Higher-kinded types**: If Belief is a type constructor, how does subtyping lift?

4. **Gradual typing**: Could CLAIR support gradual confidence where some bounds are unknown?

### 11.2 Practical Questions

1. **Type inference algorithm**: What's the precise algorithm for inferring confidence bounds with subtyping?

2. **Principal types**: Does adding subtyping affect the existence of principal types?

3. **IDE support**: How should tooling visualize confidence subtyping?

---

## 12. Conclusions

### 12.1 Key Findings

1. **Subtyping is sound and natural**: Higher confidence implies usability where lower confidence is expected.

2. **Direction is opposite from resource grading**: In CLAIR, more confidence is a subtype; in resource systems, less usage is a subtype.

3. **Both × and ⊕ are monotone**: Subtyping composes correctly with all CLAIR operations.

4. **Non-distributivity doesn't affect subtyping**: The dual-monoid structure is orthogonal to subtyping soundness.

5. **Static vs dynamic bounds**: CLAIR types express static construction-time bounds; actual confidence may decrease at runtime due to defeat.

6. **Function types follow standard variance**: Contravariant in argument confidence, covariant in result confidence.

### 12.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Subtyping for c >= c' is sound | 0.95 | Standard refinement type argument |
| × and ⊕ are monotone | 0.99 | Mathematical property of [0,1] |
| Non-distributivity is orthogonal to subtyping | 0.90 | Never need to equate non-equal expressions |
| Type inference is decidable (rationals) | 0.85 | Standard constraint solving |
| Static bounds interpretation is correct | 0.80 | Practical but debatable |

### 12.3 Recommendations

1. **Adopt subtyping** with c >= c' implying Belief<A>[c] <: Belief<A>[c']

2. **Use bidirectional type checking** for better inference

3. **Document the static bounds interpretation** clearly

4. **Consider bounded quantification** for polymorphic confidence

5. **Task 2.24 (type inference)** should build on this subtyping foundation

---

## 13. Impact on Other Threads

### Thread 2.24 (Type Inference)
- Subtyping provides the foundation for constraint-based inference
- Inference generates c >= c' constraints solved with linear arithmetic

### Thread 7 (Implementation)
- Runtime representation unchanged by subtyping
- Type checker must implement subsumption

### Thread 8 (Formal Verification)
- Lean formalization should include subtyping judgment
- Prove monotonicity of × and ⊕

### Thread 2.22 (Curry-Howard)
- Subsumption rule corresponds to identity coercion
- Proof terms don't change under subtyping

---

## 14. References

### Primary Sources

- **Rondon, P., Kawaguchi, M., & Jhala, R.** (2008). "Liquid Types." *PLDI 2008*.

- **Vazou, N., Seidel, E.L., Jhala, R., Vytiniotis, D., & Peyton Jones, S.** (2014). "Refinement Types for Haskell." *ICFP 2014*.

- **Cardelli, L. & Wegner, P.** (1985). "On Understanding Types, Data Abstraction, and Polymorphism." *Computing Surveys* 17(4).

- **Orchard, D., Liepelt, V., & Eades, H.** (2019). "Quantitative Program Reasoning with Graded Modal Types." *ICFP 2019*.

### CLAIR Internal

- Thread 2.22: exploration/thread-2.22-curry-howard-terms.md
- Thread 2.25: exploration/thread-2.25-dual-monoid-grading.md
- formal/categorical-structure.md
- formal/belief-types.tex

---

*Thread 2.23 Status: Substantially explored. Subtyping is sound and recommended. Ready for implementation and formalization.*
