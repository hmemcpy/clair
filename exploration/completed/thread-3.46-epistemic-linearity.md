# Thread 3.46: Epistemic Linearity Formalization

> **Status**: Active exploration (Session 72)
> **Task**: 3.46 Can we formalize "epistemic evidence as non-duplicable resource" as a general type-theoretic principle?
> **Question**: Is there a principled way to apply linear logic's resource semantics to epistemic justification?
> **Prior Work**: Thread 3.40 (correlation-aware enforcement), Thread 3.23 (linear types for evidence), Thread 2.13 (correlated evidence)

---

## 1. The Problem

### 1.1 Motivation from Thread 3.40

Thread 3.40 discovered that treating identical self-introspections as independent evidence creates a **bootstrap vulnerability**:

- Multiple introspections of the same self-referential belief, if aggregated as independent, can amplify confidence beyond warranted bounds
- The mitigation: automatic correlation enforcement (δ = 1) for same-self introspections

This is a specific instance of a deeper principle: **the same evidence, counted multiple times, doesn't provide more justification than a single count**.

### 1.2 The General Problem: Evidence Duplication

Throughout CLAIR, we encounter scenarios where evidence "duplication" is problematic:

1. **Self-introspection** (Thread 3.40): `introspect(self) ⊕ introspect(self)` overcounts
2. **Correlated sources** (Thread 2.13): Two news articles citing the same source aren't independent
3. **Shared premises** (Thread 2): DAG structure acknowledges premises can justify multiple conclusions, but each should only "count" once per aggregation
4. **Belief revision** (Thread 5): Retracting one source shouldn't affect confidence more than once, even if it supported multiple paths

### 1.3 The Type-Theoretic Question

Can we express "evidence is a non-duplicable resource" at the type level, analogous to how linear type systems track non-duplicable computational resources?

---

## 2. Linear Logic Background

### 2.1 The Core Insight of Linear Logic

Girard's linear logic (1987) rejects the **structural rule of contraction**:

```
Classical contraction:   Γ, A, A ⊢ B
                        ──────────────
                         Γ, A ⊢ B
```

Contraction says: "if I can prove B using A twice, I can prove it using A once (because I can duplicate A)."

Linear logic says: **No automatic duplication.** If you have one A, you can use it exactly once.

### 2.2 Linear Logic Connectives

Linear logic splits the classical connectives into resource-sensitive versions:

| Classical | Linear (Multiplicative) | Linear (Additive) |
|-----------|-------------------------|-------------------|
| A ∧ B     | A ⊗ B (tensor)          | A & B (with)      |
| A ∨ B     | A ⅋ B (par)             | A ⊕ B (plus)      |
| A → B     | A ⊸ B (lollipop)        | —                 |

Key distinctions:
- **Tensor (⊗)**: "I have A and B simultaneously" (both resources)
- **With (&)**: "I can choose to have A or B, but not both" (one copy, choose use)
- **Plus (⊕)**: "I have either A or B" (resource is one of them)
- **Lollipop (⊸)**: "Consuming A produces B" (linear function)

### 2.3 Exponentials: Controlled Duplication

Linear logic reintroduces controlled duplication via **exponentials**:

```
!A (of course A) — can be duplicated/discarded
?A (why not A)   — dual of !A
```

With `!A`, the structural rules of weakening and contraction are restored:

```
Promotion:     !Γ ⊢ A           Contraction:   !A, !A ⊢ B
              ────────                        ──────────
              !Γ ⊢ !A                          !A ⊢ B
```

The exponential marks **which resources can be freely duplicated**.

### 2.4 Substructural Hierarchy

| Logic | Weakening | Contraction | Exchange |
|-------|-----------|-------------|----------|
| Classical | ✓ | ✓ | ✓ |
| Affine | ✓ | ✗ | ✓ |
| Relevant | ✗ | ✓ | ✓ |
| Linear | ✗ | ✗ | ✓ |
| Ordered | ✗ | ✗ | ✗ |

For epistemic evidence:
- **Weakening** (can discard): Sometimes appropriate—not all available evidence need be used
- **Contraction** (can duplicate): **This is what we want to restrict**
- **Exchange** (can reorder): Generally fine for evidence (order of premises usually doesn't matter)

This suggests **affine logic** (allows weakening, forbids contraction) as a starting point for epistemic linearity.

---

## 3. Epistemic Linearity: The Proposal

### 3.1 Core Principle

**Axiom (Epistemic Non-Duplication)**:
A piece of epistemic evidence, once used to justify a conclusion, cannot be reused independently to provide additional justification for the same conclusion.

Formally: For any evidence e supporting conclusion P:
```
e ⊕ e = e
```

This is **idempotence** of evidence aggregation over identical sources.

### 3.2 What "Same Evidence" Means

The key challenge: When are two pieces of evidence "the same"?

**Level 1: Reference Identity**
```
introspect(self) and introspect(self) — same reference
```

**Level 2: Value Identity**
```
e₁ and e₂ where e₁ = e₂ — same underlying evidence object
```

**Level 3: Informational Identity**
```
e₁ and e₂ where content(e₁) = content(e₂) — same information content
```

**Level 4: Provenance Overlap**
```
e₁ and e₂ share common ancestors in justification DAG
```

Each level captures a different notion of "sameness" relevant to evidence duplication.

### 3.3 Linear Types for Evidence

Introduce a type distinction:

```lean
-- Unrestricted evidence (can be duplicated)
type Evidence<A> = { ... }   -- Normal type, allows contraction

-- Linear evidence (must be used exactly once)
type LinEvidence<A> = { ... }  -- Linear type, no contraction

-- Affine evidence (can be used at most once)
type AffEvidence<A> = { ... }  -- Affine type, allows weakening
```

In CLAIR context:

```clair
-- A belief backed by linear evidence
type LinearBelief<A> = Belief<A> with (evidence : LinEvidence<A>)

-- Aggregation rules differ:
-- For Evidence<A> (unrestricted): e ⊕ e = e ⊕ e (naive, may overcount)
-- For LinEvidence<A> (linear): e ⊕ e is TYPE ERROR (can't use twice)
-- For AffEvidence<A> (affine): e ⊕ e is TYPE ERROR, but e alone is fine
```

### 3.4 Typing Rules

**Unrestricted evidence context**:
```
Γ, e : Evidence<A>, e : Evidence<A> ⊢ conclusion : B
────────────────────────────────────────────────────── (Contraction)
Γ, e : Evidence<A> ⊢ conclusion : B
```

**Linear evidence context**:
```
Δ is a LINEAR context (each evidence used exactly once)

Δ₁ ⊢ M : A    Δ₂ ⊢ N : B
────────────────────────── (Tensor-intro)
Δ₁, Δ₂ ⊢ (M, N) : A ⊗ B
```

The key: when aggregating beliefs with linear evidence, each piece of evidence goes to exactly one use.

---

## 4. Information-Theoretic Foundation

### 4.1 Shannon's Insight on Redundancy

Shannon's information theory provides theoretical grounding:

**Mutual Information**: For random variables A and B,
```
I(A; B) = H(A) + H(B) - H(A, B)
```

When A and B are identical (A = B):
```
I(A; A) = H(A) + H(A) - H(A) = H(A)
```

**The information content of A observed twice is the same as A observed once.**

This is exactly what epistemic linearity captures at the logical level.

### 4.2 Information Gain from Evidence

Define the **information gain** from evidence e supporting P:
```
IG(e → P) = log(P(P | e) / P(P))
```

For identical evidence:
```
IG(e → P) + IG(e → P) ≠ IG(e, e → P)  when e and e are correlated
```

In the limit of perfect correlation (same evidence):
```
IG(e, e → P) = IG(e → P)   (no additional information)
```

### 4.3 The Redundancy Interpretation

In CLAIR's aggregation:
```
c ⊕ c = c + c - c×c = 2c - c²
```

This is **greater than c** (for 0 < c < 1), suggesting the two uses provide additional justification.

But if the two `c` values come from the **same evidence**, this overcounts. The "correct" aggregate is:
```
c ⊕_δ=1 c = (c + c)/2 = c    (via correlation-aware aggregation)
```

Linear types would prevent the first (incorrect) form at the type level.

---

## 5. Design Integration with CLAIR

### 5.1 The Affine Evidence Type

I propose **affine** rather than strict linear types for CLAIR evidence:

```lean
-- Affine: can use at most once (allows weakening, forbids contraction)
structure AffineEvidence (α : Type) where
  content : α
  used : Bool := false  -- Track usage at runtime
  deriving Repr

-- Linear: must use exactly once (forbids both)
-- More restrictive; may be too burdensome for practical use
```

**Rationale**: Not all evidence *must* be used (weakening is epistemically acceptable—we can hold evidence without incorporating it). But evidence *should not* be counted multiple times (contraction is problematic).

### 5.2 Affine Aggregation Rule

```lean
-- Aggregation that consumes both pieces of evidence
def aggregate (e₁ : AffineEvidence Confidence) (e₂ : AffineEvidence Confidence)
              (h_distinct : e₁.id ≠ e₂.id) -- Must be distinct evidence
              : AffineEvidence Confidence :=
  { content := e₁.content ⊕ e₂.content
  , id := fresh_id()
  , consumed := [e₁, e₂] }
```

The `h_distinct` proof obligation ensures no double-counting at compile time.

### 5.3 Exponential for Reusable Evidence

Some evidence genuinely can be reused:
- **Axioms**: Mathematical truths can support multiple conclusions
- **Definitions**: Type definitions can be referenced multiple times
- **Published facts**: Well-established knowledge is freely duplicable

Mark these with the exponential:

```clair
-- Unrestricted evidence (marked with !)
let axiom : !Evidence<"2+2=4"> = ...

-- Can be used multiple times
let proof1 = derive ... using axiom
let proof2 = derive ... using axiom  -- Same axiom, OK
```

### 5.4 Interaction with Stratified Introspection

Thread 3's stratification + Thread 3.40's correlation enforcement + epistemic linearity form a coherent system:

| Mechanism | Prevents |
|-----------|----------|
| Stratification | Paradoxical self-reference |
| Correlation enforcement | Bootstrap via same-self aggregation |
| Affine typing | All evidence duplication at type level |

Affine typing is the most general; the others are specific instantiations for self-reference scenarios.

---

## 6. Formal Analysis

### 6.1 What Epistemic Linearity Captures

**Theorem (Evidence Non-Duplication Principle)**:
Let e be a piece of affine evidence with confidence c. Let A(e) denote the aggregate confidence when e is used. Then for any valid CLAIR derivation:
```
A(e) = A(e, e) = A(e, e, ..., e)  (any finite number of uses)
```

**Proof sketch**:
Affine typing prevents multiple uses of the same e. If e appears twice, one of:
1. Type error (rejected at compile time), or
2. The second is actually a copy (!e), which is semantically distinct, or
3. The system applies correlation-aware aggregation (δ = 1)

In all valid cases, the aggregate respects evidence identity. ∎

### 6.2 Idempotence vs. Affine Typing

Two approaches to the same goal:

**Approach 1: Semantic Idempotence**
```
Make aggregation idempotent over identical evidence:
e ⊕_id e = e
```
Pro: Simple semantics, no type-level changes
Con: Requires runtime identity checking

**Approach 2: Affine Typing**
```
Prevent identical evidence from being aggregated:
aggregate(e, e) is ill-typed
```
Pro: Static guarantee, no runtime overhead
Con: More complex type system

CLAIR can support both:
- Affine types for **static** prevention where evidence identity is known
- Correlation-aware aggregation for **dynamic** handling where identity determined at runtime

### 6.3 Soundness Condition

**Theorem (Epistemic Linearity Soundness)**:
If CLAIR's type system enforces affine evidence typing, then no well-typed derivation overcounts evidence.

**Proof sketch**:
1. By affine typing, each evidence variable e appears at most once in any derivation
2. Unrestricted evidence (!e) is semantically marked as freely duplicable
3. Correlation-aware aggregation handles runtime-discovered correlations
4. By exhaustion, all evidence sources are counted appropriately. ∎

---

## 7. Limitations and Challenges

### 7.1 The Identification Problem

Epistemic linearity works best when evidence identity is clear. Challenges arise when:

1. **Reformulated evidence**: Same information in different form
   - "The sky is blue" and "Blue is the color of the sky"
   - Logically equivalent, but syntactically distinct

2. **Partial overlap**: Evidence shares some but not all information
   - Two studies that share half their data points

3. **Emergent correlation**: Evidence that becomes correlated through reasoning
   - Initially independent facts that turn out to share a common cause

Linear types can't fully solve these—they're fundamentally about *reference* identity, not *informational* identity.

### 7.2 The Granularity Problem

What counts as "one piece of evidence"?

- A single observation?
- A single premise in a derivation?
- An entire justification chain?

Different granularities lead to different typing disciplines.

### 7.3 Expressiveness vs. Safety Trade-off

Strict affine typing may reject useful programs:

```clair
-- May want to use same evidence to support two related conclusions
let evidence = observe("temperature is high")
let conclusion1 = derive("it's hot") from evidence
let conclusion2 = derive("cooling needed") from evidence
-- With strict affine: error—evidence used twice
-- But this seems legitimate?
```

**Resolution**: The exponential (!) marks evidence that can be freely reused:
```clair
let evidence : !Evidence<...> = observe("temperature is high")
-- Now can use multiple times
```

But then the burden is on the programmer to correctly mark reusable evidence.

### 7.4 Relation to Correlation Parameter δ

Thread 2.13's correlation-aware aggregation is a **soft** version of epistemic linearity:

| δ value | Meaning | Linear analogue |
|---------|---------|-----------------|
| δ = 0 | Fully independent | Both evidence valid, aggregate via ⊕ |
| 0 < δ < 1 | Partially correlated | "Partial" duplication |
| δ = 1 | Fully correlated | Same evidence, linear restriction applies |

Linear types are the **limit case** where δ = 1 is enforced at type level.

---

## 8. Implementation Sketch

### 8.1 Type System Extension

Add multiplicity annotations to CLAIR types:

```lean
-- Multiplicity for evidence usage
inductive Multiplicity where
  | linear    -- Exactly once
  | affine    -- At most once
  | relevant  -- At least once
  | unlimited -- Any number

-- Evidence type with multiplicity
structure TypedEvidence (m : Multiplicity) (α : Type) where
  content : α
  confidence : Confidence
```

### 8.2 Context Splitting

Aggregation requires **context splitting**:

```lean
-- Linear context: maps evidence IDs to their types
def LinCtx := List (EvidenceId × Multiplicity × Type)

-- Judgment: Δ ⊢ e : B means "using evidence in Δ, derive B"
-- Context must be split appropriately

-- Aggregation rule with split contexts:
-- Δ₁ ⊢ e₁ : B    Δ₂ ⊢ e₂ : B    Δ₁ ∩ Δ₂ = ∅ (disjoint!)
-- ───────────────────────────────────────────────────────
--        Δ₁ ∪ Δ₂ ⊢ aggregate(e₁, e₂) : B
```

The **disjointness condition** (Δ₁ ∩ Δ₂ = ∅) ensures no evidence is used in both.

### 8.3 The Exponential Zone

Track "exponential zone" for freely duplicable evidence:

```lean
-- Judgment with two contexts: linear (Δ) and exponential (Γ)
-- Γ; Δ ⊢ e : B
-- Γ is unrestricted (can use any evidence any number of times)
-- Δ is linear (each evidence used exactly once)

-- Promotion: if derivation uses only exponential evidence, result is exponential
-- Γ; · ⊢ e : B
-- ─────────────
-- Γ; · ⊢ !e : !B
```

### 8.4 Practical Defaults

For ergonomics, CLAIR could default to:
- **Self-introspections**: Always affine (can't duplicate)
- **External evidence**: Unrestricted by default, opt-in to affine
- **Aggregation**: Automatically check for duplicates, warn if found

This matches Thread 3.40's "Alternative B" approach.

---

## 9. Prior Art Connections

### 9.1 Linear Logic (Girard 1987)

CLAIR's epistemic linearity is a domain-specific application of Girard's resource semantics. The connection:

| Linear Logic | Epistemic Linearity |
|--------------|---------------------|
| Resource | Evidence |
| Contraction (forbidden) | Evidence duplication (forbidden) |
| Weakening (allowed/forbidden) | Unused evidence (typically allowed) |
| Exponential (!) | Axioms, definitions, common knowledge |

### 9.2 Linear Types in Programming Languages (Wadler 1990, Pierce & Turner 2000)

- **Linear Haskell**: Wadler's proposal for linear types in functional languages
- **Rust's ownership**: Affine types enforcing memory safety
- **Clean's uniqueness types**: Ensuring in-place updates

CLAIR extends these ideas from computational resources to epistemic resources.

### 9.3 Relevance Logic (Anderson & Belnap 1975)

Relevance logic forbids "irrelevant" premises—the conclusion must actually depend on the premises. This is **weakening** (using premises without needing them).

Interestingly, relevance logic allows **contraction** (using a premise multiple times), which is what we want to restrict. So CLAIR's epistemic linearity is more aligned with **affine** logic than relevance logic.

### 9.4 Information Theory (Shannon 1948)

As noted in §4, Shannon's theory grounds the principle: information content is not additive over redundant sources. Epistemic linearity is the logical/type-theoretic encoding of this informational principle.

### 9.5 Dempster-Shafer Cautious Rule (Smets 1993)

The cautious combination rule in evidence theory is **idempotent**: m ∧ m = m. This achieves the same effect as epistemic linearity through different means (semantic rather than syntactic).

---

## 10. Open Questions

### 10.1 Decidability of Linearity Checking

Is it decidable whether a CLAIR program respects affine evidence usage?

**Conjecture**: Yes, for the stratified fragment. Linearity checking is known to be decidable for linear lambda calculus, and CLAIR's stratification prevents problematic self-reference.

### 10.2 Gradual Linearity

Could CLAIR support "gradual" linearity—allowing unchecked programs but tracking potential violations?

Analogous to gradual typing: start untyped, add linear annotations incrementally.

### 10.3 Linearity and Defeat

How does epistemic linearity interact with defeat?

If evidence e supports P, and e is undercut, can e still be used elsewhere? The undercut "marks" e as compromised, but doesn't delete it. What's the linear semantics?

### 10.4 Linearity Across Conversations

CLAIR conversations are bounded. Does evidence linearity persist across conversations? If I use evidence e in conversation 1, can I use it "again" in conversation 2?

The answer depends on whether "conversation-local" linearity is the right scope, or whether there's a notion of "global" evidence that accumulates.

---

## 11. Recommendations

### 11.1 Adopt Affine Semantics for Self-Introspection

**Recommendation**: CLAIR should treat self-introspections as affine by default.

Justification:
- Thread 3.40 already establishes the need for correlation enforcement
- Affine typing provides static guarantees beyond runtime checks
- Aligns with linear logic's resource semantics

### 11.2 Exponential for Axioms and Definitions

**Recommendation**: CLAIR should mark axioms, definitions, and established facts with the exponential (!), allowing unrestricted reuse.

Justification:
- Some evidence genuinely is reusable
- Matches epistemic practice (axioms support many conclusions)
- Provides escape hatch from strictness

### 11.3 Default to Correlation-Aware Aggregation

**Recommendation**: CLAIR's aggregation should use correlation-aware semantics (δ-parameterized) with automatic δ inference from evidence identity.

Justification:
- Handles runtime-discovered correlation
- Graceful degradation when static analysis is insufficient
- Subsumes strict linearity (δ = 1 case)

### 11.4 Optional Strict Linear Mode

**Recommendation**: CLAIR could offer a "strict linear mode" where all evidence is affine by default, for users who want maximum static guarantees.

Justification:
- Some applications may prefer static safety over expressiveness
- Educational value in making resource discipline explicit

---

## 12. Conclusion

### 12.1 Summary

**Task 3.46 is substantially answered.**

Epistemic linearity—the principle that evidence should not be counted multiple times—can be formalized as a type-theoretic principle using affine types. The key insights:

1. **Linear logic provides the foundation**: Forbidding contraction captures evidence non-duplication
2. **Affine is the right discipline**: Allow weakening (unused evidence OK), forbid contraction (duplication not OK)
3. **Exponentials mark reusable evidence**: Axioms, definitions get the ! modifier
4. **Correlation-aware aggregation is the semantic counterpart**: δ = 1 achieves idempotence when linearity can't be statically enforced
5. **Information theory grounds the principle**: Redundant information doesn't add to information content

### 12.2 Key Theorems

**Axiom (Epistemic Non-Duplication)**:
```
e ⊕_id e = e
```
The same evidence, counted twice, provides no more justification than counted once.

**Soundness (Affine Typing)**:
If CLAIR's type system enforces affine evidence typing, no well-typed derivation overcounts evidence.

### 12.3 Confidence Table

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Evidence non-duplication is a valid epistemic principle | 0.95 | Information-theoretic grounding |
| Affine types capture non-duplication | 0.90 | Direct correspondence to forbidden contraction |
| Affine (not strict linear) is right for CLAIR | 0.85 | Weakening is epistemically acceptable |
| Correlation-aware aggregation is the semantic counterpart | 0.90 | δ = 1 achieves same effect |
| Full integration is tractable | 0.75 | Requires type system extension |
| Decidability for stratified fragment | 0.80 | Linear type checking is decidable |

### 12.4 Impact on CLAIR

This formalization:
- Provides theoretical grounding for Thread 3.40's design
- Unifies several phenomena under one principle (self-introspection, correlated sources, shared premises)
- Opens path to static guarantees beyond runtime correlation checking
- Connects CLAIR to the rich tradition of substructural logic

### 12.5 New Questions Raised

- **3.47**: Full Lean formalization of affine evidence types
- **3.48**: Interaction between epistemic linearity and defeat
- **3.49**: Decidability proof for CLAIR with affine evidence
- **3.50**: Gradual linearity for incremental adoption

---

## 13. References

### CLAIR Internal

- Thread 3.40: exploration/thread-3.40-correlation-aware-introspection-enforcement.md
- Thread 3.23: (referenced in IMPLEMENTATION_PLAN.md)
- Thread 2.13: exploration/thread-2.13-correlated-evidence.md

### External

- **Girard, J-Y.** (1987). "Linear Logic." *Theoretical Computer Science*.
  - [Linear Logic (Stanford Encyclopedia)](https://plato.stanford.edu/entries/logic-linear/)
  - [Linear Logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_logic)

- **Wadler, P.** (1990). "Linear Types Can Change the World!" *Programming Concepts and Methods*.

- **Walker, D.** (2005). "Substructural Type Systems." *Advanced Topics in Types and Programming Languages*.
  - [Substructural Type Systems (Harvard)](https://groups.seas.harvard.edu/courses/cs152/2019sp/lectures/lec17-substructural.pdf)

- **Shannon, C.** (1948). "A Mathematical Theory of Communication." *Bell System Technical Journal*.

- **Anderson, A.R. & Belnap, N.D.** (1975). *Entailment: The Logic of Relevance and Necessity*.
  - [Substructural Logics (Stanford Encyclopedia)](https://plato.stanford.edu/entries/logic-substructural/)

- **Smets, P.** (1993). "Belief Functions: The Disjunctive Rule of Combination and the Generalized Bayesian Theorem." *IJAR*.

- **Double Counting in Fine-Tuning Arguments**:
  - [Fine-tuning as Old Evidence, Double Counting, and the Multiverse](https://www.tandfonline.com/doi/full/10.1080/02698595.2019.1565214)

---

*Thread 3.46 Status: Substantially explored. Epistemic linearity formalized as affine type discipline forbidding evidence contraction. Information-theoretic grounding established. Integration path with Thread 3.40's correlation enforcement identified. Ready for type system implementation.*
