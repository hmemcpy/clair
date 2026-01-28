# Thread 2.17: Justification Equivalence and Normal Forms

> **Status**: Active exploration (Session 58)
> **Task**: 2.17 When are two CLAIR justification DAGs "equivalent"? Normal forms?
> **Question**: What is the correct notion of equivalence for CLAIR justifications, and how do normal forms arise?
> **Prior Work**: Thread 2.16 (sequent calculus), Thread 2.19 (cut elimination), Thread 2.22 (Curry-Howard), Thread 2.25 (dual-monoid grading)

---

## 1. The Problem

### 1.1 Why Justification Equivalence Matters

CLAIR beliefs carry explicit justifications—the derivational history explaining *why* a belief is held. Two beliefs about the same proposition can have different justifications:

```
Belief₁: "The sky is blue" with confidence 0.8
         Justified by: observation + scientific explanation

Belief₂: "The sky is blue" with confidence 0.8
         Justified by: trusted source testimony
```

**Key question**: When should we consider two justifications "equivalent"?

This matters for:
1. **Optimization**: Can we simplify justification DAGs without losing meaning?
2. **Identity**: When are two beliefs "the same belief"?
3. **Caching**: Can we share equivalent justification sub-DAGs?
4. **Type checking**: When do two derivations produce the same typed belief?
5. **Semantic correctness**: Does equivalence preserve confidence and meaning?

### 1.2 Candidate Notions of Equivalence

Several notions are possible:

| Equivalence | Definition | Captures |
|-------------|------------|----------|
| **Syntactic** | Identical DAG structure | Strong identity |
| **Structural** | Isomorphic DAGs (up to renaming) | Graph identity |
| **Semantic** | Same confidence and conclusion | Belief identity |
| **Definitional** | Same normal form | Computational identity |
| **Intensional** | Same derivation steps | Proof identity |
| **Extensional** | Same model-theoretic truth | Truth-functional |

**Claim**: The right notion for CLAIR is **definitional equivalence via normal forms**, which lies between intensional and extensional.

### 1.3 The Normal Form Approach

From Thread 2.19 (cut elimination), we know:

> Cut-free derivations exist for all provable sequents. These define **normal forms**.

The cut elimination theorem suggests:

**Definition (Justification Normal Form)**: A justification j is in **normal form** if:
1. The corresponding sequent derivation is cut-free
2. All aggregations are fully expanded
3. No unnecessary weakenings remain
4. All defeat operations are at leaves (applied as early as possible)

**Definition (Justification Equivalence)**: Two justifications j₁ and j₂ are **equivalent** (j₁ ≃ j₂) if they have the same normal form.

---

## 2. Prior Art Survey

### 2.1 Proof Equivalence in Type Theory

In type theory (Martin-Löf, Coq, Agda, Lean):

**Definitional/Judgmental Equality**: Two terms are judgmentally equal if they reduce to the same normal form via computation rules. Written `t ≡ s` or `t =_{def} s`.

**Propositional Equality**: Two terms are propositionally equal if there exists a proof of `t = s`. Weaker than judgmental equality.

**Key insight for CLAIR**: Justification equivalence should be **definitional** (computable), not just propositional (provable).

### 2.2 Proof Equivalence in Justification Logic

Artemov's Justification Logic (JL) has proof terms:
- `t : A` means "t is a justification for A"
- `t · s` for application
- `t + s` for sum (choice)
- `!t` for proof checker

**JL equivalence**: In JL, proof terms are **intentionally different**. Two proofs t and s are equivalent only if syntactically identical (no quotient).

**CLAIR difference**: CLAIR has richer structure (confidence, defeat, DAGs). We need a more refined notion.

### 2.3 Cut Elimination and Normal Forms

**Gentzen's insight**: Cut elimination produces proofs in a canonical form where:
1. All reasoning is "direct" (no lemmas)
2. Subformula property holds
3. Proof search becomes systematic

**For CLAIR** (Thread 2.19): Cut elimination holds with the caveat that confidence may decrease. This means:
- Normal forms exist
- But confidence in normal form c' ≤ c
- The same conclusion may have multiple cut-free derivations with different confidences

### 2.4 Coherence in Category Theory

In category theory, **coherence theorems** show that diagrams commute:
- Mac Lane's coherence for monoidal categories
- All paths give the same result

**For CLAIR**: Do all equivalent derivations give the same confidence? This is the **coherence question**.

### 2.5 Term Rewriting and Confluence

**Church-Rosser / Confluence**: If a term can reduce in multiple ways, all paths eventually meet (same normal form).

**Strong normalization**: All reduction sequences terminate.

**For CLAIR** (from Thread 2.22): Cut elimination implies strong normalization. The question is: is the reduction relation confluent?

---

## 3. Analysis: What Should Equivalence Preserve?

### 3.1 Dimensions of Justification

A CLAIR justification j has multiple aspects:

| Dimension | Description | Preserved by equivalence? |
|-----------|-------------|---------------------------|
| **Conclusion** | What proposition is believed | ✓ Must preserve |
| **Confidence** | Degree of belief | Partially (may decrease in NF) |
| **Structure** | DAG topology | ✗ Can simplify |
| **Labels** | Support/undercut/rebut edges | ✓ Must preserve type |
| **Provenance** | Source information | ✓ Must preserve |
| **Steps** | Exact derivation sequence | ✗ Can vary |

### 3.2 Confidence and Equivalence

**Critical observation**: Two derivations of the same conclusion can have different confidences:

```
Derivation A:
  Premise P with confidence 0.9
  Premise Q with confidence 0.8
  Derive P ∧ Q with confidence 0.9 × 0.8 = 0.72

Derivation B:
  Aggregate two witnesses for P ∧ Q
  Combined confidence: 0.6 ⊕ 0.5 = 0.8
```

Both conclude P ∧ Q, but with different confidences (0.72 vs 0.80).

**Should these be equivalent?**

**No.** Confidence is part of the belief's identity. Different confidences mean different epistemic commitments.

**Refined definition**: j₁ ≃ j₂ iff they have the same normal form **and** the same (or compatible) confidence.

### 3.3 The Coherence Problem

**Question**: When two derivations are "structurally similar," do they yield the same confidence?

Consider:
```
Path 1: derive(derive(a, b), c)  →  conf = (c_a × c_b) × c_c
Path 2: derive(a, derive(b, c))  →  conf = c_a × (c_b × c_c)
```

By associativity of ×, these are equal: (c_a × c_b) × c_c = c_a × (c_b × c_c).

**Theorem (Derivation Coherence)**: Confidence is invariant under associative restructuring of derivation (because × is associative and commutative).

**But**: Aggregation (⊕) and derivation (×) do NOT distribute (Thread 2.25). So:
```
derive(aggregate(a, b), c)  →  conf = (c_a ⊕ c_b) × c_c
aggregate(derive(a, c), derive(b, c))  →  conf = (c_a × c_c) ⊕ (c_b × c_c)
```

These are **not equal** in general!

Example: c_a = 0.5, c_b = 0.5, c_c = 0.5
- Left: (0.5 ⊕ 0.5) × 0.5 = 0.75 × 0.5 = 0.375
- Right: (0.5 × 0.5) ⊕ (0.5 × 0.5) = 0.25 ⊕ 0.25 = 0.4375

**This is mathematically expected** (Thread 2.25): CLAIR's dual-monoid structure doesn't have distributivity.

### 3.4 Implications for Equivalence

**Key insight**: Equivalence must respect the non-distributivity of × and ⊕.

Two justifications are equivalent only if:
1. Same derivation structure (which operations, in what order)
2. Same defeat structure (what defeats what)
3. Same provenance
4. Resulting in same confidence (follows from 1-3)

**Structural changes that preserve equivalence**:
- Associativity of ×: derive(derive(a,b),c) ≃ derive(a,derive(b,c))
- Associativity of ⊕: agg(agg(a,b),c) ≃ agg(a,agg(b,c))
- Commutativity of ×: derive(a,b) ≃ derive(b,a) (for symmetric rules)
- Commutativity of ⊕: agg(a,b) ≃ agg(b,a)
- Identity for ×: derive(a, certainty) ≃ a (where certainty has conf 1)
- Identity for ⊕: agg(a, vacuum) ≃ a (where vacuum has conf 0)

**Structural changes that DON'T preserve equivalence**:
- Distributing × over ⊕: NOT equivalent (different confidence)
- Swapping derivation and aggregation order: NOT equivalent

---

## 4. Normal Form Definition

### 4.1 Justification Term Syntax (from Thread 2.22)

```
j ::= x                         -- justification variable
   | axiom(name)                -- axiomatic justification
   | rule(r, [j₁,...,jₙ])       -- derivation rule application
   | agg([j₁,...,jₙ])           -- aggregated justification
   | undercut(j, j_d)           -- undercut justification
   | rebut(j_for, j_against)    -- rebut justification
   | cut(j₁, j₂)                -- composition (corresponds to let-binding)
```

### 4.2 Reduction Rules

**Cut reduction** (from cut elimination):
```
cut(rule(r, [j₁,...,jₙ]), j') →  [reduction based on rule r]
```

**Aggregation normalization**:
```
agg([]) → identity_⊕            -- empty aggregation
agg([j]) → j                    -- singleton
agg([..., agg([j₁,...,jₖ]), ...]) → agg([..., j₁,...,jₖ, ...])  -- flattening
```

**Defeat normalization** (push defeats to leaves):
```
undercut(rule(r, js), j_d) → rule(r, [undercut(j, j_d) for j in js if defeated])
```

**Commutativity/Associativity** (canonical ordering):
```
agg([j₂, j₁]) → agg([j₁, j₂])   when j₁ < j₂ (lexicographic order)
rule(r, [j₂, j₁]) → rule(r, [j₁, j₂])   for commutative rules
```

### 4.3 Normal Form Characterization

**Definition**: A justification j is in **normal form** if:

1. **Cut-free**: No `cut` terms appear
2. **Flat aggregations**: All `agg` have non-`agg` children
3. **Ordered**: Children of `agg` and commutative rules are in canonical order
4. **Reduced**: No identity elements (conf-1 derivations, conf-0 aggregations)
5. **Defeat-early**: All defeat operations at leaves where possible

**Theorem (Normal Form Existence)**: Every well-typed justification has a unique normal form.

**Proof sketch**:
1. **Existence**: By cut elimination (Thread 2.19) + flattening + ordering
2. **Uniqueness**: Each reduction rule is confluent; the canonical ordering ensures a unique representative

### 4.4 The Equivalence Relation

**Definition**: j₁ ≃ j₂ (justification equivalence) iff nf(j₁) = nf(j₂), where nf is the normal form function.

**Properties**:
- **Reflexive**: j ≃ j (trivially)
- **Symmetric**: j₁ ≃ j₂ implies j₂ ≃ j₁ (same normal form)
- **Transitive**: j₁ ≃ j₂ and j₂ ≃ j₃ implies j₁ ≃ j₃ (same normal form)
- **Congruence**: j₁ ≃ j₁' implies rule(r, [..., j₁, ...]) ≃ rule(r, [..., j₁', ...])

---

## 5. Confidence Preservation

### 5.1 Confidence Under Normalization

**Question**: Does normalization preserve confidence?

From Thread 2.19:
> Confidence may decrease during cut elimination: c' ≤ c

So normalization may **decrease** but never **increase** confidence.

**Definition**: The **canonical confidence** of a proposition A is:
```
canon_conf(A) = max { conf(j) | j is a normal form justification for A }
```

This is the highest confidence achievable through any normalized derivation.

### 5.2 Confidence-Indexed Equivalence

For stronger equivalence that preserves confidence exactly:

**Definition**: j₁ ≃_c j₂ (confidence-preserving equivalence) iff:
1. nf(j₁) = nf(j₂)
2. conf(j₁) = conf(j₂)

This is stricter than ≃ and captures when two justifications are "computationally identical."

### 5.3 When Confidence is Preserved

Confidence is preserved when:
- No cuts are eliminated (already in normal form)
- Only associativity/commutativity transformations applied
- No intermediate confidences are lost

**Theorem**: If j is cut-free, then conf(nf(j)) = conf(j).

**Proof**: The only normalization steps for cut-free terms are:
- Flattening aggregations: preserves ⊕ structure
- Reordering: commutativity preserves values
- Neither changes the confidence computation.

---

## 6. Operational Semantics of Equivalence

### 6.1 Reduction System

Define a one-step reduction relation j →₁ j':

**Cut reductions**:
```
cut(axiom(a), j') →₁ j'[a/x]          -- substitute axiom
cut(rule(r, js), j') →₁ [principal reduction based on r]
```

**Aggregation reductions**:
```
agg([..., agg(js), ...]) →₁ agg([..., js, ...])   -- flatten
agg([j]) →₁ j                                     -- singleton
```

**Ordering reductions**:
```
agg([j₂, j₁]) →₁ agg([j₁, j₂])   when j₁ < j₂    -- sort
```

**Defeat reductions**: (Push toward leaves where legal)
```
undercut(agg([j₁, j₂]), d) →₁ agg([undercut(j₁, d), undercut(j₂, d)])
```

Wait—this last rule is questionable. Does undercut distribute over aggregation?

### 6.2 Does Undercut Distribute Over Aggregation?

**Semantic question**: If I have aggregated evidence j₁ ⊕ j₂ for A, and d defeats the justification, what happens?

**Option 1: Undercut the aggregate**
```
undercut(agg([j₁, j₂]), d)
conf = (c₁ ⊕ c₂) × (1 - d)
```

**Option 2: Undercut each component**
```
agg([undercut(j₁, d), undercut(j₂, d)])
conf = (c₁ × (1-d)) ⊕ (c₂ × (1-d))
```

Are these equal? Let's check:
- Option 1: (c₁ ⊕ c₂) × (1-d) = (c₁ + c₂ - c₁c₂)(1-d)
- Option 2: (c₁(1-d)) ⊕ (c₂(1-d)) = c₁(1-d) + c₂(1-d) - c₁c₂(1-d)²

Let c₁ = c₂ = 0.5, d = 0.5:
- Option 1: (0.5 + 0.5 - 0.25)(0.5) = 0.75 × 0.5 = 0.375
- Option 2: 0.25 + 0.25 - 0.25 × 0.25 = 0.5 - 0.0625 = 0.4375

**They differ!** This means undercut does NOT distribute over aggregation.

**Conclusion**: The reduction `undercut(agg([j₁, j₂]), d) →₁ agg([undercut(j₁, d), undercut(j₂, d)])` is **NOT valid**.

This is consistent with Thread 2.25's finding that CLAIR has a De Morgan bimonoid structure without distributivity.

### 6.3 Revised Reduction Rules

The correct reductions preserve the non-distributivity:

**Undercut stays "outside"**:
```
undercut(agg(js), d) →₁ undercut(agg(js), d)   -- no change; this IS normal form
```

**Undercut can push through derivation** (because × is on both sides):
```
undercut(rule(r, [j]), d) →₁ rule(r, [undercut(j, d)])   -- for single-premise rules
```

For multi-premise rules, it depends on whether the defeat targets all premises or specific ones. This requires tracking which justification edges the defeat attacks.

### 6.4 Confluence

**Theorem (Local Confluence)**: The reduction system is locally confluent.

**Proof sketch**: Each critical pair (where two rules overlap) can be resolved:
- Cut/Cut: Standard Gentzen argument
- Agg/Agg: Flattening is idempotent
- Order/Order: Sorting is deterministic

**Corollary (Confluence)**: By Newman's lemma (local confluence + termination → confluence).

**Corollary (Uniqueness of Normal Forms)**: Every justification has a unique normal form.

---

## 7. Algorithmic Aspects

### 7.1 Computing Normal Forms

```python
def normalize(j: Justification) -> Justification:
    """Compute the normal form of a justification."""

    # Step 1: Eliminate cuts (most complex part)
    j = eliminate_cuts(j)

    # Step 2: Flatten aggregations
    j = flatten_aggregations(j)

    # Step 3: Sort children
    j = sort_children(j)

    # Step 4: Remove identities
    j = remove_identities(j)

    return j

def eliminate_cuts(j: Justification) -> Justification:
    """Gentzen-style cut elimination."""
    match j:
        case Cut(j1, j2):
            j1_nf = eliminate_cuts(j1)
            j2_nf = eliminate_cuts(j2)
            return reduce_cut(j1_nf, j2_nf)
        case Rule(r, js):
            return Rule(r, [eliminate_cuts(jj) for jj in js])
        case Agg(js):
            return Agg([eliminate_cuts(jj) for jj in js])
        case Undercut(j, d):
            return Undercut(eliminate_cuts(j), eliminate_cuts(d))
        case _:
            return j

def reduce_cut(j1: Justification, j2: Justification) -> Justification:
    """Principal cut reduction."""
    # ... complex case analysis based on Thread 2.19
    pass
```

### 7.2 Complexity

**Question**: What is the complexity of normalization?

**Cut elimination complexity**: In the worst case, cut elimination can be non-elementary (tower of exponentials). However:
- For propositional CLAIR: at most doubly exponential
- For CLAIR-finite: polynomial in the size of the proof (finite search space)
- For already cut-free terms: linear (just flattening and sorting)

**Practical observation**: Most CLAIR justifications in practice will be shallow and nearly cut-free, making normalization fast.

### 7.3 Checking Equivalence

```python
def equivalent(j1: Justification, j2: Justification) -> bool:
    """Check if two justifications are equivalent."""
    return normalize(j1) == normalize(j2)
```

This is decidable whenever normalization terminates (which it does by strong normalization).

---

## 8. Connection to Belief Identity

### 8.1 When Are Two Beliefs "The Same"?

A CLAIR belief is: `Belief<A>[c] with justification j`

**Definition**: Two beliefs B₁ = (A, c₁, j₁) and B₂ = (A, c₂, j₂) are **equivalent** if:
1. Same proposition: A = A
2. Same confidence: c₁ = c₂
3. Equivalent justification: j₁ ≃ j₂

Note: If j₁ ≃ j₂ (same normal form), they should yield the same confidence, so condition 2 follows from condition 3 in most cases.

### 8.2 Belief Identity vs Provenance

**Subtle point**: Two beliefs might be "logically equivalent" but have different **provenance**.

Example:
```
B₁: "Water is H₂O" justified by chemistry textbook
B₂: "Water is H₂O" justified by physics professor
```

If these have the same confidence and normalize to the same form, they're equivalent **as beliefs**. But the provenance information (source) differs.

**CLAIR's stance**: Provenance is part of the justification. If provenance differs, the justifications differ, so the beliefs are **not equivalent** unless we explicitly quotient by provenance.

### 8.3 Provenance-Agnostic Equivalence

For some applications, we might want equivalence that ignores provenance:

**Definition**: j₁ ≃_p j₂ (provenance-agnostic equivalence) if:
- nf(j₁) and nf(j₂) have the same **structure** and **confidence**
- But possibly different source annotations

This is a coarser equivalence, useful for caching and optimization.

---

## 9. Formalization in Type Theory

### 9.1 Setoid Structure

In type theory, we can model justification equivalence as a **setoid**:

```lean
structure Justification where
  data : JustificationData
  conf : Confidence

def JustificationEquiv (j1 j2 : Justification) : Prop :=
  normalize j1 = normalize j2

instance : Setoid Justification where
  r := JustificationEquiv
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
```

### 9.2 Quotient Type

We can form the quotient type of justifications modulo equivalence:

```lean
def JustificationClass := Quotient (inferInstance : Setoid Justification)

-- Normal forms give representatives
def representative (c : JustificationClass) : Justification :=
  Quotient.lift normalize (fun _ _ h => h) c
```

### 9.3 Integration with Belief Type

```lean
structure Belief (A : Type) where
  value : A
  conf : Confidence
  justification : JustificationClass  -- equivalence class, not raw justification
```

This ensures that beliefs are identified up to justification equivalence.

---

## 10. Open Questions

### 10.1 Efficiency of Normal Form Computation

**Question**: Can we compute normal forms efficiently in practice?

Approaches:
- Lazy normalization (normalize on demand)
- Hash-consing (share common sub-justifications)
- Incremental normalization (update NF after small changes)

### 10.2 Normal Forms for Defeat Cycles

**Question**: What is the normal form of a justification involving defeat cycles?

From Thread 5.11, defeat cycles have fixed-point semantics. The "normal form" would need to represent this fixed point explicitly:
```
fixpoint(λj. undercut(j, d))
```

This requires extending the justification syntax to handle cycles.

### 10.3 Decidability of Equivalence

**Question**: Is justification equivalence decidable?

**Answer**: Yes, for CLAIR-finite-stratified:
- Normalization terminates (strong normalization)
- Normal forms are computable
- Equality of normal forms is decidable

For full CLAIR: may be undecidable if normalization doesn't terminate.

### 10.4 Gradedness and Equivalence

**Question**: How does grading interact with equivalence?

If we have Belief<A>[c₁] ≃ Belief<A>[c₂], must c₁ = c₂?

**Answer**: In our definition, yes. Confidence is preserved by normalization of cut-free terms. If two beliefs are equivalent, their confidences must match.

---

## 11. Conclusions

### 11.1 Key Findings

1. **Normal form equivalence is the right notion**: Two justifications are equivalent iff they have the same normal form (cut-free, flattened, ordered).

2. **Cut elimination provides normal forms**: Thread 2.19's cut elimination theorem gives the foundation for normal forms.

3. **Non-distributivity constrains equivalence**: Because × and ⊕ don't distribute, we cannot freely reorganize derivation and aggregation. Equivalence must respect this structure.

4. **Confidence is invariant under normalization** (for cut-free terms): The canonical confidence is well-defined.

5. **Defeat doesn't distribute over aggregation**: undercut(agg(a,b), d) ≠ agg(undercut(a,d), undercut(b,d)) in general.

6. **Equivalence is decidable** for CLAIR-finite-stratified: Normalization terminates and equality of normal forms is decidable.

### 11.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Normal form equivalence is correct | 0.85 | Matches proof-theoretic tradition |
| Cut elimination provides normal forms | 0.90 | Proven in Thread 2.19 |
| Non-distributivity constrains equiv | 0.95 | Mathematical necessity |
| Equivalence decidable for finite case | 0.85 | Follows from termination |
| Defeat doesn't distribute | 0.95 | Counterexample computed |

### 11.3 Recommendations

1. **Formalize in Lean**: Add JustificationEquiv and normalize function to formal/lean/
2. **Implement in interpreter**: Use normal forms for belief caching (Thread 7)
3. **Document non-distributivity**: Ensure users understand aggregation vs derivation semantics
4. **Consider hash-consing**: Share equivalent justification sub-DAGs

---

## 12. Impact on Other Threads

### Thread 2 (Justification Structure)
- Equivalence clarifies when justifications are "the same"
- DAG sharing via normal form representatives

### Thread 7 (Implementation)
- Use normal forms for belief caching
- Hash-consing justification DAGs

### Thread 8 (Verification)
- Add Setoid instance for Justification in Lean
- Prove normalization termination

### Thread 2.22 (Curry-Howard)
- Equivalence corresponds to definitional equality of proof terms
- Normal forms are values; reduction is computation

---

## 13. References

### Primary Sources

- **Gentzen, G.** (1935). "Investigations into Logical Deduction."

- **Howard, W.A.** (1969). "The Formulae-as-Types Notion of Construction."

- **Girard, J.-Y.** (1987). "Linear Logic."

- **Artemov, S.** (2001). "Explicit Provability and Constructive Semantics."

### CLAIR Internal

- Thread 2.16: exploration/thread-2.16-sequent-calculus.md
- Thread 2.19: exploration/thread-2.19-cut-elimination.md
- Thread 2.22: exploration/thread-2.22-curry-howard-terms.md
- Thread 2.25: exploration/thread-2.25-dual-monoid-grading.md
- Thread 5.11: exploration/thread-5.11-defeat-fixedpoints.md

---

*Thread 2.17 Status: Substantially explored. Normal form equivalence defined. Non-distributivity implications analyzed. Decidability established for finite case.*
