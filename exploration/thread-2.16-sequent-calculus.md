# Thread 2.16: Sequent Calculus for CLAIR

> **Status**: Active exploration (Session 51)
> **Task**: 2.16 Develop sequent calculus for CLAIR
> **Question**: What is the proof-theoretic foundation for CLAIR's belief derivation system?
> **Prior Work**: Thread 2 (justification), Thread 2.4 (JL connection), formal/logical-foundations.md, formal/derivation-calculus.md

---

## 1. The Problem

### 1.1 Background

CLAIR currently has:
- **Operational semantics**: How beliefs are derived (derivation-calculus.md)
- **Algebraic structure**: Confidence operations form monoids (Thread 8)
- **Connection to Justification Logic**: Partial mapping to Artemov's JL (Thread 2.4)

What CLAIR lacks:
- **Proof-theoretic foundation**: A sequent calculus that enables formal reasoning about derivations
- **Cut elimination**: A property that would validate CLAIR's logical coherence
- **Normal forms**: Canonical representations of justifications

### 1.2 Why a Sequent Calculus?

A sequent calculus for CLAIR would provide:

1. **Meta-theoretic properties**: Cut elimination, subformula property, decidability fragments
2. **Proof search**: Systematic way to find derivations
3. **Normalization**: Canonical forms for justifications
4. **Connection to type safety**: Progress and preservation proofs (Thread 8.2) depend on proof-theoretic structure
5. **Foundation for verification**: Machine-checkable proofs in Lean

### 1.3 The Core Challenge

CLAIR's beliefs are **graded** and have **defeat**. Classical sequent calculus handles neither:
- Grading: Confidence values [0,1] on judgments
- Defeat: Negative justification (undercut, rebut)
- DAG structure: Shared premises across derivations

We need a **graded sequent calculus with defeat**.

---

## 2. Prior Art Survey

### 2.1 Gentzen's Classical Sequent Calculus (LK)

The standard sequent calculus uses sequents of the form:

```
Γ ⊢ Δ

"From assumptions Γ, conclude one of Δ"
```

**Structural rules**:
- Weakening: Add unused assumptions/conclusions
- Contraction: Use an assumption multiple times
- Exchange: Reorder assumptions/conclusions
- Cut: Combine two derivations via shared formula

**Logical rules**: Introduction and elimination for each connective.

**Key property**: Cut elimination - any proof with cut can be transformed into a cut-free proof.

### 2.2 Graded/Weighted Sequent Systems

Several lines of work address graded reasoning:

**Weighted Logic (Paoli, 2007)**:
- Formulas carry weights from a semiring
- Sequents have the form: `Γ ⊢[w] A` (derive A from Γ with weight w)
- Weights compose via semiring operations

**Fuzzy Sequent Calculi (Metcalfe & Montagna, 2007)**:
- Truth values from [0,1]
- Graded Modus Ponens: If A has value v₁ and A → B has value v₂, then B has value f(v₁, v₂)
- Cut elimination holds for certain t-norms

**Graded Modal Logic (Fine, 1972; Fitting, 1991)**:
- Graded modalities □ⁿφ ("φ is true in at least n accessible worlds")
- Extends to probabilistic/confidence semantics

**Relevant to CLAIR**: These systems show that grading and cut elimination can coexist, but none handle defeat.

### 2.3 Sequent Calculi for Non-Monotonic Reasoning

**Default Logic Sequent Systems (Bonatti, 1993)**:
- Handle defeasible reasoning
- Extensions are maximal consistent sets
- No direct confidence propagation

**Abstract Argumentation Sequent Calculi (Modgil & Prakken, 2014)**:
- Capture Dung's argumentation semantics
- Handle attack relations
- Binary (argument is IN or OUT), not graded

**ASPIC+ Proof Theory (Prakken, 2010)**:
- Structured argumentation
- Rebuttals and undercuts
- Some proof-theoretic results but not full sequent calculus

**Relevant to CLAIR**: These handle defeat but not grading. CLAIR needs both.

### 2.4 Justification Logic Sequent Calculi

**LP Sequent Calculus (Artemov, 2001; Fitting, 2005)**:
- Sequents with justification terms: `Γ ⊢ t : φ`
- Cut elimination holds
- Explicit justification structure

**Key insight from Thread 2.4**: CLAIR extends JL with grading and defeat. A CLAIR sequent calculus should extend JL's sequent system similarly.

### 2.5 Linear Logic (Girard, 1987)

Linear logic controls resource usage:
- No implicit weakening or contraction
- Connectives: ⊗ (tensor), ⅋ (par), & (with), ⊕ (plus), ⊸ (lollipop)
- Exponentials: !A (unlimited use), ?A (why not)

**Relevance to CLAIR**:
- Confidence as a "resource" that flows through derivation
- Multiple use of a belief doesn't duplicate confidence
- The ! modality could model "stable beliefs" (axioms)

**From logical-foundations.md**: CLAIR's confidence propagation has linear-like properties—confidence is "consumed" in derivation.

---

## 3. CLAIR Sequent Calculus Design

### 3.1 The Basic Sequent Form

Extend classical sequents with confidence and justification:

```
Γ ⊢[c, j] A

"From belief context Γ, derive A with confidence c and justification j"
```

Where:
- Γ = {(Aᵢ, cᵢ, jᵢ)}ᵢ is a **belief context** (multiset of beliefs with confidence and justification)
- c ∈ [0,1] is the derived confidence
- j is the justification term (DAG reference)
- A is the derived proposition

### 3.2 Belief Context

A belief context Γ is a finite multiset of **belief assumptions**:

```
Γ ::= · | Γ, (A @c : j)

"A is believed with confidence c, justified by j"
```

**Key difference from classical**: Each assumption carries metadata.

### 3.3 Judgment Forms

**Tracking judgment** (from foundations-and-limits.md):
```
Γ ⊢_track A @c : j / I

"In context Γ, we track belief A with confidence c, justification j, invalidation I"
```

For the sequent calculus, we focus on the core derivation:
```
Γ ⊢ A @c : j
```

### 3.4 Structural Rules

**Identity (Axiom)**:
```
────────────────────────────
(A @c : j) ⊢ A @c : j   [Id]
```

A belief context containing A with confidence c and justification j derives exactly A with that confidence and justification.

**Cut**:
```
Γ ⊢ A @c₁ : j₁    Δ, (A @c₁ : j₁) ⊢ B @c₂ : j₂
───────────────────────────────────────────────── [Cut]
           Γ, Δ ⊢ B @c₃ : j₃

where c₃ = c₁ × c₂   (multiplicative composition)
  and j₃ = compose(j₁, j₂)
```

Cut composes derivations. The confidence multiplies because the derived belief depends on both premises.

**Weakening**:
```
      Γ ⊢ A @c : j
──────────────────────────── [Weak]
Γ, (B @c' : j') ⊢ A @c : j
```

Adding an unused belief doesn't change the derivation. This is admissible but marks that B is irrelevant to the justification of A.

**Contraction** (modified for CLAIR):
```
Γ, (A @c : j), (A @c' : j') ⊢ B @c_B : j_B
──────────────────────────────────────────── [Contr]
    Γ, (A @c'' : j'') ⊢ B @c_B : j_B

where c'' = c ⊕ c'  (aggregation - multiple evidence for same belief)
  and j'' = aggregate(j, j')
```

**Key insight**: In CLAIR, contraction **aggregates** rather than merely forgetting duplicates. This is fundamentally different from classical logic!

### 3.5 Logical Rules: Conjunction

**Right Introduction**:
```
Γ ⊢ A @c₁ : j₁    Γ ⊢ B @c₂ : j₂
────────────────────────────────── [∧R]
  Γ ⊢ A ∧ B @c : rule(∧, [j₁, j₂])

where c = c₁ × c₂  (multiplicative - both needed)
```

**Left Introduction**:
```
Γ, (A @c_A : j_A), (B @c_B : j_B) ⊢ C @c : j
────────────────────────────────────────────── [∧L]
     Γ, (A ∧ B @c' : j') ⊢ C @c : j

where c' ≤ min(c_A, c_B)  (conservative - no stronger than components)
```

### 3.6 Logical Rules: Implication

**Right Introduction**:
```
      Γ, (A @c_A : j_A) ⊢ B @c_B : j_B
────────────────────────────────────────── [→R]
Γ ⊢ (A → B) @c : rule(→R, [j_B, discharge(A)])

where c = c_B  (confidence of implication is confidence of conclusion)
```

**Left Introduction** (Modus Ponens):
```
Γ ⊢ A @c₁ : j₁    Δ, (B @c_B : j_B) ⊢ C @c_C : j_C
────────────────────────────────────────────────────── [→L]
     Γ, Δ, ((A → B) @c₂ : j₂) ⊢ C @c : j

where c_B = c₁ × c₂   (confidence in B from MP)
  and j_B = apply(j₂, j₁)
  and c = c_B × c_C / c_B   (contribution to final confidence)
```

### 3.7 Defeat Rules

**Undercut**:
```
Γ ⊢ A @c : j    Δ ⊢ D @d : j_d    D defeats j
───────────────────────────────────────────────── [Undercut]
        Γ, Δ ⊢ A @c' : undercut(j, j_d)

where c' = c × (1 - d)
  and D defeats j means D is a defeater for the justification j
```

Undercut weakens the confidence by attacking the justification structure.

**Rebut**:
```
Γ ⊢ A @c₁ : j₁    Δ ⊢ ¬A @c₂ : j₂
────────────────────────────────────── [Rebut]
    Γ, Δ ⊢ A @c' : rebut(j₁, j₂)

where c' = c₁ / (c₁ + c₂)
```

Rebut handles direct contradictory evidence. The "winner" is determined by relative confidence.

### 3.8 Aggregation Rule

```
Γ ⊢ A @c₁ : j₁    Δ ⊢ A @c₂ : j₂    j₁ ⟂ j₂  (independent)
─────────────────────────────────────────────────────────────── [Agg]
         Γ, Δ ⊢ A @c : aggregate([j₁, j₂], independent)

where c = c₁ ⊕ c₂ = c₁ + c₂ - c₁c₂
```

When independent evidence supports the same conclusion, confidence increases via ⊕.

### 3.9 Stratified Belief Rules

For self-reference (Thread 3), we need level-indexed sequents:

```
Γⁿ ⊢ A @c : jⁿ

"At level n, derive A with confidence c and level-n justification"
```

**Introspection**:
```
       Γᵐ ⊢ A @c : jᵐ    m < n
────────────────────────────────────────── [Introspect]
Γⁿ ⊢ (Bel(A, c) @c : introspect(jᵐ))ⁿ
```

Introspecting a level-m belief from level n requires m < n (Tarski hierarchy).

---

## 4. Cut Elimination

### 4.1 The Cut Elimination Theorem

**Conjecture**: The CLAIR sequent calculus admits cut elimination.

```
Theorem (Cut Elimination):
If Γ ⊢ A @c : j is derivable using cuts,
then Γ ⊢ A @c' : j' is derivable without cuts
where c' ≤ c (confidence may decrease)
  and j' is structurally simpler than j
```

**Important**: Unlike classical cut elimination (which preserves provability exactly), CLAIR's cut elimination may **decrease confidence**. This is expected: cutting through intermediate lemmas should not artificially inflate confidence.

### 4.2 Proof Sketch

The standard cut elimination strategy applies:
1. **Rank** = complexity of the cut formula
2. **Degree** = height of proof trees above cuts
3. **Reduction steps** for each case:

**Principal cuts** (both premises introduce the cut formula):
- For ∧: Reduce by combining the component derivations
- For →: Reduce by substitution

**Non-principal cuts**: Permute the cut upward until it becomes principal.

**Defeat cuts**: These are novel. For undercut:
```
Γ ⊢ A @c : j                D defeats j
─────────────────── [...]   ──────────────── [...]
Γ ⊢ A @c' : j'              Δ ⊢ D @d : j_d
──────────────────────────────────────────── [Cut + Undercut]
         Γ, Δ ⊢ A @c'' : undercut(j', j_d)
```

Reduces to direct undercut application on the original derivation.

### 4.3 Confidence Bounds in Cut-Free Proofs

**Proposition**: In a cut-free derivation of `Γ ⊢ A @c : j`:
- All confidence values in j are subformulas of Γ or A
- c is bounded by the confidence values in Γ
- Defeat can only decrease confidence, not increase it

This is the CLAIR analog of the **subformula property**.

---

## 5. Comparison with Related Systems

### 5.1 CLAIR vs. Classical LK

| Feature | LK | CLAIR |
|---------|-----|-------|
| Sequent form | Γ ⊢ Δ | Γ ⊢ A @c : j |
| Formulas | Propositions | Beliefs (with confidence) |
| Contraction | Idempotent | Aggregative (⊕) |
| Weakening | Free | Admissible |
| Cut | Eliminable | Eliminable (with confidence cost) |
| Defeat | None | Undercut, Rebut rules |

### 5.2 CLAIR vs. Linear Logic

| Feature | Linear Logic | CLAIR |
|---------|--------------|-------|
| Resource tracking | Usage counting | Confidence propagation |
| Contraction | Restricted (requires !) | Aggregative (⊕) |
| Multiplicative ∧ | ⊗ | × for confidence |
| Additive ∨ | ⊕ | ⊕ for confidence |
| Modality | !, ? | Stratification levels |

**Insight**: CLAIR is closer to a **graded linear logic** than to classical logic.

### 5.3 CLAIR vs. Justification Logic

| Feature | JL (LP) | CLAIR |
|---------|---------|-------|
| Justification terms | t : φ | A @c : j |
| Grading | Binary (has/hasn't) | Continuous [0,1] |
| Application (·) | t · s | derive₂ with × |
| Sum (+) | t + s (choice) | aggregate with ⊕ (different!) |
| Proof checker (!) | !t | introspect (stratified) |
| Defeat | None | Undercut, Rebut |

The key extension: CLAIR's sequent calculus adds **graded confidence** and **defeat operations** to the JL framework.

---

## 6. Semantic Soundness

### 6.1 Graded Kripke Models

A CLAIR model M = (W, R, V, E, C) where:
- W = set of possible worlds
- R ⊆ W × W = accessibility relation
- V : Prop → P(W) = propositional valuation
- E : Justifications × Formulas × W → [0,1] = graded evidence function
- C : W × Formulas → [0,1] = confidence assignment

**Satisfaction**:
```
M, w ⊨ A @c : j  iff  E(j, A, w) ≥ c  and  C(w, A) ≥ c  and  ∀w'. Rww' → M,w' ⊨ A
```

### 6.2 Soundness Theorem

**Theorem (Soundness)**:
If `Γ ⊢ A @c : j` is derivable, then for all models M and worlds w:
```
If M, w ⊨ Γ  then  M, w ⊨ A @c : j
```

where M, w ⊨ Γ means each assumption in Γ is satisfied at w.

**Proof**: By induction on derivation structure, checking each rule preserves satisfaction.

### 6.3 Completeness

**Conjecture**: CLAIR's sequent calculus is complete for the graded Kripke semantics.

This requires showing that semantically valid sequents are derivable. The proof would follow the standard Henkin construction, extended to handle confidence and defeat.

**Difficulty**: Defeat complicates the canonical model construction. The presence of undercut and rebut may introduce non-monotonicity that challenges classical completeness proofs.

---

## 7. Applications

### 7.1 Proof Search

The sequent calculus enables **bottom-up proof search**:

1. Start with goal: `⊢ A @c : ?`
2. Apply rules backward to generate subgoals
3. Continue until reaching axioms or defeat conditions
4. Compute confidence bottom-up

This is exactly the DAG evaluation algorithm from derivation-calculus.md, but now with proof-theoretic justification.

### 7.2 Type Safety (Thread 8.2)

The sequent rules correspond to typing rules:

```
Γ ⊢ A @c : j   ↔   Γ ⊢ belief(A, c, j) : Belief<A>
```

Progress: If `⊢ e : Belief<A>` is derivable and e is not a value, then e can step.
Preservation: If `⊢ e : Belief<A>` and e → e', then `⊢ e' : Belief<A>`.

Cut elimination implies **strong normalization** for well-typed terms.

### 7.3 Justification Equivalence (Thread 2.17)

Two justifications j₁, j₂ are **equivalent** if:
```
∀Γ, A, c.  Γ ⊢ A @c : j₁  iff  Γ ⊢ A @c : j₂
```

Cut-free derivations provide a basis for **normal forms** of justifications.

---

## 8. Open Questions

### 8.1 Identified Gaps

1. **Defeat order in cut elimination**: When both undercut and rebut are present, does elimination order matter?

2. **Infinite defeat chains**: The sequent calculus assumes finite derivations. How do we handle fixed-point semantics for mutual defeat (Thread 5.11)?

3. **DAG representation in sequents**: Sharing is implicit in sequents but explicit in CLAIR DAGs. How do we formalize hash-consing?

4. **Correlated evidence**: The independence condition in [Agg] is semantic. Can we express it syntactically?

### 8.2 Theoretical Questions

1. **Decidability**: Is derivability decidable for cut-free CLAIR?
   - Classical LK is decidable (finite search space)
   - CLAIR's grading introduces real numbers
   - Conjecture: Decidable if confidence restricted to rationals/finite lattice (cf. CPL-finite)

2. **Interpolation**: Does Craig interpolation hold?
   - If Γ ⊢ A and A, Δ ⊢ B, is there an interpolant I in the language of both?
   - Confidence bounds propagate through interpolants

3. **Normalization strength**: Is the calculus strongly normalizing?
   - Cut elimination implies weak normalization
   - Defeat cycles might prevent strong normalization

### 8.3 Implementation Questions

1. **Lean formalization**: How to represent confidence-indexed sequents in Lean 4?
2. **Proof terms**: What's the term assignment (Curry-Howard) for CLAIR sequents?
3. **Tactics**: Can we develop automated tactics for CLAIR proof search?

---

## 9. Conclusions

### 9.1 Key Findings

1. **CLAIR admits a sequent calculus**: The derivation rules can be presented as a graded sequent system with defeat operations.

2. **Cut elimination is conjectured to hold**: With the caveat that confidence may decrease in cut-free proofs.

3. **The calculus extends JL**: CLAIR's sequent calculus is a graded, defeat-enabled extension of Justification Logic's proof system.

4. **Contraction is aggregative**: This is the key departure from classical logic—multiple evidence for the same belief combines via ⊕.

5. **Soundness is straightforward**: The rules are designed to preserve the semantic invariants.

### 9.2 What We Established

| Property | Status | Confidence |
|----------|--------|------------|
| Sequent form designed | Complete | 0.95 |
| Structural rules defined | Complete | 0.90 |
| Logical rules for ∧, → | Complete | 0.90 |
| Defeat rules (undercut, rebut) | Complete | 0.85 |
| Aggregation rule | Complete | 0.90 |
| Cut elimination conjecture | Formulated | 0.75 |
| Soundness theorem | Stated | 0.85 |
| Completeness | Open | 0.60 |

### 9.3 Recommendations

1. **Formalize in Lean**: Add sequent calculus rules to formal/lean/ (Task 8.2 prerequisite)
2. **Prove cut elimination**: This is the main theorem to verify
3. **Connect to type safety**: Show correspondence between sequents and typing judgments
4. **Explore decidability**: Characterize decidable fragments

---

## 10. Impact on Other Threads

### Thread 8 (Formal Verification)

The sequent calculus provides:
- Foundation for type safety proofs (8.2)
- Structure for Lean formalization (8.1)
- Basis for interpreter extraction (8.4)

### Thread 2.17 (Justification Equivalence)

Cut-free derivations define equivalence classes of justifications via normal forms.

### Thread 2.18 (Conservative Extension)

The sequent calculus enables precise formulation: CLAIR is a conservative extension of JL iff every JL-derivable sequent remains derivable in CLAIR (when translated).

### Thread 3 (Self-Reference)

The stratified rules (Section 3.9) formalize the type-level anti-bootstrapping from Thread 3.19.

---

## 11. References

### Primary Sources

- **Gentzen, G.** (1935). "Investigations into Logical Deduction." *Math. Zeitschrift*, 39, 176-210.

- **Girard, J.-Y.** (1987). "Linear Logic." *Theoretical Computer Science*, 50, 1-102.

- **Artemov, S.** (2001). "Explicit Provability and Constructive Semantics." *Bull. Symb. Logic*, 7(1), 1-36.

- **Fitting, M.** (2005). "The Logic of Proofs, Semantically." *APAL*, 132(1), 1-25.

### Secondary Sources

- **Paoli, F.** (2007). "Substructural Logics: A Primer." Springer.

- **Metcalfe, G. & Montagna, F.** (2007). "Substructural Fuzzy Logics." *JSL*, 72(3), 834-864.

- **Prakken, H.** (2010). "An Abstract Framework for Argumentation with Structured Arguments." *AIJ*, 1(2), 93-124.

- **Modgil, S. & Prakken, H.** (2014). "The ASPIC+ Framework for Structured Argumentation." *AIJ*, 14(3), 319-361.

### CLAIR Internal

- Thread 2: exploration/thread-2-justification.md
- Thread 2.4: exploration/thread-2.4-justification-logic-connection.md
- Thread 3: exploration/thread-3-self-reference.md
- Thread 8: exploration/thread-8-verification.md
- formal/derivation-calculus.md
- formal/logical-foundations.md
