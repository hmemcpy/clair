# Thread 2.4: CLAIR and Artemov's Justification Logic

> **Status**: Active exploration (Session 50)
> **Task**: 2.4 Formalize justification logic - Connect to Artemov's work
> **Question**: What can CLAIR borrow from Justification Logic? What needs extending?
> **Prior Work**: Thread 2 (justification structure), notes/prior-art.md

---

## 1. The Problem

### 1.1 Background

Artemov's Justification Logic (JL) is the primary formal framework for reasoning about explicit justifications. It extends modal logic by replacing the necessity operator □ with explicit justification terms `t : P` ("t is a justification for P").

CLAIR's justification structure (Thread 2) uses labeled DAGs with edges representing support and defeat. The question is: **What is the precise relationship between CLAIR's justification DAGs and Artemov's justification terms?**

### 1.2 The Core Question

> Can CLAIR's justification structure be understood as an extension of Justification Logic, and if so, what exactly is the extension?

### 1.3 What We Need to Establish

1. **Mapping**: How do JL's term constructors map to CLAIR's DAG operations?
2. **Extensions**: What does CLAIR add that JL lacks?
3. **Limitations**: What does JL provide that CLAIR currently lacks?
4. **Formal Connection**: Can we define a homomorphism between the structures?

---

## 2. Artemov's Justification Logic: A Deep Survey

### 2.1 Historical Development

Justification Logic originated in Artemov's work on the arithmetical completeness of intuitionistic logic (1995, 2001). The key insight was that Gödel's embedding of intuitionistic propositional logic into S4 (□ as provability) could be made explicit by replacing □ with concrete proof terms.

**Key Papers**:
- Artemov, S. (1995). "Operational Modal Logic." Technical Report.
- Artemov, S. (2001). "Explicit Provability and Constructive Semantics." Bull. Symb. Logic.
- Artemov, S. & Fitting, M. (2019). *Justification Logic: Reasoning with Reasons*. Cambridge.

### 2.2 The Logic LP (Logic of Proofs)

The core system LP has the following syntax:

**Justification Terms**:
```
t ::= c           -- constant (axiom justifications)
    | x           -- variable (hypothesis)
    | t · s       -- application (modus ponens)
    | t + s       -- sum (choice of justifications)
    | !t          -- proof checker (verification)
```

**Formulas**:
```
φ ::= p           -- propositional variable
    | ⊥           -- falsity
    | φ → ψ       -- implication
    | t : φ       -- justification assertion
```

### 2.3 Key Axioms of LP

**Propositional Axioms**: Classical propositional logic axioms and modus ponens.

**Application Axiom**:
```
s : (φ → ψ) → (t : φ → (s · t) : ψ)
```
"If s justifies φ → ψ, and t justifies φ, then s · t justifies ψ."

**Sum Axiom (Monotonicity)**:
```
t : φ → (t + s) : φ
s : φ → (t + s) : φ
```
"If t justifies φ, then t + s also justifies φ (for any s)."

**Proof Checker Axiom**:
```
t : φ → !t : (t : φ)
```
"If t justifies φ, then !t justifies that t justifies φ."

**Constant Specification**: For each axiom A, there exists a constant c such that `c : A`.

### 2.4 Key Theorems

**Internalization Theorem**: For any provable φ, there exists a justification term t such that `t : φ` is provable.

**Realization Theorem**: Every theorem of S4 modal logic can be realized in LP by replacing □ with appropriate justification terms.

**Arithmetical Completeness**: LP is arithmetically complete for the standard proof interpretation of intuitionistic logic.

### 2.5 Semantics

**Kripke-Fitting Models**: A JL model is a triple (W, R, V, E) where:
- W is a set of possible worlds
- R ⊆ W × W is accessibility (often reflexive and transitive for LP)
- V is a propositional valuation
- E : Terms × Formulas → P(W) is the "evidence function"

**Key Condition**:
```
w ⊨ t : φ  iff  w ∈ E(t, φ) and ∀w'. R(w,w') → w' ⊨ φ
```
"t : φ holds at w iff w is in the evidence set for t justifying φ, AND φ holds in all accessible worlds."

---

## 3. CLAIR's Justification Structure

### 3.1 The Current Design (from Thread 2)

CLAIR justifications are **DAGs with labeled edges**:

```
Justification :=
  | Asserted { source : Source }
  | Derived {
      rule : Rule,
      premises : List BeliefId,  -- DAG edges, not tree children
      edge_type : EdgeType       -- support, undercut, rebut
    }
  | Aggregated { sources : List BeliefId }
```

### 3.2 Edge Types (from Thread 2.10)

```
EdgeType :=
  | Support      -- positive evidential support
  | Undercut     -- attacks the inference link
  | Rebut        -- attacks the conclusion directly
```

### 3.3 Confidence Propagation (from Thread 2.10, 2.11)

- **Derivation**: Confidence multiplies (c₁ × c₂)
- **Aggregation**: Confidence combines via ⊕ (1 - (1-c₁)(1-c₂))
- **Undercut**: c' = c × (1 - d)
- **Rebut**: c' = c_for / (c_for + c_against)

---

## 4. Mapping JL to CLAIR

### 4.1 Term Constructor Correspondence

| JL Term | CLAIR Operation | Correspondence Quality |
|---------|-----------------|------------------------|
| `c` (constant) | `Asserted { source }` | Direct (axiom/source) |
| `x` (variable) | `premise_id` (reference) | Direct (hypothesis) |
| `t · s` (application) | `Derived { rule: MP, premises: [s, t] }` | Structural match |
| `t + s` (sum) | No direct equivalent | **Gap** |
| `!t` (proof checker) | `introspect` (Thread 3) | Approximate (stratified) |

### 4.2 Application (·) in Detail

**JL Application**:
```
s : (φ → ψ)    t : φ
─────────────────────────
      (s · t) : ψ
```

**CLAIR Derivation** (for modus ponens):
```
b_s : Belief (φ → ψ)    b_t : Belief φ
───────────────────────────────────────────
  derive₂ mp_rule b_s b_t : Belief ψ
```

The structural correspondence is clear:
- JL's `·` composes justifications for premises into a justification for the conclusion
- CLAIR's `derive₂` composes beliefs (with justifications) for premises into a belief for the conclusion
- Both are fundamentally **modus ponens over justified statements**

**Key Difference**: CLAIR's derivation includes **confidence propagation** (c_result = c_s × c_t), which JL lacks.

### 4.3 Sum (+) in Detail

**JL Sum**: `t + s` is a justification for anything that either `t` or `s` justifies.

This is **NOT** the same as CLAIR's aggregation!

- JL `t + s`: "I can justify φ using t OR using s" (choice)
- CLAIR aggregate: "t AND s both support φ, so confidence increases" (combination)

**Analysis**:
- JL's sum is **monotonicity/weakening**: having more justification options is never worse
- CLAIR's aggregation is **evidential combination**: independent evidence increases confidence

**Neither subsumes the other**:
- JL sum doesn't increase "strength" (no confidence concept)
- CLAIR aggregate is strictly about same-conclusion evidence, not alternative justifications

**Potential Extension**: CLAIR could add a `choice` construct:
```
Choice { alternatives : List BeliefId }
-- "Any of these would suffice"
-- confidence = max(confidences)  -- pessimistic: any one suffices
```

### 4.4 Proof Checker (!) in Detail

**JL Proof Checker**: `t : φ → !t : (t : φ)`
"If t justifies φ, then !t justifies that t justifies φ."

This is **self-referential justification**—exactly what Thread 3 addresses!

**CLAIR's Treatment**:
- Thread 3 stratifies beliefs: `Belief<n, A>` can only reference `Belief<m, B>` for m < n
- `introspect : Belief<m, A> → Belief<n, Meta<A>>` requires proof that m < n
- This corresponds to iterated application of !:
  - `!t : (t : φ)` is level-1 about level-0
  - `!!t : (!t : (t : φ))` is level-2 about level-1

**Key Insight**: CLAIR's stratification is more explicit than JL's proof checker:
- JL: ! is a term constructor that can be applied freely
- CLAIR: introspection is typed and level-checked
- CLAIR prevents paradoxes that JL must address semantically

---

## 5. What CLAIR Adds to JL

### 5.1 Graded Confidence

JL justifications are **ungraded**—a term either justifies a formula or it doesn't.

CLAIR adds **epistemic commitment levels**:
```
Belief<α> = (value : α, confidence : [0,1])
```

This is a fundamental extension. Where JL has:
```
t : φ  -- binary: t does or doesn't justify φ
```

CLAIR has:
```
b : Belief φ  where b.confidence = 0.85
-- graded: b justifies φ with confidence 0.85
```

**Formal Interpretation**: CLAIR's confidence can be seen as a **fuzzy membership degree** in the evidence function:
```
E(t, φ, w) ∈ [0,1]  -- degree to which t is evidence for φ at w
```

This aligns CLAIR with fuzzy modal logic (Thread 3.13, CPL).

### 5.2 Defeat (Negative Justification)

JL has only **positive** justification—terms that support conclusions.

CLAIR adds **negative** justification via defeat edges:
```
EdgeType.Undercut  -- attacks the inference
EdgeType.Rebut     -- attacks the conclusion
```

**Significance**: This is a major extension. In JL:
- No way to express "t undermines the inference from s to φ"
- No way to express "t provides counter-evidence to φ"

CLAIR can express:
```
Derived {
  rule: MP,
  premises: [s, t],
  edge_type: Undercut,  -- t undercuts s's support for φ
  confidence: 0.7
}
```

**Connection to Defeasible Logic**: CLAIR's defeat aligns with Pollock's defeaters (1987) rather than JL.

### 5.3 DAG Structure (Shared Premises)

JL terms are **tree-like by construction**:
- Each subterm has exactly one parent
- If `t · s` appears twice, it's two separate term occurrences

CLAIR justifications are **DAGs**:
- The same premise belief can support multiple conclusions
- Premises are identified by `BeliefId`, enabling sharing

**Example**:
```
    [A] ────────┬──────> [A ∧ B]
    (conf 0.9)  │
                │
    [B] ────────┘        [A → C]
    (conf 0.8)           (conf 0.95)
        │                    │
        └────────────────────┴──────> [C]
                                      (derived from both)
```

In JL, the two uses of A would be separate term occurrences. In CLAIR, it's the same `BeliefId`, and modifications to A automatically affect all dependents.

### 5.4 Invalidation Propagation

JL doesn't address what happens when a justification is **retracted**.

CLAIR (Thread 5) has explicit **belief revision**:
- Removing an edge triggers DAG invalidation
- Confidence recomputation follows topological order
- Defeat chains have fixed-point semantics

---

## 6. What JL Provides That CLAIR Lacks

### 6.1 Formal Proof Theory

JL has a well-developed **proof theory**:
- Sequent calculus presentations
- Cut elimination
- Interpolation theorems
- Decidability results

CLAIR has operational semantics but less proof-theoretic development.

**Recommendation**: CLAIR could benefit from a sequent calculus presentation for formal meta-theory.

### 6.2 Modal Logic Connection

JL's **Realization Theorem** connects it to S4 modal logic:
- Every S4 theorem can be realized in LP
- Provides classical foundations and model theory

CLAIR's connection to modal logic (Thread 3, CPL) is still developing.

### 6.3 Proof Polynomials

Artemov's more recent work includes **proof polynomials**—algebraic structures on justification terms.

This could inform CLAIR's confidence algebra:
- JL proof polynomials: (t + s) · r = t · r + s · r (distributivity)
- CLAIR doesn't satisfy this: (c₁ ⊕ c₂) × c₃ ≠ (c₁ × c₃) ⊕ (c₂ × c₃)

**Insight**: CLAIR's algebra is fundamentally different from JL's—this is expected given fuzzy vs. classical foundations.

---

## 7. Formal Mapping

### 7.1 Translation from JL to CLAIR

Define a translation `⟦-⟧` from JL terms/formulas to CLAIR structures:

**Terms**:
```
⟦c⟧ = Asserted { source: AxiomSource(c) }
⟦x⟧ = HypothesisRef(x)
⟦t · s⟧ = Derived {
  rule: Application,
  premises: [⟦s⟧, ⟦t⟧],
  edge_type: Support,
  confidence: conf(⟦t⟧) × conf(⟦s⟧)
}
⟦t + s⟧ = Choice { alternatives: [⟦t⟧, ⟦s⟧] }  -- NEW construct
⟦!t⟧ = Introspect { source: ⟦t⟧, level: level(⟦t⟧) + 1 }
```

**Formulas**:
```
⟦p⟧ = Belief<Prop(p)>
⟦φ → ψ⟧ = Belief<⟦φ⟧ → ⟦ψ⟧>
⟦t : φ⟧ = Belief<⟦φ⟧> with justification ⟦t⟧
```

### 7.2 Translation from CLAIR to JL

More difficult—CLAIR has features JL lacks:
- Confidence doesn't translate (JL is ungraded)
- Defeat doesn't translate (JL has no negative justification)
- Aggregation ≠ sum (different semantics)

**Partial Translation** (losing information):
```
⟦Asserted{s}⟧ = c_s  -- constant for source
⟦Derived{r, [p₁,...,pₙ], Support}⟧ = r · ⟦p₁⟧ · ... · ⟦pₙ⟧
⟦Derived{r, [...], Undercut|Rebut}⟧ = ??? -- no translation
⟦Aggregated{[e₁,...,eₙ]}⟧ = ⟦e₁⟧ + ... + ⟦eₙ⟧  -- WRONG semantics
```

The translation is **lossy**—CLAIR is strictly more expressive than JL for belief structures.

### 7.3 Soundness Preservation

**Theorem (Partial Soundness)**: If a CLAIR derivation uses only Support edges and no confidence constraints, then:
- The structure of the derivation corresponds to a JL proof
- If the JL proof is valid, the CLAIR derivation is structurally well-formed

**Proof Sketch**: Both systems implement modus ponens as the core inference rule. Application (·) in JL corresponds to Support-derivation in CLAIR. The structural rules are identical when defeat is absent.

---

## 8. CLAIR as an Extension of JL

### 8.1 The Extension Taxonomy

CLAIR extends JL in several orthogonal dimensions:

| Dimension | JL | CLAIR | Extension Type |
|-----------|---|-------|----------------|
| Grading | Binary (0 or 1) | Continuous [0,1] | Generalization |
| Evidence type | Positive only | Positive + Defeat | Orthogonal extension |
| Structure | Tree (terms) | DAG | Structural extension |
| Revision | None | Full revision theory | Orthogonal extension |
| Self-reference | Free (!) | Stratified | Restriction + extension |

### 8.2 Formal Characterization

**Definition**: Let JL⁺ be the extension of JL with:
1. **Graded evidence function**: E : Terms × Formulas × Worlds → [0,1]
2. **Defeat modality**: D(t, s, φ) meaning "t defeats s as a justification for φ"
3. **DAG structure**: Terms are identified up to structural equality (sharing)

**Conjecture**: CLAIR's belief structure is a model of JL⁺.

This requires formalization of:
- How confidence propagates through · and +
- Semantics of defeat in Kripke-Fitting models
- DAG evaluation in evidence functions

### 8.3 What Would Full Formalization Require?

1. **Syntax**: Define CLAIR's justification terms as an extension of LP syntax
2. **Axioms**: State the confidence propagation rules as axioms
3. **Semantics**: Define graded Kripke-Fitting models with defeat
4. **Soundness**: Prove the axioms are sound w.r.t. the semantics
5. **Completeness**: Prove every semantically valid formula is provable (harder)

---

## 9. Open Questions

### 9.1 Identified Gaps

1. **Choice construct**: Should CLAIR add JL-style sum (choice)?
   - Different from aggregation (which increases confidence)
   - Useful for "any of these would work" scenarios
   - Confidence: max(alternatives)? Something else?

2. **Proof polynomials**: Does CLAIR's algebra have nice algebraic properties?
   - We know × and ⊕ don't distribute
   - Are there useful identities?

3. **Realization**: Can CLAIR "realize" modal logics beyond S4/GL?
   - CPL (Thread 3.13) is one direction
   - What about other modalities?

### 9.2 Theoretical Questions

1. **Decidability of justification equivalence**: In CLAIR, when are two justification DAGs "equivalent"?
2. **Normal forms**: Is there a canonical form for CLAIR justifications?
3. **Conservative extension**: Is CLAIR a conservative extension of JL?

---

## 10. Conclusions

### 10.1 Key Findings

1. **CLAIR extends JL** in multiple dimensions: confidence, defeat, DAG structure, revision
2. **Core correspondence**: JL's application (·) ↔ CLAIR's Support-derivation
3. **Not the same**: JL's sum (+) ≠ CLAIR's aggregation (different semantics)
4. **Translation is lossy**: CLAIR → JL loses defeat and confidence information
5. **CLAIR is more expressive** for representing realistic epistemic states

### 10.2 What We Established

- **Mapping**: JL term constructors map partially to CLAIR operations
- **Extensions**: CLAIR adds confidence, defeat, DAGs, revision
- **Limitations**: JL has better proof theory; CLAIR could benefit from sequent calculus
- **Formal Connection**: Partial soundness-preserving translation exists

### 10.3 Confidence Assessment

| Finding | Confidence |
|---------|------------|
| JL application ↔ CLAIR derivation | 0.95 |
| JL sum ≠ CLAIR aggregation | 0.90 |
| CLAIR is more expressive than JL | 0.90 |
| Translation from CLAIR to JL is lossy | 0.95 |
| CLAIR could be formalized as JL extension | 0.75 |

### 10.4 Recommendations

1. **Add Choice construct**: For JL-compatibility and "any suffices" scenarios
2. **Develop sequent calculus**: For better proof-theoretic foundations
3. **Formalize JL⁺**: The graded, defeat-enabled extension of JL
4. **Connect to CPL**: Relate JL⁺ semantics to CPL (Thread 3.13)

---

## 11. Impact on Other Threads

### Thread 8 (Formal Verification)

The JL connection provides:
- A reference point for CLAIR's justification semantics
- Potential sequent calculus for mechanization
- Connection to established modal logic

### Thread 3 (Self-Reference)

JL's proof checker (!) is CLAIR's introspect, but:
- CLAIR's stratification is more explicit
- CPL extends the graded self-reference beyond JL

### Thread 5 (Belief Revision)

JL doesn't address revision; CLAIR's contribution here is novel relative to JL.

---

## 12. References

### Primary Sources

- Artemov, S. (2001). "Explicit Provability and Constructive Semantics." *Bulletin of Symbolic Logic*, 7(1), 1-36.
- Artemov, S. & Fitting, M. (2019). *Justification Logic: Reasoning with Reasons*. Cambridge University Press.
- Fitting, M. (2005). "The Logic of Proofs, Semantically." *Annals of Pure and Applied Logic*, 132(1), 1-25.

### Secondary Sources

- Kuznets, R. & Studer, T. (2019). *Logics of Proofs and Justifications*. College Publications.
- Artemov, S. (2008). "The Logic of Justification." *Review of Symbolic Logic*, 1(4), 477-513.

### Related Work

- Pollock, J. (1987). "Defeasible Reasoning." *Cognitive Science*, 11(4), 481-518.
- Dung, P. M. (1995). "On the Acceptability of Arguments." *Artificial Intelligence*, 77(2), 321-357.
- Thread 2: exploration/thread-2-justification.md
- Thread 3.13: exploration/thread-3.13-graded-provability-logic.md
