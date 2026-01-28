# Thread 2.22: Curry-Howard Proof Terms for CLAIR

> **Status**: Active exploration (Session 53)
> **Task**: 2.22 What's the term assignment for CLAIR sequents?
> **Question**: Can we develop a Curry-Howard correspondence for CLAIR's sequent calculus?
> **Prior Work**: Thread 2.16 (sequent calculus), Thread 2.19 (cut elimination), formal/logical-foundations.md

---

## 1. The Problem

### 1.1 What Is a Curry-Howard Correspondence?

The Curry-Howard correspondence establishes:

| Logic | Programming |
|-------|-------------|
| Proposition | Type |
| Proof | Program (term) |
| Proof normalization | Computation |
| Cut elimination | Evaluation |

For a sequent calculus, the correspondence assigns **proof terms** to derivations:

```
Γ ⊢ A     becomes     γ : Γ ⊢ e : A

"From assumptions Γ, derive A"  ↔  "In context γ, term e has type A"
```

### 1.2 Why This Matters for CLAIR

A Curry-Howard correspondence for CLAIR would provide:

1. **Computational interpretation**: What do CLAIR derivations *compute*?
2. **Programming language foundation**: CLAIR as a typed programming language
3. **Strong normalization**: From cut elimination (Thread 2.19)
4. **Implementation guidance**: How to represent beliefs at runtime (Thread 7)
5. **Formal verification**: Type-theoretic proofs in Lean (Thread 8)

### 1.3 The CLAIR Challenge

CLAIR's sequent calculus (Thread 2.16) has features beyond standard type theory:

1. **Graded judgments**: Types carry confidence values
2. **Justification terms**: Explicit provenance tracking
3. **Defeat operations**: Non-monotonic reasoning
4. **Aggregation**: Multiple evidence combines via ⊕

The question is: **What term language corresponds to CLAIR's sequent calculus?**

---

## 2. Prior Art Survey

### 2.1 Simply-Typed Lambda Calculus ↔ Intuitionistic Logic

The original correspondence (Howard 1969):

| Sequent Rule | Term Constructor |
|--------------|------------------|
| Assumption | Variable x |
| →-Intro | λx.e (abstraction) |
| →-Elim | e₁ e₂ (application) |
| ∧-Intro | (e₁, e₂) (pair) |
| ∧-Elim | fst e, snd e (projection) |
| Cut | let x = e₁ in e₂ (substitution) |

**Key insight**: Cut elimination corresponds to β-reduction (computation).

### 2.2 Justification Logic Proof Terms (Artemov)

Artemov's Justification Logic has explicit proof terms:

```
t : A     "t is a justification for A"

t · s : B     (application: if s:A and t:A→B, then t·s:B)
t + s : A     (sum: if t:A or s:A, then t+s:A)
!t : t:A      (proof checker: if t:A provable, then !t proves that t:A)
```

**Key finding (Thread 2.4)**: CLAIR extends JL with:
- Grading (confidence)
- Defeat (undercut, rebut)
- DAG structure (not just trees)

### 2.3 Graded Type Systems

**Graded Modal Types** (Orchard et al. 2019):

```
Γ ⊢ e : □ᵣ A     "e has type A with grade r"
```

Where r comes from a semiring (R, +, ·, 0, 1). Operations track resource usage:
- Addition (+) for branching
- Multiplication (·) for composition

**Coeffect calculus** (Petricek, Orchard, Mycroft 2014):
- Types indexed by "context requirements"
- Tracks what resources a computation needs

**Relevance to CLAIR**: Confidence values [0,1] form a partial semiring (×, ⊕, 0, 1)—though note ⊕ and × don't distribute (Thread 8).

### 2.4 Linear Logic Proof Terms

Girard's linear logic has a term assignment:

| Rule | Term |
|------|------|
| ⊗-Intro | (e₁ ⊗ e₂) |
| ⊗-Elim | let x ⊗ y = e₁ in e₂ |
| ⊸-Intro | λx.e |
| ⊸-Elim | e₁ e₂ |
| !-Intro | !e |
| !-Elim | let !x = e₁ in e₂ |

**Relevance to CLAIR**: CLAIR's confidence propagation is linear-like—confidence "flows" through computation.

### 2.5 Effect Systems and Indexed Types

**Effect systems** (Gifford & Lucassen 1986):
```
e : A ! E     "e has type A with effect E"
```

Effects track computational side-effects (IO, exceptions, state).

**Indexed types** (Xi & Pfenning 1998):
```
e : A[i]     "e has type A indexed by i"
```

**Relevance to CLAIR**: Confidence could be an index or effect:
- `e : Belief<A>[c]` — belief indexed by confidence
- `e : A ! Conf(c)` — type with confidence effect

---

## 3. CLAIR Term Language Design

### 3.1 Design Principles

1. **Explicit justification**: Terms carry provenance information
2. **Graded types**: Confidence is part of the type
3. **Defeat as operation**: Undercut and rebut are term formers
4. **Aggregation as combination**: Multiple evidence combines in terms

### 3.2 Basic Term Grammar

```
Terms e ::= x                      -- variable (from context)
         | belief(v, c, j)         -- belief constructor
         | val(e)                  -- extract value from belief
         | conf(e)                 -- extract confidence from belief
         | just(e)                 -- extract justification from belief
         | λx:A.e                  -- function abstraction
         | e₁ e₂                   -- function application
         | (e₁, e₂)                -- pair
         | fst(e) | snd(e)         -- projections
         | derive(e₁,...,eₙ; r)    -- derivation rule application
         | aggregate(e₁, e₂)       -- evidence aggregation
         | undercut(e, d)          -- defeat by undermining justification
         | rebut(e₁, e₂)           -- defeat by counter-evidence
         | introspect(e)           -- belief about belief (stratified)
         | let x = e₁ in e₂        -- local binding (corresponds to cut)

Justifications j ::= j_var         -- justification variable
                  | axiom(name)    -- axiomatic justification
                  | rule(r, [j₁,...,jₙ])  -- rule application
                  | agg([j₁,...,jₙ])      -- aggregated justification
                  | undercut(j, j_d)      -- undercut justification
                  | rebut(j_for, j_against)  -- rebut justification

Confidence c ::= c ∈ [0,1]         -- confidence literal
              | c₁ × c₂            -- multiplicative composition
              | c₁ ⊕ c₂            -- additive composition
              | c × (1 - d)        -- undercut formula
              | c / (c + d)        -- rebut formula
```

### 3.3 Type Grammar

```
Types A ::= B                      -- base types (Bool, Nat, etc.)
         | A₁ → A₂                 -- function type
         | A₁ × A₂                 -- product type
         | A₁ + A₂                 -- sum type
         | Belief<A>[c]            -- graded belief type with confidence bound
         | Meta<A>[n]              -- stratified meta-belief at level n
```

The key innovation: `Belief<A>[c]` is a **graded type** where c is a confidence bound.

### 3.4 Contexts

```
Contexts Γ ::= ·                   -- empty context
            | Γ, x : Belief<A>[c]  -- belief assumption
```

Context entries are belief assumptions with confidence bounds.

---

## 4. Term Assignment to Sequent Rules

### 4.1 Structural Rules

**Identity (Axiom)**:
```
─────────────────────────────────
x : Belief<A>[c] ⊢ x : Belief<A>[c]   [Id]
```

The term is simply the variable from context.

**Cut (Let-binding)**:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ, x : Belief<A>[c₁] ⊢ e₂ : Belief<B>[c₂]
───────────────────────────────────────────────────────────────────── [Cut]
              Γ, Δ ⊢ let x = e₁ in e₂ : Belief<B>[c₁ × c₂]
```

Cut corresponds to let-binding. Confidence multiplies because the result depends on both derivations.

**Weakening**:
```
        Γ ⊢ e : Belief<A>[c]
─────────────────────────────────────── [Weak]
Γ, y : Belief<B>[c'] ⊢ e : Belief<A>[c]
```

The term doesn't change—y is simply unused.

**Contraction (Aggregation)**:
```
Γ, x₁ : Belief<A>[c₁], x₂ : Belief<A>[c₂] ⊢ e : Belief<B>[c]
────────────────────────────────────────────────────────────── [Contr]
    Γ, x : Belief<A>[c₁ ⊕ c₂] ⊢ e[aggregate(x,x)/x₁,x₂] : Belief<B>[c]
```

Contraction aggregates the two beliefs into one with combined confidence.

### 4.2 Conjunction Rules

**∧-Right Introduction**:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Γ ⊢ e₂ : Belief<B>[c₂]
─────────────────────────────────────────────────── [∧R]
Γ ⊢ derive((e₁, e₂); ∧I) : Belief<A × B>[c₁ × c₂]
```

**Term**: `derive((e₁, e₂); ∧I)` pairs the beliefs and records the derivation rule.

**∧-Left Introduction**:
```
Γ, x : Belief<A>[c_A], y : Belief<B>[c_B] ⊢ e : Belief<C>[c]
──────────────────────────────────────────────────────────── [∧L]
    Γ, z : Belief<A × B>[c'] ⊢ e[fst(z)/x, snd(z)/y] : Belief<C>[c]
```

**Term**: Replace x,y with projections from z.

### 4.3 Implication Rules

**→-Right Introduction**:
```
Γ, x : Belief<A>[c_A] ⊢ e : Belief<B>[c_B]
───────────────────────────────────────────────────────────── [→R]
Γ ⊢ belief(λx.e, c_B, rule(→I, [just(e)])) : Belief<A → B>[c_B]
```

**Term**: Abstract over x, forming a function. The belief wraps the function with the derivation's confidence.

**→-Left Introduction (Modus Ponens)**:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ, y : Belief<B>[c_B] ⊢ e₂ : Belief<C>[c_C]
────────────────────────────────────────────────────────────────────── [→L]
Γ, Δ, f : Belief<A → B>[c₂] ⊢ let y = derive(f e₁; →E) in e₂ : Belief<C>[c']
```

where c' = (c₁ × c₂) × c_C.

**Term**: Apply f to e₁, bind the result to y, then continue with e₂.

### 4.4 Defeat Rules

**Undercut**:
```
Γ ⊢ e : Belief<A>[c]    Δ ⊢ d : Belief<Defeat(just(e))>[d_c]
─────────────────────────────────────────────────────────────── [Undercut]
    Γ, Δ ⊢ undercut(e, d) : Belief<A>[c × (1 - d_c)]
```

**Term**: `undercut(e, d)` applies the defeat to e's justification.

**Semantic interpretation**: The undercut term constructs a new belief with:
- Same value as e
- Reduced confidence: c × (1 - d_c)
- Modified justification: undercut(just(e), just(d))

**Rebut**:
```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ ⊢ e₂ : Belief<¬A>[c₂]
──────────────────────────────────────────────────── [Rebut]
   Γ, Δ ⊢ rebut(e₁, e₂) : Belief<A>[c₁ / (c₁ + c₂)]
```

**Term**: `rebut(e₁, e₂)` combines evidence for and against A.

### 4.5 Aggregation Rule

```
Γ ⊢ e₁ : Belief<A>[c₁]    Δ ⊢ e₂ : Belief<A>[c₂]    independent(e₁, e₂)
────────────────────────────────────────────────────────────────────────── [Agg]
         Γ, Δ ⊢ aggregate(e₁, e₂) : Belief<A>[c₁ ⊕ c₂]
```

**Term**: `aggregate(e₁, e₂)` combines independent evidence.

**Semantic interpretation**: When two independent sources support the same proposition, we form a single belief with aggregated confidence.

### 4.6 Stratified Belief Rules

For self-reference (Thread 3), we add level-indexed types:

```
Γᵐ ⊢ e : Belief<A>[c]    m < n
────────────────────────────────────────────────── [Introspect]
Γⁿ ⊢ introspect(e) : Belief<Meta<A>>[c × g(c)]ⁿ
```

where g(c) = c² is the Löb discount function (Thread 3.18).

**Term**: `introspect(e)` creates a meta-belief about e with discounted confidence.

---

## 5. Operational Semantics

### 5.1 Evaluation Rules

Cut elimination (Thread 2.19) corresponds to computation. The key reduction:

**β-reduction (function application)**:
```
(λx.e₁) e₂  →  e₁[e₂/x]
```

**let-reduction (cut)**:
```
let x = v in e  →  e[v/x]     (when v is a value)
```

**projection reduction**:
```
fst(v₁, v₂)  →  v₁
snd(v₁, v₂)  →  v₂
```

**value extraction**:
```
val(belief(v, c, j))  →  v
conf(belief(v, c, j))  →  c
just(belief(v, c, j))  →  j
```

### 5.2 Defeat Reduction

**Undercut reduction**:
```
undercut(belief(v, c, j), belief(d_val, d_c, d_j))
  →  belief(v, c × (1 - d_c), undercut_j(j, d_j))
```

The confidence is reduced, the justification is modified.

**Rebut reduction**:
```
rebut(belief(v, c₁, j₁), belief(_, c₂, j₂))
  →  belief(v, c₁ / (c₁ + c₂), rebut_j(j₁, j₂))
```

The "winning" value is determined by which has higher confidence; the resulting confidence is the normalized value.

### 5.3 Aggregation Reduction

```
aggregate(belief(v, c₁, j₁), belief(v, c₂, j₂))
  →  belief(v, c₁ ⊕ c₂, agg_j([j₁, j₂]))
```

Same value, combined confidence, aggregated justification.

---

## 6. Type Safety

### 6.1 Progress and Preservation

Cut elimination (Thread 2.19) implies:

**Theorem (Progress)**: If `· ⊢ e : Belief<A>[c]` (closed, well-typed term), then either:
1. e is a value, or
2. e can take a step: e → e'

**Theorem (Preservation)**: If `Γ ⊢ e : Belief<A>[c]` and e → e', then `Γ ⊢ e' : Belief<A>[c']` where c' ≤ c.

**Note**: Confidence may decrease during evaluation (as noted in Thread 2.19 for cut elimination). This is expected: computation may reveal that the original confidence was too optimistic.

### 6.2 Strong Normalization

**Theorem**: The CLAIR term calculus is strongly normalizing.

**Proof sketch**: Cut elimination (Thread 2.19) shows all cuts can be eliminated. By the Curry-Howard correspondence, this means all terms reduce to normal form. The measure (cut rank, cut grade) from Thread 2.19 directly translates to a termination measure on term reductions.

### 6.3 Confluence

**Conjecture**: The CLAIR term calculus is confluent.

**Sketch**: Standard techniques apply. The key non-obvious cases:
- Defeat operations (undercut, rebut) don't interfere with other reductions
- Aggregation is commutative and associative (proven in Thread 8)

---

## 7. Examples

### 7.1 Simple Derivation

```
-- Two beliefs
x : Belief<Nat>[0.8] = belief(42, 0.8, axiom("input"))
y : Belief<Nat>[0.9] = belief(7, 0.9, axiom("input"))

-- Derive their sum
derive_sum : Belief<Nat>[0.72] =
  derive((x, y); add_rule)
  -- confidence: 0.8 × 0.9 = 0.72
  -- justification: rule(add, [just(x), just(y)])
```

### 7.2 Defeated Belief

```
-- Original belief
claim : Belief<String>[0.9] = belief("Earth is flat", 0.9, observation("horizon"))

-- Defeating evidence
defeat : Belief<Defeat(just(claim))>[0.95] =
  belief(defeats_horizon, 0.95, scientific_evidence)

-- After undercut
weakened : Belief<String>[0.045] = undercut(claim, defeat)
-- confidence: 0.9 × (1 - 0.95) = 0.045
```

### 7.3 Aggregated Evidence

```
-- Two independent witnesses
witness1 : Belief<Guilty>[0.7] = belief(true, 0.7, testimony("Alice"))
witness2 : Belief<Guilty>[0.6] = belief(true, 0.6, testimony("Bob"))

-- Aggregate (assuming independent)
combined : Belief<Guilty>[0.88] = aggregate(witness1, witness2)
-- confidence: 0.7 ⊕ 0.6 = 1 - (1-0.7)(1-0.6) = 1 - 0.12 = 0.88
```

### 7.4 Function with Beliefs

```
-- A function that adds confidence requirements
higher_bar : Belief<A → A>[1.0] =
  belief(
    λx. if conf(x) ≥ 0.9 then x else belief(val(x), 0.5, lowered_conf),
    1.0,
    axiom("confidence_filter")
  )
```

---

## 8. Comparison with Related Systems

### 8.1 CLAIR vs Standard Curry-Howard

| Aspect | Standard | CLAIR |
|--------|----------|-------|
| Types | A | Belief<A>[c] |
| Terms | e : A | e : Belief<A>[c] |
| Cut | let x = e₁ in e₂ | Same, with c₁ × c₂ |
| Normalization | β-reduction | β-reduction + defeat |
| Grading | None | Confidence [0,1] |

### 8.2 CLAIR vs Justification Logic

| Aspect | JL | CLAIR |
|--------|-----|-------|
| Justification terms | t : A | e : Belief<A>[c] |
| Application (·) | t · s : B | derive(f e; →E) |
| Sum (+) | t + s : A | aggregate(e₁, e₂) (different!) |
| Proof checker (!) | !t : t:A | introspect(e) (stratified) |
| Defeat | None | undercut, rebut |

**Key difference**: JL's sum (+) represents *choice* of justification (either works). CLAIR's aggregation represents *combination* of evidence (both contribute).

### 8.3 CLAIR vs Graded Type Systems

| Aspect | Graded Types | CLAIR |
|--------|--------------|-------|
| Grade structure | Semiring (R, +, ·) | Partial: ([0,1], ⊕, ×) |
| Grade semantics | Resource usage | Epistemic confidence |
| Substructural | Often linear | Aggregative contraction |
| Effects | Tracked | Justifications tracked |

**Key finding**: CLAIR's confidence algebra doesn't form a semiring (⊕ and × don't distribute). This means standard graded type theory doesn't directly apply; CLAIR needs a **dual-monoid** grading structure.

---

## 9. Open Questions

### 9.1 Theoretical Questions

1. **Decidability of type checking**: Is CLAIR type checking decidable?
   - If confidence restricted to rationals: likely yes
   - If confidence is real-valued: potentially undecidable

2. **Principal types**: Does every well-typed term have a principal (most general) type?
   - Confidence bounds complicate this

3. **Subtyping**: Should `Belief<A>[c]` be a subtype of `Belief<A>[c']` when c ≥ c'?
   - More confident beliefs can be used where less confident ones are expected

4. **Polymorphism**: How does parametric polymorphism interact with confidence?

### 9.2 Practical Questions

1. **Type inference**: Can confidence bounds be inferred?
2. **Runtime representation**: How do terms map to memory layouts? (Thread 7.2)
3. **Optimization**: Can we eliminate confidence tracking when not needed?
4. **Interoperability**: How do CLAIR programs interact with ungraded code?

### 9.3 The Non-Distributivity Problem

CLAIR's confidence operations form two separate monoids:
- (×, 1) for derivation
- (⊕, 0) for aggregation

But they don't form a semiring because distributivity fails:
```
a × (b ⊕ c) ≠ (a × b) ⊕ (a × c)
```

**Implication**: Standard graded type theory (which assumes a semiring) doesn't directly apply. We need:
- A **two-sorted** grading structure
- Clear typing rules for when × vs ⊕ applies
- No mixing of the two operations in type bounds

---

## 10. Conclusions

### 10.1 Key Findings

1. **CLAIR has a Curry-Howard correspondence**: Sequent rules correspond to term constructors, and cut elimination corresponds to computation.

2. **The type system is graded**: Types carry confidence bounds that propagate through derivations.

3. **Defeat operations are novel term formers**: `undercut` and `rebut` are computational operations that modify confidence.

4. **Aggregation differs from logical disjunction**: CLAIR's `aggregate` combines evidence (confidence increases), unlike JL's sum (choice between justifications).

5. **Strong normalization holds**: From cut elimination (Thread 2.19).

6. **Non-distributivity is fundamental**: CLAIR requires a dual-monoid grading, not a semiring.

### 10.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Term assignment exists | 0.90 | Direct construction from sequent rules |
| Cut ↔ let-binding | 0.95 | Standard correspondence |
| Strong normalization | 0.85 | From cut elimination |
| Type safety (progress/preservation) | 0.80 | Requires formal proof |
| Confluence | 0.70 | Needs verification |
| Decidable type checking | 0.65 | Depends on confidence representation |

### 10.3 Recommendations

1. **Formalize in Lean**: Add term language to formal/lean/ as next step
2. **Design syntax**: Concrete syntax for CLAIR programs (builds on formal/syntax.md)
3. **Implement type checker**: Reference implementation in Haskell (Thread 7)
4. **Explore subtyping**: Confidence-based subtyping may be useful
5. **Handle non-distributivity**: Design clear rules for when × vs ⊕ applies

---

## 11. Impact on Other Threads

### Thread 7 (Implementation)
- Term language informs runtime representation (Task 7.2)
- Reduction rules define evaluation strategy
- Type checking guides implementation

### Thread 8 (Formal Verification)
- Term assignment enables type safety proofs (Task 8.2)
- Lean formalization can use this structure
- Strong normalization connects to cut elimination

### Thread 2.17 (Justification Equivalence)
- Normal forms of terms define justification equivalence
- Two terms with same normal form have equivalent justifications

### Thread 2.21 (Decidable Fragments)
- Term language helps identify decidable fragments
- Restricted confidence values → decidable type checking

---

## 12. References

### Primary Sources

- **Howard, W.A.** (1969/1980). "The Formulae-as-Types Notion of Construction." In *To H.B. Curry: Essays on Combinatory Logic*.

- **Artemov, S.** (2001). "Explicit Provability and Constructive Semantics." *Bull. Symb. Logic*, 7(1), 1-36.

- **Girard, J.-Y.** (1987). "Linear Logic." *Theoretical Computer Science*, 50, 1-102.

### Graded Types

- **Orchard, D., Liepelt, V., & Eades, H.** (2019). "Quantitative Program Reasoning with Graded Modal Types." *ICFP 2019*.

- **Petricek, T., Orchard, D., & Mycroft, A.** (2014). "Coeffects: A Calculus of Context-Dependent Computation." *ICFP 2014*.

### CLAIR Internal

- Thread 2.16: exploration/thread-2.16-sequent-calculus.md
- Thread 2.19: exploration/thread-2.19-cut-elimination.md
- Thread 8: exploration/thread-8-verification.md
- formal/logical-foundations.md
- formal/syntax.md

---

*Thread 2.22 Status: Substantially explored. Term assignment designed. Ready for formalization.*
