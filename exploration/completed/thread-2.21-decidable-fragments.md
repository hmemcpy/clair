# Thread 2.21: Decidable Fragments of CLAIR

> **Status**: Active exploration (Session 57)
> **Task**: 2.21 Characterize decidable fragments of CLAIR
> **Question**: Which subsets of the full CLAIR language are decidable (admit decision procedures for validity/satisfiability)?
> **Prior Work**: Thread 2.19 (cut elimination), Thread 2.20 (completeness), Thread 3.16 (CPL decidability)

---

## 1. The Problem

### 1.1 What Does Decidability Mean for CLAIR?

A logic is **decidable** if there exists an algorithm that, given any formula φ, terminates and correctly answers whether φ is valid (provable in all models) or satisfiable (provable in some model).

For CLAIR, the decidability questions are:

1. **Validity**: Given a sequent Γ ⊢ A @c : j, can we algorithmically determine if it's derivable?
2. **Satisfiability**: Given a belief structure, can we determine if there exists a model?
3. **Type checking**: Can we verify that a CLAIR program is well-typed with decidable confidence bounds?

### 1.2 Why Decidability Matters

**For implementation (Thread 7)**:
- A decidable type checker can be fully automated
- Error messages can be precise ("this derivation fails because...")
- Compile-time guarantees become possible

**For anti-bootstrapping (Thread 3)**:
- If confidence bounds are decidable, we can check Löbian constraints at compile time
- Type-level anti-bootstrapping requires decidability of at least a fragment

**For verification (Thread 8)**:
- Decidable fragments can have decision procedures extracted to executable code
- Model checking becomes tractable

### 1.3 The Challenge

Full CLAIR is likely **undecidable**. Evidence:

1. **CPL undecidability (Thread 3.16)**: The self-reference fragment with transitivity and continuous values inherits undecidability from Vidal (2019).

2. **Completeness requires approximation (Thread 2.20)**: Rational completeness holds, but real-valued completeness requires limit arguments.

3. **Turing completeness (formal/turing-completeness.md)**: CLAIR can simulate arbitrary computation, so validity is at least as hard as halting.

**Goal**: Characterize exactly which fragments ARE decidable, and understand the trade-offs.

---

## 2. Dimensions of Restriction

CLAIR can be restricted along several orthogonal dimensions:

### 2.1 Confidence Domain

| Domain | Description | Decidability Impact |
|--------|-------------|---------------------|
| **[0,1]** (full) | Real-valued confidence | Likely undecidable with transitivity |
| **ℚ ∩ [0,1]** (rational) | Rational confidence | Completeness holds; decidability unclear |
| **L_n** (finite) | Finite lattice {0, 1/n, ..., 1} | **Decidable** (Bou et al. 2011) |
| **{0,1}** (binary) | Classical logic | **Decidable** (classical logic) |

### 2.2 Self-Reference

| Level | Description | Decidability Impact |
|-------|-------------|---------------------|
| **Full CPL** | Unrestricted graded Löb | Likely undecidable (Vidal) |
| **CPL-finite** | Löb over finite lattice | **Decidable** |
| **CPL-0 (stratified)** | No same-level self-reference | **Decidable** |
| **None** | No belief introspection | **Decidable** |

### 2.3 Defeat Operations

| Level | Description | Decidability Impact |
|-------|-------------|---------------------|
| **Full defeat** | Undercut + Rebut + cycles | Adds fixed-point computation |
| **Acyclic defeat** | No defeat cycles allowed | Simpler evaluation |
| **No defeat** | Positive evidence only | Classical JL-like |

### 2.4 Modality/Quantification

| Level | Description | Decidability Impact |
|-------|-------------|---------------------|
| **Full FOL** | First-order quantifiers | Undecidable (Church-Turing) |
| **Propositional** | No quantifiers | Reduces complexity |
| **Monadic** | At most one modality nesting | Often decidable |
| **Local** | No modal operators | Trivially decidable |

---

## 3. Analysis of Decidable Fragments

### 3.1 CLAIR-Finite: Finite Confidence Lattice

**Definition**: CLAIR-finite is CLAIR restricted to a finite confidence lattice L_n = {0, 1/n, 2/n, ..., 1}.

**Theorem**: CLAIR-finite is decidable.

**Proof sketch**:
1. With finite confidence values, the canonical model construction (Thread 2.20) terminates
2. Each belief can take only |L_n| many confidence values
3. The model search space is bounded
4. Bou et al. (2011) establishes decidability for many-valued modal logics over finite residuated lattices
5. CLAIR-finite satisfies their preconditions

**Complexity conjecture**: PSPACE-complete
- Upper bound: CLAIR-finite ⊆ finite-valued modal logic ⊆ PSPACE
- Lower bound: Classical propositional logic is PSPACE-hard and embeds

**Practical lattice**: L_5 = {0, 0.25, 0.5, 0.75, 1.0}
- Captures "none/low/medium/high/certain"
- Rounding: floor for g(c)=c², ceiling for ⊕
- 5 values suffice for practical reasoning (Thread 3.20)

### 3.2 CLAIR-Stratified: No Same-Level Self-Reference

**Definition**: CLAIR-stratified enforces Tarski's hierarchy:
- Beliefs are indexed by level n
- Level-n beliefs can only reference level-m beliefs where m < n
- Self-reference within a level is syntactically forbidden

**Theorem**: CLAIR-stratified is decidable over rational confidence.

**Proof sketch**:
1. Without same-level self-reference, no fixed-point computation is needed
2. Each level can be type-checked independently (bottom-up)
3. The problematic Vidal-style encodings require self-referential loops
4. Stratification breaks these encodings

**Complexity**: PSPACE for each level, polynomial levels → PSPACE overall

**Implementation**: Thread 8.11 formalizes this in Lean as `StratifiedBelief<n, α>`.

### 3.3 CLAIR-Propositional: No Quantifiers

**Definition**: CLAIR without first-order quantifiers (∀, ∃ over domains).

**Theorem**: CLAIR-propositional with finite confidence is decidable.

**Proof**: Propositional modal logics are decidable. Adding graded confidence over a finite lattice preserves decidability (Bou et al. 2011).

**Note**: This is distinct from quantification over beliefs, which Thread 3.14 identifies as an open question.

### 3.4 CLAIR-Acyclic-Defeat: No Defeat Cycles

**Definition**: CLAIR where the defeat graph (but not support graph) is acyclic.

**Observation**: Defeat cycles (A defeats B defeats A) require fixed-point computation (Thread 5.11). Without cycles, confidence evaluation is a simple bottom-up traversal.

**Theorem**: CLAIR with acyclic defeat over finite confidence is decidable.

**Proof**: Topological sort of defeat edges, evaluate confidence bottom-up, finite domain bounds search space.

### 3.5 CLAIR-Local: No Modality

**Definition**: CLAIR without the belief operator B_c or modal □.

This reduces to a typed language with confidence annotations but no epistemic operators.

**Theorem**: CLAIR-local is decidable and type-checkable in polynomial time.

**Proof**: Without modality, CLAIR reduces to a refinement type system. Type checking for confidence bounds is linear arithmetic over [0,1], which is decidable.

---

## 4. The Main Classification Theorem

### 4.1 Summary Table

| Fragment | Confidence | Self-Ref | Defeat | Modality | Decidable? | Complexity |
|----------|------------|----------|--------|----------|------------|------------|
| Full CLAIR | [0,1] | Full | Full | Full | **Likely No** | — |
| CLAIR-finite | L_n | Full | Full | Full | **Yes** | PSPACE |
| CLAIR-rational | ℚ∩[0,1] | Full | Full | Full | **Unknown** | — |
| CLAIR-stratified | [0,1] | CPL-0 | Full | Full | **Yes** (rational) | PSPACE |
| CLAIR-finite-stratified | L_n | CPL-0 | Full | Full | **Yes** | PSPACE |
| CLAIR-propositional | [0,1] | None | None | Prop | **Yes** | NP |
| CLAIR-local | [0,1] | None | None | None | **Yes** | P |

### 4.2 The Decidability Hierarchy

```
                      CLAIR (Full)
                          |
                          | (likely undecidable)
                          |
        +--------+--------+--------+
        |        |        |        |
   rational   stratified  finite  propositional
        |        |        |        |
        ↓        ↓        ↓        ↓
     unknown    Yes       Yes      Yes
        |        |        |        |
        +--------+--------+--------+
                          |
                    CLAIR-local (decidable, easy)
```

### 4.3 Theorem Statement

**Theorem (Decidable Fragments Classification)**:

1. **CLAIR-finite** (confidence in L_n for finite n) is decidable (PSPACE).
2. **CLAIR-stratified** (no same-level self-reference) is decidable over rational confidence.
3. **CLAIR-finite-stratified** (both restrictions) is decidable (PSPACE).
4. **Full CLAIR** with continuous [0,1] confidence and unrestricted self-reference is likely undecidable.
5. The decidability of **CLAIR-rational** (rational confidence, full self-reference) is open.

**Proof**: Items 1-3 follow from prior art (Bou et al. 2011, Vidal 2019 avoidance). Item 4 follows from Thread 3.16's analysis. Item 5 remains genuinely open.

---

## 5. Analysis of Undecidability Sources

### 5.1 The Vidal Obstruction

The key undecidability result is:

**Theorem (Vidal 2019)**: Transitive modal logics over standard MV-algebras (Łukasiewicz) or Product algebras are undecidable.

CLAIR triggers this because:
- Axiom 4 (□A → □□A) requires transitivity
- Confidence operations (×, ⊕) are Product/Łukasiewicz-like
- CPL adds Löb's axiom (stronger than axiom 4)

### 5.2 Why Finite Lattices Escape

Finite lattices escape because:
1. The Vidal encoding requires continuous values to represent arbitrary computation
2. Finite lattices have bounded information content
3. The encoding cannot express unbounded counters or tapes

### 5.3 Why Stratification Escapes

Stratification escapes because:
1. The problematic encodings use self-referential loops
2. Stratification syntactically forbids same-level reference
3. Cross-level reference is bounded (level n can only see 0..n-1)

---

## 6. Implications for CLAIR Design

### 6.1 Recommendation: Decidable Core + Escape Hatches

**Design principle**: CLAIR should have a decidable core with optional escape hatches for undecidable features.

**Decidable core (CLAIR-safe)**:
- Finite confidence lattice L_5 or L_10
- Stratified self-reference by default
- Acyclic defeat for type-level checking

**Escape hatches (CLAIR-full)**:
- `@continuous` annotation for real-valued confidence
- `@self_ref` annotation for fixed-point self-reference (Thread 3)
- `@cyclic_defeat` annotation for defeat cycles with fixed-point semantics

### 6.2 Type-Level vs Runtime Decidability

| Level | Requirements | Recommendation |
|-------|--------------|----------------|
| **Type checking** | Must be decidable | Use CLAIR-finite-stratified |
| **Static analysis** | Should be decidable | Use CLAIR-stratified |
| **Runtime evaluation** | Can be undecidable | Allow full CLAIR |

### 6.3 Implementation Strategy

For the reference interpreter (Thread 7):

```haskell
-- Type-level confidence: finite
type TypeConfidence = FiniteLattice L5

-- Runtime confidence: rational (or real approximation)
type RuntimeConfidence = Rational

-- Type checking: decidable algorithm
typeCheck :: CLAIR.Program -> Either TypeError TypedProgram

-- Runtime: may not terminate for pathological cases
evaluate :: TypedProgram -> IO (Either RuntimeError Value)
```

---

## 7. Connection to Completeness

### 7.1 Completeness + FMP ⟹ Decidability

**Classical pattern**:
- Completeness: Valid ⟹ Provable
- Finite Model Property (FMP): Not valid ⟹ Finite countermodel exists
- Together: Enumerate finite models up to some size

**For CLAIR-finite**:
- Thread 2.20 proves completeness for rational confidence
- Finite lattice ensures FMP (canonical model is finite-branching)
- Therefore decidable

### 7.2 The Rational Case

For CLAIR-rational:
- Completeness holds (Thread 2.20)
- FMP is unclear (rational values are countably infinite)
- Decidability remains open

**Conjecture**: CLAIR-rational may be decidable via careful quasimodel construction (following Gödel modal logic).

---

## 8. Open Questions

### 8.1 Is CLAIR-rational Decidable?

**Status**: Open
**Approaches**:
1. Prove FMP for CLAIR over rationals
2. Develop quasimodel semantics (like Gödel modal logic)
3. Find reduction to known decidable logic

### 8.2 Optimal Finite Lattice

**Status**: Open (Thread 3.27)
**Question**: What is the best finite lattice L_n for CLAIR?

Trade-offs:
- L_3 = {0, 0.5, 1}: Minimal, fast, coarse
- L_5 = {0, 0.25, 0.5, 0.75, 1}: Recommended default
- L_10: More precision, higher complexity
- L_100: Near-continuous, high complexity

### 8.3 Complexity Bounds

**Status**: Conjectured
**Question**: What is the precise complexity of CLAIR-finite?

Conjecture: PSPACE-complete
- Upper: Follows from modal logic inclusion
- Lower: Classical GL reduction

Need formal proof.

### 8.4 Defeat + Finite Lattice Interaction

**Status**: Partially explored (Thread 5.11)
**Question**: Do defeat fixed-points behave well over finite lattices?

The fixed-point formula a* = a(1-b)/(1-ab) may not stay in L_n.
Need rounding strategy (Thread 3.20 addresses this for g(c)=c²).

---

## 9. Comparison with Related Logics

### 9.1 Comparison Table

| Logic | Confidence | Self-Ref | Decidable? | Complexity |
|-------|------------|----------|------------|------------|
| Classical GL | {0,1} | Full | Yes | PSPACE |
| Łukasiewicz K | [0,1] | None | Yes | PSPACE |
| Łukasiewicz K4 | [0,1] | Transitive | **No** | — |
| Gödel K4 | [0,1] | Transitive | Yes | PSPACE |
| **CLAIR-finite** | L_n | Full | Yes | PSPACE |
| **CLAIR-stratified** | ℚ | CPL-0 | Yes | PSPACE |
| **Full CLAIR** | [0,1] | Full | **No** | — |

### 9.2 Key Insight

The combination of:
- Continuous values (Łukasiewicz/Product)
- Transitivity (axiom 4)

is the source of undecidability.

Breaking either restores decidability:
- Finite values: CLAIR-finite
- No transitivity: Not useful for CLAIR (breaks introspection)
- Stratification: Effectively removes problematic transitivity within levels

---

## 10. Conclusions

### 10.1 Key Findings

1. **Full CLAIR is likely undecidable** due to Vidal's result on transitive many-valued modal logics.

2. **CLAIR-finite (finite confidence lattice) is decidable** (PSPACE), making it suitable for type-level checking.

3. **CLAIR-stratified (no same-level self-reference) is decidable** over rational confidence, validating the design in Thread 3.

4. **The combination CLAIR-finite-stratified is decidable** and should be the default for type-level operations.

5. **CLAIR-rational decidability is open** — this is a genuine research question.

### 10.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Full CLAIR undecidable | 0.75 | Vidal analogy |
| CLAIR-finite decidable | 0.90 | Bou et al. 2011 |
| CLAIR-stratified decidable | 0.85 | Stratification breaks encoding |
| CLAIR-rational decidability open | 0.80 | No proof either way |
| Complexity is PSPACE | 0.70 | Conjecture from GL |

### 10.3 Recommendations

1. **Type-level**: Use CLAIR-finite-stratified (decidable, practical)
2. **Static analysis**: Use CLAIR-stratified (decidable, more expressive)
3. **Runtime**: Allow full CLAIR with honest uncertainty about termination
4. **Formalization**: Prioritize CLAIR-finite-stratified in Lean (Thread 8)

---

## 11. Impact on Other Threads

### Thread 3 (Self-Reference)
- Confirms stratification is the right default safety mechanism
- CPL-finite and CPL-0 are the decidable fragments

### Thread 7 (Implementation)
- Type checker should implement CLAIR-finite-stratified
- Runtime can be more permissive

### Thread 8 (Verification)
- Focus Lean formalization on decidable fragments
- Decision procedure can potentially be extracted

### Thread 2.20 (Completeness)
- Completeness + FMP gives decidability recipe for finite case
- Rational case needs more work

---

## 12. References

### Primary Sources

- **Bou, F., Esteva, F., Godo, L., & Rodriguez, R.** (2011). "On the Minimum Many-Valued Modal Logic over a Finite Residuated Lattice." *J. Logic Computation*, 21(5), 739-790.

- **Vidal, A.** (2019). "On Transitive Modal Many-Valued Logics." *Fuzzy Sets and Systems*, 407, 97-114.

- **Caicedo, X., Metcalfe, G., Rodriguez, R., & Rogger, J.** (2013). "A Finite Model Property for Gödel Modal Logics." *WOLLIC 2013*, LNCS 8071.

- **Boolos, G.** (1993). *The Logic of Provability*. Cambridge University Press.

### CLAIR Internal References

- Thread 2.19: exploration/thread-2.19-cut-elimination.md
- Thread 2.20: exploration/thread-2.20-completeness.md
- Thread 3.16: exploration/thread-3.16-cpl-decidability.md
- Thread 3.20: exploration/thread-3.20-cpl-finite-formalization.md
- Thread 5.11: exploration/thread-5.11-defeat-fixedpoints.md

---

*Thread 2.21 Status: Substantially explored. Decidable fragments characterized. Full CLAIR likely undecidable. Recommendations established.*
