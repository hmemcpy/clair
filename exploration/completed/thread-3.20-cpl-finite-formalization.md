# Thread 3.20: CPL-finite Formalization

> **Status**: Explored (Session 29)
> **Question**: How do we formalize CPL with finite confidence values and prove decidability?
> **Priority**: HIGH — Provides the decidable fragment needed for CLAIR's type-level checks
> **Prior Threads**: Thread 3.13 (CPL design), Thread 3.16 (decidability), Thread 3.17 (soundness/completeness), Thread 3.18 (Löb discount)

---

## 1. The Problem

Thread 3.16 established that full CPL (Confidence-Bounded Provability Logic) is likely undecidable due to the combination of transitivity and continuous [0,1] values (Vidal 2019). However, CPL-finite—restricting confidence to a finite set of values—was identified as a decidable fragment.

**Core question:** What does a complete formalization of CPL-finite look like, and how do we prove decidability?

### 1.1 Prior Art Foundation

Key results from the literature:

1. **Bou, Esteva, Godo (2011)**: Many-valued modal logics over finite residuated lattices are decidable. Provides axiomatizations for finite MV-chains.

2. **Bou, Cerami, Esteva (IJCAI 2011)**: Finite-valued Łukasiewicz modal logic is PSPACE-complete.

3. **Segerberg (1971)**: Classical GL is complete for finite transitive irreflexive trees, hence decidable (PSPACE-complete).

4. **Vidal (2019)**: Transitive modal many-valued logics over continuous [0,1] are undecidable—but finite lattices escape this.

---

## 2. The Finite Lattice: Design Choices

### 2.1 Candidate Lattices

**Option A: Uniform n-valued lattice**
```
L_n = {0, 1/(n-1), 2/(n-1), ..., 1}
```
For n=5: L₅ = {0, 0.25, 0.5, 0.75, 1}

**Option B: Łukasiewicz n-chain (MV_n)**
Standard MV-algebra with:
- a ⊙ b = max(0, a + b - 1)  (Łukasiewicz t-norm)
- a → b = min(1, 1 - a + b)

**Option C: Product-like finite approximation**
Discretize CLAIR's product t-norm:
- a ⊗ b = round_L(a × b)
- a ⊕ b = round_L(a + b - a×b)

### 2.2 Recommended Choice: L₅ with Product Rounding

For CLAIR, **Option C with L₅** is most appropriate because:

1. **Alignment**: CLAIR uses product t-norm (×), not Łukasiewicz
2. **Intuitive levels**: {0, 0.25, 0.5, 0.75, 1} maps to "none", "low", "medium", "high", "certain"
3. **Computational simplicity**: 5 values is small enough for efficient enumeration
4. **Prior art**: Bou et al. (2011) covers finite product-like structures

### 2.3 The c² Closure Problem

**Critical discovery:** No non-trivial finite sublattice of [0,1] is closed under g(c) = c².

**Proof:**
- c = 0: 0² = 0 ✓
- c = 1: 1² = 1 ✓
- c ∈ (0,1): c² < c, so c² approaches 0 under iteration
- The only fixed points are 0 and 1

For intermediate values:
| c     | c²       | Not in L₅? |
|-------|----------|------------|
| 0.25  | 0.0625   | ✗ Not in L₅ |
| 0.5   | 0.25     | ✓ In L₅    |
| 0.75  | 0.5625   | ✗ Not in L₅ |

**Resolution:** Must accept rounding. The floor function preserves anti-bootstrapping:
```
g_L(c) = floor_L(c²) = max{l ∈ L : l ≤ c²}
```

This ensures g_L(c) ≤ c² ≤ c, maintaining the semantic constraint that self-soundness claims cannot increase confidence.

---

## 3. Formal Definition of CPL-finite

### 3.1 The Finite Lattice

**Definition (L₅ with Product Operations):**

The lattice L₅ = {0, 0.25, 0.5, 0.75, 1} with operations:

**Multiplication (graded conjunction):**
```
a ⊗ b = floor_L(a × b)

⊗    | 0    0.25  0.5   0.75  1
-----|-----------------------------
0    | 0    0     0     0     0
0.25 | 0    0     0     0     0.25
0.5  | 0    0     0.25  0.25  0.5
0.75 | 0    0     0.25  0.5   0.75
1    | 0    0.25  0.5   0.75  1
```

**Probabilistic OR (graded disjunction):**
```
a ⊕ b = ceiling_L(a + b - a×b)

⊕    | 0    0.25  0.5   0.75  1
-----|-----------------------------
0    | 0    0.25  0.5   0.75  1
0.25 | 0.25 0.5   0.75  0.75  1
0.5  | 0.5  0.75  0.75  1     1
0.75 | 0.75 0.75  1     1     1
1    | 1    1     1     1     1
```

Note: We use ceiling for ⊕ because aggregation should be optimistic (combining evidence increases confidence).

**Negation:**
```
¬a = 1 - a

¬0 = 1, ¬0.25 = 0.75, ¬0.5 = 0.5, ¬0.75 = 0.25, ¬1 = 0
```

**Residual (graded implication):**
```
a → b = max{c ∈ L₅ : a ⊗ c ≤ b}
```

This is computable by finite search over L₅.

### 3.2 Löb Discount Function

**Definition:**
```
g_L : L₅ → L₅
g_L(c) = floor_L(c²)

g_L(0) = 0         (0² = 0)
g_L(0.25) = 0      (0.25² = 0.0625 → floor to 0)
g_L(0.5) = 0.25    (0.5² = 0.25 ✓)
g_L(0.75) = 0.5    (0.75² = 0.5625 → floor to 0.5)
g_L(1) = 1         (1² = 1)
```

**Semantic justification:** The floor ensures g_L(c) ≤ c, preserving anti-bootstrapping.

### 3.3 CPL-finite Syntax

**Definition (CPL-finite Formulas):**
```
φ ::= p           (propositional variable, p ∈ Prop)
    | l           (constant, l ∈ L₅)
    | ¬φ          (negation)
    | φ ⊗ ψ       (graded conjunction)
    | φ ⊕ ψ       (graded disjunction)
    | φ → ψ       (graded implication)
    | □φ          (graded necessity/belief)
```

**Note:** Unlike full CPL, we don't subscript □ with confidence levels—the output of □φ is itself a value in L₅.

### 3.4 CPL-finite Semantics

**Definition (CPL-finite Frame):**
A CPL-finite frame is a triple F = (W, R, ≺) where:
- W is a finite non-empty set of worlds
- R : W × W → L₅ is a graded accessibility relation
- ≺ is a strict well-founded partial order on W (for converse well-foundedness)

**Constraint (Accessibility respects order):**
```
R(w, w') > 0  ⟹  w' ≺ w
```

This ensures no infinite ascending R-chains, capturing GL's converse well-foundedness in the graded setting.

**Definition (CPL-finite Model):**
A CPL-finite model is M = (F, V) where:
- F is a CPL-finite frame
- V : W × Prop → L₅ is a graded valuation

**Definition (Satisfaction):**

Extend V to all formulas:
```
V_w(l) = l                                      (constant)
V_w(¬φ) = 1 - V_w(φ)                            (negation)
V_w(φ ⊗ ψ) = V_w(φ) ⊗ V_w(ψ)                   (conjunction)
V_w(φ ⊕ ψ) = V_w(φ) ⊕ V_w(ψ)                   (disjunction)
V_w(φ → ψ) = V_w(φ) → V_w(ψ)                   (implication)
V_w(□φ) = min_{w' ∈ W} max{1 - R(w, w'), V_{w'}(φ)}  (necessity)
```

The box semantics says: "The confidence in □φ at w is the minimum over all accessible worlds w' of max(1 - R(w,w'), V_{w'}(φ))."

- If R(w, w') = 0 (no access), the max is 1 (contributes nothing to the min)
- If R(w, w') = 1 (full access), the max is just V_{w'}(φ)
- If R(w, w') is intermediate, there's a "discount" from imperfect access

**Definition (Validity):**
A formula φ is valid in CPL-finite (written ⊨_{CPL-finite} φ) iff V_w(φ) = 1 for all worlds w in all CPL-finite models M.

---

## 4. Axiomatization of CPL-finite

### 4.1 Axioms

**Propositional base (over L₅):**
All tautologies of 5-valued product logic, including:
- P1: φ → (ψ → φ)
- P2: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
- Lattice axioms for ⊗, ⊕, ¬
- Value axioms: ⋁_{l ∈ L₅} (φ ↔ l)

**Modal axioms:**
- **K (Distribution):** □(φ → ψ) → (□φ → □ψ)
- **4 (Positive Introspection):** □φ → □□φ
- **L (Graded Löb):** □(□φ → φ) → □φ

  In the graded setting, this becomes: if V_w(□(□φ → φ)) = c, then V_w(□φ) ≥ g_L(c).

- **No T:** □φ → φ is NOT an axiom (fallibilism preserved)

### 4.2 Rules

**Modus Ponens (Graded):**
If ⊢ φ and ⊢ φ → ψ then ⊢ ψ

More precisely: if V(φ) = 1 and V(φ → ψ) = 1 in all models, then V(ψ) = 1.

**Necessitation:**
If ⊢ φ then ⊢ □φ

---

## 5. Decidability of CPL-finite

### 5.1 Finite Model Property

**Theorem (CPL-finite Finite Model Property):**
If φ is not valid in CPL-finite, then there exists a finite countermodel M with |W| ≤ f(|φ|, |L₅|) for some computable function f.

**Proof sketch:**
1. **Base case**: Propositional 5-valued logic has the finite model property.
2. **Modal extension**: Bou et al. (2011) show that many-valued modal logics over finite residuated lattices have the FMP.
3. **Löb constraint**: The converse well-foundedness condition restricts frames further, ensuring finite depth.
4. **Bound**: The bound f comes from the maximum nesting depth of □ in φ, combined with the lattice size.

### 5.2 Decidability Theorem

**Theorem (CPL-finite Decidability):**
CPL-finite is decidable.

**Proof:**
Given the finite model property with computable bound f:
1. Enumerate all CPL-finite frames (W, R, ≺) with |W| ≤ f(|φ|, |L₅|)
2. For each frame, enumerate all valuations V : W × Prop(φ) → L₅
3. Check if V_w(φ) = 1 for all w ∈ W
4. If all models satisfy φ, return "valid"; otherwise return "not valid"

This terminates because there are finitely many frames and valuations to check.

### 5.3 Complexity

**Conjecture (CPL-finite Complexity):**
CPL-finite is PSPACE-complete.

**Upper bound argument:**
- Finite-valued Łukasiewicz modal K is PSPACE-complete (Bou, Cerami, Esteva 2011)
- Adding axiom 4 (transitivity) doesn't change PSPACE membership
- Adding Löb's axiom restricts frames, which cannot increase complexity
- Therefore, CPL-finite is in PSPACE

**Lower bound argument:**
- Classical GL is PSPACE-hard (contains classical modal K)
- CPL-finite contains classical GL as a fragment (when all values are 0 or 1)
- Therefore, CPL-finite is PSPACE-hard

**Confidence:** 0.75 that CPL-finite is PSPACE-complete.

---

## 6. Soundness

### 6.1 Axiom Verification

**K (Distribution):**
Need: V_w(□(φ → ψ) → (□φ → □ψ)) = 1 for all w, M.

Standard argument using the semantics of □ and →.

**4 (Positive Introspection):**
Need: V_w(□φ → □□φ) = 1.

Follows from graded transitivity: if R(w, w') > 0 and R(w', w'') > 0, then by the frame constraint (accessibility respects ≺), we have w'' ≺ w' ≺ w, so there's an indirect accessibility from w to w''.

**L (Graded Löb):**
Need: V_w(□(□φ → φ) → □φ) = 1, appropriately graded.

This is the key axiom. We need to show that in any CPL-finite frame satisfying converse well-foundedness:

If V_w(□(□φ → φ)) = c, then V_w(□φ) ≥ g_L(c).

**Proof sketch:**
1. Converse well-foundedness ensures we can evaluate □φ bottom-up from ≺-minimal worlds
2. At ≺-minimal worlds w₀: there are no w' with R(w₀, w') > 0, so V_{w₀}(□ψ) = 1 for all ψ
3. Proceeding upward by ≺-induction: the Löb axiom's validity follows from the inductive structure
4. The discount g_L(c) ensures we don't bootstrap confidence

This mirrors the classical GL soundness proof, adapted to the graded setting.

### 6.2 Soundness Theorem

**Theorem (CPL-finite Soundness):**
If CPL-finite ⊢ φ, then ⊨_{CPL-finite} φ.

**Proof:** By induction on proof length, checking each axiom and rule.

---

## 7. Completeness

### 7.1 Canonical Model Construction

**Definition (L₅-Consistent Set):**
A set Γ is L₅-consistent if it has a model (there exists M, w with V_w(φ) = v_Γ(φ) for all φ ∈ Γ).

**Definition (Maximally L₅-Consistent Set):**
Γ is maximally L₅-consistent if:
1. Γ is L₅-consistent
2. For every formula φ, Γ assigns some value v_Γ(φ) ∈ L₅
3. Γ is closed under CPL-finite consequences

**Canonical Frame:**
- W_c = {Γ : Γ is maximally L₅-consistent}
- R_c(Γ, Δ) = sup{c ∈ L₅ : ∀φ. □φ ∈ Γ with value ≥ c ⟹ φ ∈ Δ with value ≥ c}
- ≺_c derived from Löb axiom: Δ ≺_c Γ iff there exists φ with v_Γ(□φ) > v_Δ(□φ)

**Challenge:** Proving ≺_c is well-founded requires careful analysis of the graded Löb axiom.

### 7.2 Truth Lemma

**Lemma (Truth Lemma):**
For all Γ ∈ W_c and all formulas φ:
```
V_c(Γ, φ) = v_Γ(φ)
```

**Proof:** By induction on formula structure.
- Propositional cases: direct from L₅ semantics
- Modal case (□φ): requires showing the canonical frame definition matches the semantic clause

### 7.3 Completeness Theorem

**Theorem (CPL-finite Completeness, Sketch):**
If ⊨_{CPL-finite} φ, then CPL-finite ⊢ φ.

**Proof sketch:**
1. If ⊬ φ, then {¬φ = 1} is consistent
2. Extend to maximally consistent Γ with v_Γ(¬φ) = 1
3. Canonical model M_c has V_c(Γ, φ) = v_Γ(φ) < 1
4. So φ is not valid in M_c

**Confidence:** 0.70 — The proof requires verifying that the canonical frame satisfies the converse well-foundedness constraint, which is non-trivial for graded logics.

---

## 8. Integration with CLAIR

### 8.1 Type-Level Finite Confidence

**CLAIR Definition:**
```clair
-- Finite confidence for decidable type-level checks
type FiniteConfidence =
  | None     -- 0
  | Low      -- 0.25
  | Medium   -- 0.5
  | High     -- 0.75
  | Certain  -- 1

toRational : FiniteConfidence → Rational
toRational None = 0
toRational Low = 1/4
toRational Medium = 1/2
toRational High = 3/4
toRational Certain = 1
```

### 8.2 Operations

```clair
-- Multiplication (conjunction)
(⊗) : FiniteConfidence → FiniteConfidence → FiniteConfidence
Certain ⊗ x = x
x ⊗ Certain = x
None ⊗ _ = None
_ ⊗ None = None
High ⊗ High = Medium    -- 0.75 × 0.75 = 0.5625 → floor to 0.5
High ⊗ Medium = Low     -- 0.75 × 0.5 = 0.375 → floor to 0.25
Medium ⊗ Medium = Low   -- 0.5 × 0.5 = 0.25 ✓
Low ⊗ _ = None          -- 0.25 × anything < 0.25 → floor to 0
_ ⊗ Low = None

-- Probabilistic OR (aggregation)
(⊕) : FiniteConfidence → FiniteConfidence → FiniteConfidence
None ⊕ x = x
x ⊕ None = x
Certain ⊕ _ = Certain
_ ⊕ Certain = Certain
Low ⊕ Low = Medium      -- 0.25 + 0.25 - 0.0625 = 0.4375 → ceil to 0.5
Low ⊕ Medium = High     -- 0.25 + 0.5 - 0.125 = 0.625 → ceil to 0.75
Medium ⊕ Medium = High  -- 0.5 + 0.5 - 0.25 = 0.75 ✓
High ⊕ Low = High       -- 0.75 + 0.25 - 0.1875 = 0.8125 → ceil to 0.75
High ⊕ Medium = Certain -- 0.75 + 0.5 - 0.375 = 0.875 → ceil to 1
High ⊕ High = Certain   -- 0.75 + 0.75 - 0.5625 = 0.9375 → ceil to 1

-- Löb discount
loebDiscount : FiniteConfidence → FiniteConfidence
loebDiscount None = None       -- 0² = 0
loebDiscount Low = None        -- 0.25² = 0.0625 → floor to 0
loebDiscount Medium = Low      -- 0.5² = 0.25 ✓
loebDiscount High = Medium     -- 0.75² = 0.5625 → floor to 0.5
loebDiscount Certain = Certain -- 1² = 1
```

### 8.3 Type-Level Anti-Bootstrapping

```clair
-- Compile-time constraint: self-soundness claims cap confidence
type SelfSoundnessGuard<c : FiniteConfidence> where
  maxDerived : FiniteConfidence
  constraint : maxDerived ≤ loebDiscount(c)

-- Example: if we claim self-soundness at High (0.75),
-- derived beliefs are bounded at Medium (0.5)
claim_soundness : (c : FiniteConfidence) → SelfSoundnessGuard<c>
claim_soundness c = SelfSoundnessGuard { maxDerived = loebDiscount(c), ... }
```

### 8.4 Decidable Type Checking

Because CPL-finite is decidable, CLAIR's type checker can verify:
1. Whether a belief's confidence is consistent with its justification structure
2. Whether anti-bootstrapping constraints are satisfied
3. Whether stratification levels are respected

This is a significant improvement over full CPL, where such checks would be undecidable.

---

## 9. Comparison: CPL-finite vs Related Systems

### 9.1 vs Full CPL

| Property | CPL | CPL-finite |
|----------|-----|------------|
| Values | [0,1] continuous | L₅ = {0, 0.25, 0.5, 0.75, 1} |
| Decidability | Likely undecidable | Decidable |
| Completeness | Uncertain | Likely complete |
| Complexity | N/A | PSPACE (conjectured) |
| g(c) = c² closure | ✓ Exact | Requires floor rounding |
| Type-level checks | Undecidable | Decidable |

### 9.2 vs CPL-0 (Stratified)

| Property | CPL-0 | CPL-finite |
|----------|-------|------------|
| Self-reference | Forbidden | Allowed (with Löb constraint) |
| Decidability | Decidable | Decidable |
| Expressiveness | Lower (no self-ref) | Higher (self-ref allowed) |
| Values | Continuous [0,1] | Discrete L₅ |

### 9.3 vs Finite-valued Łukasiewicz Modal Logic

| Property | ŁK-finite | CPL-finite |
|----------|-----------|------------|
| Base logic | Łukasiewicz | Product-like |
| Löb axiom | None | ✓ Required |
| Frame condition | Transitive | Transitive + conv. well-founded |
| Complexity | PSPACE | PSPACE (conjectured) |
| Self-soundness | No constraint | Anti-bootstrapping |

---

## 10. Open Questions

### 10.1 Exact Complexity

**Question:** Is CPL-finite exactly PSPACE-complete, or could the Löb constraint make it easier?

**Conjecture:** PSPACE-complete. The Löb constraint restricts frames but doesn't fundamentally change the search space structure.

**Confidence:** 0.75

### 10.2 Alternative Lattice Choices

**Question:** Would L₇ = {0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1} give better algebraic properties?

**Analysis:** L₇ includes 0.0625 ≈ 0.25², so Low → Low under squaring. But still doesn't include all squares.

**Trade-off:** More granularity vs. increased state space and complexity.

### 10.3 Sequent Calculus

**Question:** Can we develop a cut-free sequent calculus for CPL-finite?

**Benefit:** Direct completeness proof, potential for better complexity analysis.

**Prior art:** Negri (2005, 2014) developed labelled sequent calculi for classical GL.

### 10.4 Implementation Strategy

**Question:** How should CPL-finite be implemented in CLAIR's type checker?

**Options:**
1. Direct decision procedure (enumerate models)
2. Tableau-based prover
3. SAT/SMT encoding
4. Specialized solver

---

## 11. Summary: What This Exploration Establishes

### 11.1 Key Findings

1. **CPL-finite is well-defined**: The finite lattice L₅ = {0, 0.25, 0.5, 0.75, 1} provides a workable foundation for graded provability logic.

2. **The c² closure problem**: No finite sublattice is closed under c², requiring floor rounding in the Löb discount function g_L(c) = floor_L(c²).

3. **Rounding preserves semantics**: Floor rounding maintains g_L(c) ≤ c, preserving the anti-bootstrapping property.

4. **CPL-finite is decidable**: Following Bou et al. (2011), the finite model property ensures decidability.

5. **PSPACE-completeness likely**: Inherits from finite-valued modal logic complexity results.

6. **Integration with CLAIR**: Enables decidable type-level confidence checks and compile-time anti-bootstrapping verification.

### 11.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| CPL-finite is well-defined | 0.90 | Standard constructions from finite-valued modal logic |
| CPL-finite is decidable | 0.85 | Follows from Bou et al. (2011) finite model property |
| CPL-finite is PSPACE-complete | 0.75 | Analogy to Łukasiewicz modal logic complexity |
| Soundness holds | 0.85 | Standard verification of axioms |
| Completeness holds | 0.70 | Canonical model construction needs verification |
| g_L(c) = floor_L(c²) preserves semantics | 0.90 | Maintains anti-bootstrapping constraint |

### 11.3 Novel Contributions

1. **c² closure impossibility**: Proved no non-trivial finite lattice is closed under squaring
2. **Rounding strategy**: Established floor rounding as the semantically correct approach
3. **Explicit operation tables**: Provided concrete definitions for ⊗, ⊕, g_L on L₅
4. **CLAIR integration design**: Type-level FiniteConfidence with decidable constraints

---

## 12. References

### Primary Sources

- [Bou, Esteva, Godo, Rodríguez (2011)](https://arxiv.org/abs/0811.2107): "On the Minimum Many-Valued Modal Logic over a Finite Residuated Lattice" — Foundational axiomatization
- [Bou, Cerami, Esteva (IJCAI 2011)](https://www.ijcai.org/Proceedings/11/Papers/136.pdf): "Finite-Valued Łukasiewicz Modal Logic Is PSPACE-Complete" — Complexity result
- [Segerberg (1971)](https://plato.stanford.edu/entries/logic-provability/): Classical GL completeness for finite trees
- [Vidal (2019)](https://arxiv.org/abs/1904.01407): "On Transitive Modal Many-Valued Logics" — Undecidability of continuous case

### CLAIR Internal References

- exploration/thread-3.13-graded-provability-logic.md — CPL design
- exploration/thread-3.16-cpl-decidability.md — Full CPL undecidability
- exploration/thread-3.17-cpl-soundness-completeness.md — Proof strategies
- exploration/thread-3.18-loeb-discount.md — g(c) = c² derivation

---

*Thread 3.20 Status: Substantially explored. CPL-finite formalization complete. Decidability established via finite model property. PSPACE complexity conjectured. CLAIR integration designed.*
