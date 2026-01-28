# Thread 3.16: CPL Decidability

> **Status**: Explored (Session 25)
> **Question**: Is Confidence-Bounded Provability Logic (CPL) decidable?
> **Priority**: HIGH — Determines if CPL is computationally tractable for CLAIR
> **Prior Thread**: Thread 3.13 (Graded Provability Logic design)

---

## 1. The Question

Thread 3.13 proposed CPL (Confidence-Bounded Provability Logic) as a graded extension of GL (Gödel-Löb provability logic) with:
- Confidence values in [0,1]
- Graded K, 4, and L (Löb) axioms
- No truth axiom (preserving fallibilism)
- Anti-bootstrapping theorem

**Core question:** Is CPL decidable? Classical GL is decidable (PSPACE-complete). Does adding graded confidence preserve decidability?

---

## 2. Background: Why Decidability Matters

### 2.1 For CLAIR

If CPL is decidable:
- Type-level anti-bootstrapping checks can be automated
- Compile-time verification of Löbian constraints is tractable
- The logic has a decision procedure for validity

If CPL is undecidable:
- Anti-bootstrapping becomes a heuristic, not a guarantee
- Some self-referential patterns cannot be checked mechanically
- Must rely on syntactic restrictions or conservative approximations

### 2.2 Classical GL Decidability

Classical GL is decidable via the **finite model property** (FMP):

**Theorem (Segerberg 1971; de Jongh-Kripke):**
GL is complete with respect to finite transitive irreflexive trees. Any formula not provable in GL is falsifiable in a finite model.

**Consequence:** PSPACE-complete decision procedure—test satisfiability by searching finite models of bounded size (exponential in formula length).

**Key frame property:** GL frames are transitive and conversely well-founded (no infinite ascending chains). Converse well-foundedness implies irreflexivity and forces finite-depth evaluation.

---

## 3. Prior Art: Decidability of Fuzzy/Many-Valued Modal Logics

### 3.1 The Landscape

| Logic | Base | Transitivity | Decidability |
|-------|------|--------------|--------------|
| Fuzzy K (Łukasiewicz) | Standard MV | No | ✓ Decidable |
| Fuzzy K (Product) | Standard Product | No | ✓ Decidable |
| Fuzzy K (Gödel) | Gödel algebra | No | ✓ Decidable |
| Transitive Łukasiewicz | Standard MV | Yes (K4) | ✗ **Undecidable** |
| Transitive Product | Standard Product | Yes (K4) | ✗ **Undecidable** |
| Transitive Gödel | Gödel algebra | Yes | Open |
| S5 Łukasiewicz | Standard MV | S5 | ✓ Decidable |
| Global Modal | Łukasiewicz/Product | Various | ✗ **Undecidable** |

### 3.2 The Critical Vidal Result

**Theorem (Vidal 2019, "On Transitive Modal Many-Valued Logics"):**
For a large family of modal logics over transitive Kripke frames evaluated on residuated lattices—including standard MV (Łukasiewicz) and Product algebras—the consequence relation is **undecidable**, even when restricted to finite models.

**Source:** [arXiv:1904.01407](https://arxiv.org/abs/1904.01407), [ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0165011418310893)

**Key insight:** This provides "an example of a decidable modal logic whose transitive expansion is undecidable."

### 3.3 Why Transitivity Causes Problems

Classical K is decidable; classical K4 (adding transitivity) is also decidable (PSPACE-complete).

But in the fuzzy setting:
- Łukasiewicz K is decidable
- Łukasiewicz K4 (transitive) is **undecidable**

The proof involves encoding undecidable problems (like Post correspondence or tiling problems) into the transitivity constraints. The continuous [0,1] values, combined with transitivity, allow encoding arbitrary computations.

### 3.4 Gödel Modal Logic

**Theorem (Caicedo, Metcalfe, Rodríguez, Rogger 2013):**
Gödel modal logics (both crisp and fuzzy accessibility) are decidable and PSPACE-complete.

**However:** This uses a non-standard semantics (quasimodels) because Gödel modal logic **lacks the finite model property** with respect to standard [0,1]-valued Kripke semantics.

**Source:** [Springer](https://link.springer.com/chapter/10.1007/978-3-642-39992-3_20)

---

## 4. Analysis: CPL Decidability

### 4.1 CPL's Frame Requirements

CPL, as a graded extension of GL, requires:
1. **Transitivity** (axiom 4: □A → □□A)
2. **Converse well-foundedness** (for Löb's axiom)
3. **Graded accessibility** (confidence values on edges)
4. **Graded valuation** (confidence values for propositions)

The Vidal result directly threatens CPL: transitivity + many-valued semantics = likely undecidable.

### 4.2 Hope from Converse Well-Foundedness?

GL's converse well-foundedness is stronger than just transitivity:
- Transitive frames: K4
- Transitive + conversely well-founded: GL

Could converse well-foundedness rescue decidability?

**Analysis:** Converse well-foundedness forces finite descending chains. In the classical case, this (combined with irreflexivity) ensures finite-depth trees suffice.

In the graded case:
- Accessibility values are in [0,1]
- Converse well-foundedness still applies to the support relation
- But the continuous values introduce new encoding power

**Conjecture:** Converse well-foundedness may help, but is unlikely to overcome the fundamental undecidability from continuous values + transitivity.

### 4.3 The Core Tension

GL's decidability relies on:
1. Finite model property (via converse well-foundedness)
2. Finite-depth evaluation (finite trees suffice)

CPL's grading introduces:
1. Continuous [0,1] values
2. Algebraic operations (×, ⊕, undercut)
3. Confidence propagation through graded edges

The question: can we maintain finite depth while allowing continuous values?

---

## 5. Three Scenarios for CPL

### 5.1 Scenario A: CPL is Undecidable (Most Likely)

**Argument:**
1. Vidal proves transitive modal Łukasiewicz is undecidable
2. CPL uses continuous [0,1] values with transitivity
3. CPL's operations (×, ⊕) are similar to Łukasiewicz t-norms
4. Therefore, CPL likely inherits undecidability

**Implications for CLAIR:**
- Cannot fully automate anti-bootstrapping checks
- Must use syntactic restrictions or conservative approximations
- The Löb constraint becomes a design guideline, not a provable property

### 5.2 Scenario B: CPL is Decidable via Restricted Semantics

**Possible approach:** Following Gödel modal logic's method:
1. Abandon standard [0,1] semantics
2. Define quasimodel semantics with finite representation
3. Prove quasimodel completeness
4. Show finite quasimodel property

**Requirements:**
- Quasimodels must capture the anti-bootstrapping theorem
- Must preserve the graded Löb axiom's meaning
- Proof would be highly non-trivial

**Technical hurdle:** Gödel logic has special properties (min/max operations, idempotent conjunction) that CPL lacks. CPL uses multiplicative operations which behave more like Product/Łukasiewicz.

### 5.3 Scenario C: CPL is Decidable via Finite Value Restriction

**Alternative approach:** Restrict to finite confidence values.

**Theorem (Bou, Esteva, Godo 2011):**
Many-valued modal logics over **finite** residuated lattices are decidable.

**Source:** [Journal of Logic and Computation](https://academic.oup.com/logcom/article-abstract/21/5/739/971984)

If CLAIR restricts confidence to a finite set (e.g., {0, 0.25, 0.5, 0.75, 1.0}), CPL becomes decidable.

**Trade-off:**
- Gain: Decidability
- Lose: Continuous confidence representation
- Pragmatic: 5-10 discrete levels may suffice for practical reasoning

---

## 6. Detailed Technical Analysis

### 6.1 Why GL is Decidable but Graded GL May Not Be

**Classical GL's FMP proof:**

1. Given a non-theorem φ, construct a canonical model
2. GL's non-canonicity is handled via filtration
3. Converse well-foundedness limits model depth
4. Any countermodel can be "chopped" to finite depth

**Graded extension obstacles:**

1. **Filtration fails for continuous values:** Classical filtration quotients by formula equivalence; continuous values break this
2. **Canonical model construction differs:** Standard MV/Product canonical models are infinite and undecidable
3. **Converse well-foundedness doesn't bound value range:** Even with finite depth, infinitely many confidence values are possible

### 6.2 The Encoding Problem

**Undecidability proofs for transitive fuzzy logics** typically encode:
- Post correspondence problem
- Tiling/domino problems
- Halting problem fragments

**The encoding uses:**
- Transitivity to propagate constraints across distances
- Continuous values to encode arbitrary information
- Modal operators to simulate computation steps

**CPL's additional Löb constraint** might prevent some encodings (anti-bootstrapping limits what can be asserted), but this is speculative.

### 6.3 Potential Decidable Fragments

Even if full CPL is undecidable, fragments may be decidable:

| Fragment | Restriction | Likely Decidable? |
|----------|-------------|-------------------|
| CPL-finite | Finite confidence values | ✓ Yes |
| CPL-0 | No self-reference (stratified only) | ✓ Likely |
| CPL-bounded | Maximum formula depth | ✓ Yes |
| CPL-local | No global consequence | Possible |
| CPL-monadic | No nested modalities | ✓ Yes |

For CLAIR, **CPL-finite** or **CPL-0** are most relevant:
- CPL-finite: practical approximation of continuous confidence
- CPL-0: relies on Thread 3's stratification (no same-level self-reference)

---

## 7. Implications for CLAIR Design

### 7.1 If CPL is Undecidable

**Strategy 1: Syntactic Restrictions**
```clair
-- Enforce stratification (Thread 3)
-- No same-level self-reference by construction
type Belief<n : Level, A> where
  -- Level-n can only reference Level-(n-1)
  justification : Justification<n-1>
```

Anti-bootstrapping becomes a syntactic invariant, not a semantic theorem.

**Strategy 2: Conservative Type Checking**
```clair
-- Reject any formula where decidability is unclear
-- Over-approximate the undecidable cases
type SelfSoundnessCheck<A> =
  | Safe        -- Proven safe
  | Unsafe      -- Proven Löbian
  | Unknown     -- Cannot decide → reject conservatively
```

**Strategy 3: Finite Confidence Levels**
```clair
-- Restrict to 5 discrete levels
type DiscreteConfidence = 0.0 | 0.25 | 0.5 | 0.75 | 1.0

-- All CPL constraints become decidable
-- Trade-off: lose granularity
```

### 7.2 If CPL is Decidable via Quasimodels

Would need to:
1. Define CPL quasimodels formally
2. Prove quasimodel completeness
3. Implement decision procedure based on quasimodel search
4. Integrate into CLAIR's type checker

This is a substantial research program (PhD-level work).

### 7.3 Recommended Approach for CLAIR

Given the evidence:
1. **Assume CPL is likely undecidable** (conservative stance)
2. **Use stratification** (Thread 3) as primary safety mechanism
3. **Consider finite confidence** for type-level checking
4. **Leave anti-bootstrapping as semantic guideline** for runtime

This aligns with CLAIR's philosophy: pragmatic dogmatism with honest uncertainty.

---

## 8. Open Research Questions

### 8.1 Immediate Questions

1. **Does converse well-foundedness help?**
   - Formal analysis of whether GL's frame condition ameliorates the Vidal undecidability

2. **Is CPL-Gödel decidable?**
   - CPL using Gödel algebra (min/max) instead of product operations
   - May inherit Gödel modal logic's decidability

3. **What is the smallest undecidable fragment?**
   - Pinpoint exactly where undecidability arises
   - Identifies maximal decidable fragment

### 8.2 Longer-Term Research

1. **Develop CPL quasimodel theory**
   - Non-standard semantics preserving anti-bootstrapping
   - Potential route to decidability

2. **Prove undecidability formally**
   - Reduce known undecidable problem to CPL
   - Would settle the question definitively

3. **Complexity of decidable fragments**
   - CPL-finite likely PSPACE or EXPTIME
   - Practical implementations need complexity bounds

---

## 9. Conclusion

### 9.1 The Verdict

**CPL is very likely undecidable.**

The combination of:
- Transitivity (required for axiom 4)
- Continuous [0,1] confidence values
- Multiplicative operations (×, ⊕)

matches the undecidability pattern proven by Vidal (2019) for transitive modal many-valued logics.

Converse well-foundedness (the additional GL constraint) may restrict the class of frames, but is unlikely to overcome the fundamental undecidability arising from continuous values in transitive contexts.

### 9.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| CPL is undecidable | 0.75 | Strong analogy to Vidal result; transitivity + continuous values |
| CPL-finite is decidable | 0.90 | Follows from Bou et al. (2011) on finite lattices |
| CPL-0 (stratified) is decidable | 0.85 | No self-reference removes problematic encodings |
| Quasimodel approach could work | 0.40 | Possible but highly non-trivial; unproven |

### 9.3 Recommendation for CLAIR

**Pragmatic stance:** Accept that full CPL is likely undecidable, and design CLAIR to work within decidable fragments:

1. **Stratification** (Thread 3) handles the safety of self-reference syntactically
2. **Anti-bootstrapping** remains a semantic guideline, not a checked invariant
3. **Finite confidence levels** can be used where type-level decidability is required
4. **Honest uncertainty** about full decidability is appropriate

This is consistent with CLAIR's philosophy: we don't claim more than we can prove.

---

## 10. Summary: What This Exploration Establishes

### 10.1 Key Findings

1. **Classical GL decidability** relies on the finite model property from converse well-foundedness
2. **Transitive fuzzy modal logics** are generally undecidable (Vidal 2019)
3. **CPL inherits the undecidability risk** from combining transitivity with continuous values
4. **Decidable fragments exist**: finite values, stratified (no self-reference), bounded depth
5. **Alternative semantics** (quasimodels) might rescue decidability but is unproven

### 10.2 New Understanding

The decision question for CPL is not merely open—we now have strong evidence pointing toward undecidability. This shifts the design strategy from "prove decidability" to "work within decidable fragments."

### 10.3 Impact on CLAIR

CLAIR should:
- Not promise compile-time verification of full CPL constraints
- Rely on stratification as the primary safety mechanism
- Consider finite confidence for type-level operations
- Document that anti-bootstrapping is a semantic guideline

---

## 11. References

### Primary Sources Consulted

- [Vidal (2019), "On Transitive Modal Many-Valued Logics"](https://arxiv.org/abs/1904.01407) — Key undecidability result
- [Stanford Encyclopedia: Provability Logic](https://plato.stanford.edu/entries/logic-provability/) — GL decidability background
- [Caicedo et al. (2013), "A Finite Model Property for Gödel Modal Logics"](https://link.springer.com/chapter/10.1007/978-3-642-39992-3_20) — Quasimodel approach
- [Bou et al. (2011), "On the Minimum Many-Valued Modal Logic over a Finite Residuated Lattice"](https://academic.oup.com/logcom/article-abstract/21/5/739/971984) — Finite lattice decidability
- [Boolos (1993), "The Logic of Provability"](https://www.cambridge.org/core/books/logic-of-provability/completeness-and-decidability-of-gl-and-k-k4-t-b-s4-and-s5/4BA38E9FF8D82235691F668D13C379FD) — Classical GL foundations

### CLAIR Internal References

- exploration/thread-3.13-graded-provability-logic.md — CPL design proposal
- exploration/thread-3-self-reference.md — Stratification approach
- exploration/thread-8-verification.md — Confidence operations

---

*Thread 3.16 Status: Explored. CPL likely undecidable. Decidable fragments identified. Pragmatic design recommendations established.*
