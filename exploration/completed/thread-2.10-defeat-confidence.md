# Thread 2.10: Defeat Confidence Propagation

> **Status**: Active exploration (Session 12)
> **Task**: 2.10 How does defeat (undercut/rebut) affect confidence?
> **Question**: When an argument is defeated, how should its confidence change?
> **Priority**: CRITICAL — Central open question connecting Threads 2 and 8

---

## 1. The Problem

Thread 2 established that CLAIR's justification structure is a **DAG with labeled edges**:
- **Support edges**: Positive contribution to confidence (handled by ×, min, ⊕)
- **Undercut edges**: Attack the justification link
- **Rebut edges**: Attack the conclusion directly

Thread 8 formalized the confidence operations for support:
- Multiplication (×): For conjunctive/sequential derivation
- Minimum (min): For conservative combination
- Probabilistic OR (⊕): For aggregation of independent evidence

**But what happens to confidence when a belief is defeated?**

This is the critical missing piece. Without it, we cannot:
1. Properly evaluate beliefs under attack
2. Model defeasible reasoning in CLAIR
3. Connect our justification DAGs to meaningful confidence values

---

## 2. Prior Art Survey

### 2.1 Pollock's Defeaters (1987, 2001)

John Pollock distinguished two types of defeat:

**Rebutting defeaters**: Attack the conclusion directly. If I believe P with confidence 0.8, and receive evidence for ¬P with confidence 0.7, these are competing beliefs.

**Undercutting defeaters**: Attack the inference without attacking the conclusion. Example: "The witness was drunk" undercuts testimony without providing evidence for any particular conclusion.

**Key insight from Pollock**: The *weakest link principle* — an argument's strength is determined by its weakest step. More precisely:
> "The degree of justification of a conclusion is the maximum over all arguments for the conclusion of the minimum strength of each step in the argument."

This suggests defeat might work by making the attacked step the "weakest link."

**Pollock's treatment of defeat**: Pollock used *prima facie* vs *ultima facie* justification. An argument is prima facie justified if it follows valid inference rules; it is ultima facie justified if it is not defeated. He did NOT use numerical confidence but rather binary defeated/not-defeated status.

**Variable degrees of justification (2001)**: Pollock later explored graded justification, computing "on sum" degrees based on argument strengths and defeater strengths. However, the specific propagation rules are complex and context-dependent.

**Sources**:
- [Stanford Encyclopedia: Defeasible Reasoning](https://plato.stanford.edu/entries/reasoning-defeasible/)
- Pollock, "Defeasible Reasoning" (1987)
- Pollock, "Defeasible Reasoning with Variable Degrees of Justification" (2001)

### 2.2 Dung's Abstract Argumentation (1995)

Dung's framework is more abstract—arguments are nodes, attacks are edges, and various *semantics* determine which sets of arguments are "acceptable."

**Key semantics**:
- **Grounded extension**: Unique, computed by iteratively accepting unattacked arguments and removing attacked ones
- **Preferred extension**: Maximal admissible sets (conflict-free + self-defending)
- **Stable extension**: Conflict-free sets that attack all non-members

**Relationship to confidence**: Dung's framework is *qualitative*—arguments are in/out, not graded. This is too coarse for CLAIR.

**Extension to weighted/gradual semantics**: Recent work extends Dung's framework to handle numerical strengths:

**Gradual semantics**: Assign each argument a strength value from a totally ordered scale. Key principles:
1. **Maximality**: Unattacked arguments with maximum basic strength get maximum final strength
2. **Void Precedence**: Unattacked arguments are stronger than attacked ones
3. **Quality Precedence**: Being attacked by strong arguments hurts more than weak ones
4. **Cardinality Precedence**: Being attacked by more arguments hurts more
5. **Compensation**: Attack strength balances quality vs quantity

**Key formulas from weighted argumentation**:

Several gradual semantics have been proposed:

**h-categorizer (Besnard & Hunter)**:
```
strength(a) = w(a) / (1 + Σ_{b attacks a} strength(b))
```
The denominator accumulates attacker strengths.

**Max-based semantics**:
```
strength(a) = w(a) - max_{b attacks a} strength(b)
```
Focus on the strongest attacker only.

**Card-based semantics**:
```
strength(a) = w(a) / (1 + |attackers(a)|)
```
Number of attackers matters, not their strength.

**Sources**:
- [Wikipedia: Argumentation Framework](https://en.wikipedia.org/wiki/Argumentation_framework)
- Amgoud & Ben-Naim, "Weighted Bipolar Argumentation Graphs" (2023)
- [Evaluation of Argument Strength in Attack Graphs](https://www.sciencedirect.com/science/article/abs/pii/S0004370221001582)

### 2.3 Subjective Logic Discounting (Jøsang)

Subjective Logic provides a principled approach to trust propagation via the **discounting operator**.

**Opinion representation**: ω = (b, d, u, a) where:
- b = belief mass
- d = disbelief mass
- u = uncertainty mass (b + d + u = 1)
- a = base rate (prior)

**Trust discounting**: When source S reports opinion ω_x about proposition X, and we have trust opinion ω_s about S, the discounted opinion is:

```
ω'_x = ω_s ⊗ ω_x = (b_s · b_x, b_s · d_x + d_s, u_s + b_s · u_x, a_x)
```

**Key insight**: Discounting:
1. Reduces belief mass proportional to trust in source
2. Transfers disbelief to uncertainty when source is distrusted
3. Uncertainty accumulates through the chain

**Relevance to defeat**: Undercutting defeat is analogous to reducing trust in the source/inference. If an undercut attacks with strength s, we might discount by (1-s).

**Sources**:
- [Subjective Logic Wikipedia](https://en.wikipedia.org/wiki/Subjective_logic)
- Jøsang, "Subjective Logic" (2016 book)
- [UAI 2016 Tutorial on Subjective Logic](https://www.auai.org/uai2016/tutorials_pres/subj_logic.pdf)

### 2.4 Spohn's Ranking Theory

Wolfgang Spohn's ranking theory uses *ordinal* rather than numerical measures of belief strength.

**Ranking functions**: κ : W → ℕ ∪ {∞} assigns "disbelief ranks" to possible worlds. Lower rank = more plausible. At least one world has rank 0.

**Proposition rank**: κ(A) = min{κ(w) : w ∈ A}

**Conditionalization**: Similar to Bayesian updating but ordinal.

**Relevance to defeat**: Ranking theory handles belief revision in a way that naturally accommodates defeat—when evidence arrives, ranks shift. The ordinal nature avoids numerical precision issues.

**Key insight**: Perhaps defeat should shift *ranks* rather than multiply/subtract numbers. This would be more robust to calibration issues.

**Sources**:
- [Ranking Theory Wikipedia](https://en.wikipedia.org/wiki/Ranking_theory)
- Spohn, "The Laws of Belief" (2012)
- [Belief Revision II: Ranking Theory](https://philsci-archive.pitt.edu/10839/1/Belief_Revision_II.pdf)

### 2.5 Jeffrey Conditioning (Probability Kinematics)

Richard Jeffrey extended Bayesian conditioning to handle *uncertain* evidence.

**Standard Bayes**: P_new(A) = P_old(A|E) when E is observed with certainty.

**Jeffrey conditioning**: When evidence shifts P(B) to P_new(B) without certainty:
```
P_new(A) = P_old(A|B) · P_new(B) + P_old(A|¬B) · P_new(¬B)
```

The conditional probabilities P(A|B) and P(A|¬B) are preserved.

**Relevance to defeat**: When a defeater arrives, it shifts our confidence in the premises/inference. Jeffrey conditioning provides a principled way to propagate this through the belief network.

**Key insight**: Defeat might not directly reduce confidence but rather shift the probability of the inference being reliable.

**Sources**:
- [Radical Probabilism Wikipedia](https://en.wikipedia.org/wiki/Radical_probabilism)
- Jeffrey, "Probability Kinematics" (1983)

---

## 3. Analysis of Options

Based on the prior art, I identify five main approaches for how defeat could affect confidence:

### Option 1: Subtractive Model

```
c' = max(0, c - defeat_strength)
```

**Pros**:
- Simple and intuitive
- Direct reduction in confidence

**Cons**:
- Asymmetric: defeat of 0.5 on 0.9 gives 0.4, but same defeat on 0.4 gives 0
- Doesn't respect the [0,1] bound naturally (needs max)
- No clear justification from probability theory

### Option 2: Multiplicative Discounting

```
c' = c × (1 - defeat_strength)
```

**Pros**:
- Always preserves [0,1] bounds
- Proportional reduction (stronger beliefs remain stronger)
- Aligns with Subjective Logic discounting
- Compositional: multiple defeaters compose naturally

**Cons**:
- Never reaches 0 exactly (asymptotic)
- May be too lenient for strong defeaters

**Variant**: With threshold
```
c' = c × (1 - defeat_strength) if defeat_strength < τ
c' = 0                          otherwise
```

### Option 3: Divisor Accumulation (h-categorizer style)

```
c' = c / (1 + defeat_strength)
```

**Pros**:
- Accumulation-friendly: multiple defeaters naturally combine
- Gradual degradation
- Used in established argumentation literature

**Cons**:
- Result can exceed original (if defeat_strength < 0?)
- No clear probabilistic interpretation

### Option 4: Max-Based (Weakest Link)

```
c' = min(c, 1 - defeat_strength)
```

**Pros**:
- Follows Pollock's weakest link principle
- Simple to understand
- The strongest defeater determines the floor

**Cons**:
- Multiple weak defeaters have no more effect than one
- Binary-ish behavior (either defeats significantly or not)

### Option 5: Probabilistic Negation

```
c' = c × ¬defeat_strength = c × (1 - defeat_strength)
```

This is identical to Option 2 but interpreted differently:
- defeat_strength is the "probability" the defeat succeeds
- (1 - defeat_strength) is the probability the inference survives

**Combined model**: For multiple defeaters D₁, ..., Dₙ:
```
c' = c × ∏ᵢ (1 - dᵢ)
```

---

## 4. Critical Distinction: Undercut vs Rebut

The options above may need to differ based on defeat type:

### 4.1 Undercutting Defeat

Undercut attacks the *inference*, not the conclusion. Example:
- Inference: "Witness testimony → Event occurred"
- Undercut: "Witness was drunk"

The undercut doesn't provide evidence for "Event didn't occur"—it just weakens the inference link.

**Proposed treatment**: Undercut reduces the *strength factor* of the rule/inference:
```
strength'(rule) = strength(rule) × (1 - undercut_strength)
```

Then confidence propagates normally through the weakened rule.

### 4.2 Rebutting Defeat

Rebut attacks the *conclusion* directly. Example:
- Conclusion: "The suspect is guilty" (c = 0.8)
- Rebutter: "The suspect has alibi" (d = 0.7)

Both provide evidence for contradictory conclusions.

**Options for rebut**:

**Option A: Competing beliefs**
Keep both beliefs with their confidences. Let downstream reasoning handle the conflict.

**Option B: Net confidence**
```
c' = c - d  (clamped to [0,1])
```

**Option C: Probabilistic comparison**
```
c' = c / (c + d)  (normalized)
```
This gives the "market share" of confidence.

**Option D: Subjective Logic fusion**
Combine as conflicting opinions, yielding a new opinion that reflects the disagreement.

---

## 5. Deep Analysis: Mathematical Properties

### 5.1 Desired Properties

What properties should defeat propagation satisfy?

**P1: Boundedness preservation**
```
∀c, d ∈ [0,1]: defeat(c, d) ∈ [0,1]
```

**P2: Monotonicity in confidence**
```
c₁ ≤ c₂ ⟹ defeat(c₁, d) ≤ defeat(c₂, d)
```
Stronger beliefs should remain stronger after same defeat.

**P3: Monotonicity in defeat**
```
d₁ ≤ d₂ ⟹ defeat(c, d₁) ≥ defeat(c, d₂)
```
Stronger defeat should reduce confidence more.

**P4: Identity**
```
defeat(c, 0) = c
```
Zero defeat leaves confidence unchanged.

**P5: Annihilation**
```
defeat(c, 1) = 0  OR  defeat(c, 1) = ε (very small)
```
Perfect defeat eliminates confidence (or nearly so).

**P6: Compositionality**
```
defeat(defeat(c, d₁), d₂) = defeat(c, combine(d₁, d₂))
```
Sequential defeats should have predictable combined effect.

### 5.2 Property Analysis of Options

| Option | P1 | P2 | P3 | P4 | P5 | P6 |
|--------|----|----|----|----|----|----|
| Subtractive | ✓* | ✓ | ✓ | ✓ | ✓ | ✗ |
| Multiplicative | ✓ | ✓ | ✓ | ✓ | ✗** | ✓ |
| Divisor | ✓ | ✓ | ✓ | ✓ | ✗ | ✗ |
| Max-based | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

*With max(0, ·) clamping
**Approaches 0 asymptotically but never reaches it

### 5.3 Recommendation: Multiplicative for Undercut

For undercutting defeat, I recommend **multiplicative discounting**:

```lean
def undercut (c : Confidence) (d : Confidence) : Confidence :=
  ⟨c.val * (1 - d.val), by
    constructor
    · exact mul_nonneg c.property.1 (by linarith [d.property.2])
    · calc c.val * (1 - d.val)
        ≤ 1 * 1 := by nlinarith [c.property.1, c.property.2, d.property.1, d.property.2]
        _ = 1 := by ring⟩
```

**Justification**:
1. Preserves [0,1] bounds without clamping
2. Compositional: `undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)` where ⊕ is probabilistic OR
3. Aligns with Subjective Logic discounting
4. Probabilistic interpretation: (1-d) is "survival probability"

### 5.4 Recommendation: Probabilistic Comparison for Rebut

For rebutting defeat, I recommend **normalized confidence**:

```lean
def rebut (c_for : Confidence) (c_against : Confidence) : Confidence :=
  if h : c_for.val + c_against.val = 0
  then ⟨0.5, by norm_num, by norm_num⟩  -- maximal uncertainty
  else ⟨c_for.val / (c_for.val + c_against.val), by
    constructor
    · exact div_nonneg c_for.property.1 (by linarith [c_for.property.1, c_against.property.1])
    · exact div_le_one_of_le (by linarith [c_against.property.1]) (by linarith [c_for.property.1, c_against.property.1])⟩
```

**Justification**:
1. Treats for/against symmetrically
2. Result is naturally in [0,1]
3. Equal arguments → 0.5 (maximal uncertainty)
4. Overwhelming argument → approaches 1 or 0
5. Intuitive "market share" interpretation

---

## 6. Multiple Defeaters

### 6.1 Multiple Undercuts

When multiple undercuts attack the same inference:

**Option A: Multiplicative composition**
```
c' = c × ∏ᵢ (1 - dᵢ)
```
Each undercut independently reduces survival probability.

**Option B: Max-based**
```
c' = c × (1 - max(dᵢ))
```
Only the strongest undercut matters.

**Option C: Aggregated then applied**
```
d_combined = d₁ ⊕ d₂ ⊕ ... ⊕ dₙ  (probabilistic OR)
c' = c × (1 - d_combined)
```

**Recommendation**: Option C, for consistency with aggregation semantics.

### 6.2 Multiple Rebuts

When multiple arguments rebut each other:

**Option A: Pairwise**
Compute rebut(c_for, c_against) for net pro/con.

**Option B: Weighted pool**
```
c' = Σ(pro_arguments) / Σ(all_arguments)
```

**Recommendation**: Option B for multi-argument scenarios.

### 6.3 Mixed Defeat

When both undercuts and rebuts are present:

**Proposed order**:
1. First, apply undercuts to weaken the inference
2. Then, compare weakened belief against rebuts

```
c_weakened = c × ∏ᵢ (1 - undercut_i)
c_final = rebut(c_weakened, c_against)
```

---

## 7. Connection to CLAIR Design

### 7.1 Edge Types and Confidence

The labeled edge types from Thread 2 now have confidence semantics:

```lean
inductive EdgeEffect where
  | support : Confidence → EdgeEffect      -- positive contribution
  | undercut : Confidence → EdgeEffect     -- multiplicative reduction
  | rebut : Confidence → EdgeEffect        -- competing conclusion

def applyEdge (c : Confidence) (e : EdgeEffect) : Confidence :=
  match e with
  | .support s => c * s           -- multiply by support strength
  | .undercut d => undercut c d   -- multiplicative discounting
  | .rebut r => rebut c r         -- probabilistic comparison
```

### 7.2 DAG Evaluation

To evaluate a belief's final confidence in a DAG:

```
function evaluateConfidence(node):
  if node is axiom:
    return node.base_confidence

  # Gather all edges
  supports = [e for e in node.edges if e.type == Support]
  undercuts = [e for e in node.edges if e.type == Undercut]
  rebuts = [e for e in node.edges if e.type == Rebut]

  # Combine supports (multiplicative or aggregative)
  c_base = combineSupports(supports)

  # Apply undercuts
  for u in undercuts:
    c_base = undercut(c_base, evaluateConfidence(u.source))

  # Apply rebuts
  if rebuts:
    c_against = aggregateRebuts(rebuts)
    return rebut(c_base, c_against)
  else:
    return c_base
```

### 7.3 Invalidation and Defeat

There's a connection between defeat and invalidation:

- **Invalidation**: Binary—the belief's support is gone (source changed, assumption false)
- **Defeat**: Graded—the belief's support is weakened

An invalidated belief could be modeled as:
```
undercut(c, 1.0) = 0
```

Or invalidation could be kept separate from defeat, as it currently is.

---

## 8. What I Don't Know

### 8.1 Empirical Unknowns

1. **Which model matches intuition?** Need user studies to see if multiplicative vs subtractive matches human reasoning.

2. **Calibration**: If Igal Tabachnik's confidence isn't calibrated, does the choice of defeat model matter?

3. **Context dependence**: Should different domains use different defeat models? (Legal reasoning vs scientific reasoning vs everyday inference)

### 8.2 Theoretical Unknowns

1. **Graded vs categorical defeat**: Should defeat be graded (0.7 undercut) or categorical (defeats/doesn't defeat)?

2. **Interaction with aggregation**: If c = a ⊕ b (aggregated), and we undercut the a-part, do we:
   - Undercut c directly?
   - Undercut a, recompute c?
   The second seems more principled but requires tracking internal structure.

3. **Reinstatement**: When a defeater is itself defeated, should the original belief be reinstated? At what confidence?

4. **Fixed points**: In cyclical defeat structures (A defeats B defeats C defeats A), is there a stable fixed point?

### 8.3 Implementation Unknowns

1. **Computational complexity**: With many defeaters, evaluation could be expensive.

2. **Incrementality**: Can we update confidence incrementally when new defeaters arrive, or must we recompute from scratch?

3. **Caching**: How to cache intermediate results in DAG evaluation?

---

## 9. Formalization Status

### 9.1 Ready for Lean 4

**Undercut operation**:
```lean
def undercut (c d : Confidence) : Confidence :=
  ⟨c.val * (1 - d.val), ⟨mul_nonneg c.prop.1 (sub_nonneg_of_le d.prop.2),
    by nlinarith [c.prop.1, c.prop.2, d.prop.1, d.prop.2]⟩⟩

theorem undercut_bounded (c d : Confidence) :
    0 ≤ (undercut c d).val ∧ (undercut c d).val ≤ 1 := (undercut c d).property

theorem undercut_zero (c : Confidence) : undercut c 0 = c := by
  simp [undercut, Zero.zero]; ext; ring

theorem undercut_one (c : Confidence) : (undercut c 1).val = 0 := by
  simp [undercut, One.one]; ring

theorem undercut_monotone_conf (c₁ c₂ d : Confidence) (h : c₁.val ≤ c₂.val) :
    (undercut c₁ d).val ≤ (undercut c₂ d).val := by
  simp [undercut]; nlinarith [d.prop.1, d.prop.2]

theorem undercut_monotone_defeat (c d₁ d₂ : Confidence) (h : d₁.val ≤ d₂.val) :
    (undercut c d₂).val ≤ (undercut c d₁).val := by
  simp [undercut]; nlinarith [c.prop.1]
```

**Rebut operation**:
```lean
def rebut (c_for c_against : Confidence) : Confidence :=
  if h : c_for.val + c_against.val = 0
  then ⟨0.5, by norm_num, by norm_num⟩
  else ⟨c_for.val / (c_for.val + c_against.val), sorry⟩  -- bound proofs needed

theorem rebut_symmetric_eq (c : Confidence) : (rebut c c).val = 0.5 := by
  simp [rebut]; sorry  -- need case analysis on whether c = 0
```

### 9.2 Not Yet Ready

- Composition of multiple undercuts
- Interaction with aggregation (⊕)
- DAG evaluation algorithm
- Fixed-point semantics for cyclic defeat

---

## 10. Conclusions

### 10.1 Answers to the Central Question

**How does defeat affect confidence?**

**For undercutting defeat**: Multiplicative discounting
```
c' = c × (1 - defeat_strength)
```

**For rebutting defeat**: Probabilistic comparison
```
c' = c_for / (c_for + c_against)
```

**For multiple defeats**: Aggregate defeater strengths using ⊕, then apply

### 10.2 Key Insights

1. **Undercut ≠ Rebut**: They require different mathematical treatment
2. **Multiplicative is compositional**: Aligns with Subjective Logic and probability theory
3. **Probabilistic comparison is symmetric**: Treats competing arguments fairly
4. **Order matters**: Apply undercuts before rebuts
5. **The weakest link principle has limitations**: It ignores quantity of attackers

### 10.3 Connection to Prior Art

| Approach | CLAIR Adaptation |
|----------|------------------|
| Pollock's weakest link | Informed min-based alternative for conservative contexts |
| Dung's extensions | Not directly applicable (qualitative, not graded) |
| Subjective Logic discounting | Basis for undercut semantics |
| Gradual argumentation | Informed design principles |
| Ranking theory | Could inform ordinal variant if calibration issues arise |

### 10.4 Next Steps

1. **Task 8.7+**: Add undercut and rebut to Lean 4 formalization
2. **Task 2.14**: Update derivation-calculus.md with defeat operations
3. **Task 2.12**: Explore reinstatement (when defeater is defeated)
4. **Task 2.13**: Handle correlated evidence in defeat contexts

---

## 11. References

### Primary Sources

- Pollock, J. (1987). "Defeasible Reasoning." *Cognitive Science*, 11(4), 481-518.
- Pollock, J. (2001). "Defeasible Reasoning with Variable Degrees of Justification." *Artificial Intelligence*, 133, 233-282.
- Dung, P.M. (1995). "On the acceptability of arguments." *Artificial Intelligence*, 77, 321-357.
- Jøsang, A. (2016). *Subjective Logic: A Formalism for Reasoning Under Uncertainty.* Springer.
- Spohn, W. (2012). *The Laws of Belief: Ranking Theory and Its Philosophical Applications.* Oxford.
- Jeffrey, R. (1983). *The Logic of Decision.* 2nd ed. Chicago.

### Secondary Sources

- Amgoud, L. & Ben-Naim, J. (2023). "Evaluation of Argument Strength in Attack Graphs." *Artificial Intelligence*.
- Baroni, P., Caminada, M., & Giacomin, M. (2011). "An introduction to argumentation semantics." *Knowledge Engineering Review*.
- [Stanford Encyclopedia: Defeasible Reasoning](https://plato.stanford.edu/entries/reasoning-defeasible/)

---

*Thread 2.10 Status: Core question substantially answered. Undercut uses multiplicative discounting; rebut uses probabilistic comparison. Ready for Lean 4 formalization. New questions raised about reinstatement and cyclic defeat.*
