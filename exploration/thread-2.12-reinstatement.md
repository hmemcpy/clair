# Thread 2.12: Reinstatement in Defeasible Reasoning

> **Status**: Substantially explored (Session 18)
> **Task**: 2.12 What happens when a defeater is itself defeated?
> **Question**: How should CLAIR handle reinstatement—the recovery of belief confidence when a defeater is countered?
> **Priority**: HIGH — Connects Thread 2.10 (defeat propagation) with practical reasoning chains

---

## 1. The Problem

Thread 2.10 established how defeat affects confidence:
- **Undercut**: c' = c × (1 - d) (multiplicative discounting)
- **Rebut**: c' = c_for / (c_for + c_against) (probabilistic comparison)

But real reasoning involves **chains of defeat**:

```
Belief A (confidence 0.9)
    ↑ undercut by
Defeater D (confidence 0.8)
    ↑ undercut by
Counter-defeater E (confidence 0.7)
```

When E defeats D, does A's confidence get **reinstated**? If so, how much?

This is the classic "reinstatement problem" in defeasible reasoning, now applied to CLAIR's graded confidence system.

---

## 2. Prior Art Survey

### 2.1 Binary Reinstatement (Dung 1995)

Dung's [abstract argumentation framework](https://en.wikipedia.org/wiki/Argumentation_framework) treats reinstatement as binary:

> "A set Args **defends** an argument A iff all of A's attackers are attacked by Args."

In the **grounded extension** (most skeptical semantics):
- Unattacked arguments are IN
- Arguments attacked by IN arguments are OUT
- Arguments defended by IN arguments (attackers are OUT) are reinstated to IN

**Key concept**: An argument is reinstated when all its defeaters are defeated. This is all-or-nothing.

### 2.2 Pollock's Defeasible Reasoning (1987, 2001)

John Pollock distinguished [rebutting vs undercutting defeat](https://plato.stanford.edu/entries/reasoning-defeasible/):

> "A conclusion is warranted, given all of one's evidence, if it is supported by an ultimately undefeated argument."
>
> "An argument is reinstated when all its defeaters are in turn ultimately defeated."

Pollock later explored **variable degrees of justification** (2001), where argument strength is computed through the reasoning chain. However, his exact propagation rules are complex and context-dependent.

### 2.3 ASPIC+ Framework (Prakken 2010)

The [ASPIC+ framework](https://journals.sagepub.com/doi/10.1080/19462166.2013.869766) for structured argumentation:

> "An argument A is defended by a set S if for all B: if B defeats A, then some C in S defeats B."

This defense mechanism grounds reinstatement—a defeated argument can be "reinstated" if its defeater is itself defeated by something in the acceptable set.

### 2.4 Gradual/Weighted Semantics (Amgoud et al.)

Recent work on [weighted bipolar argumentation](https://www.ijcai.org/proceedings/2018/0720.pdf) introduces numerical strength:

**h-categorizer semantics** (Besnard & Hunter):
```
strength(a) = w(a) / (1 + Σ_{b attacks a} strength(b))
```

The denominator accumulates attacker strengths, naturally implementing gradual weakening rather than binary defeat.

### 2.5 TMS Restoration (Doyle 1979)

Truth Maintenance Systems handle reinstatement through [dependency-directed backtracking](https://en.wikipedia.org/wiki/Reason_maintenance):

> "When a contradiction is found, the statement(s) responsible for the contradiction are identified and the records are appropriately updated."

TMS restores beliefs when their defeating justifications lose support. This is binary (IN/OUT) but the mechanism of tracking dependencies and recomputing on change is what CLAIR generalizes.

### 2.6 Floating Conclusions (Horty)

[John Horty's work on floating conclusions](http://www.horty.umiacs.io/articles/2001-floating.pdf) raises a subtle issue:

> "The phenomenon of floating conclusions indicates a problem with the view that the skeptical consequences of such theories should be identified with the statements that are supported by each of their various extensions."

A **floating conclusion** is derivable via multiple conflicting arguments. This matters when defeaters form complex webs rather than simple chains.

### 2.7 The Nixon Diamond

The classic example of conflicting defaults:
- Nixon is a Quaker → (defeasibly) Nixon is a pacifist
- Nixon is a Republican → (defeasibly) Nixon is not a pacifist

In extension-based semantics, this yields two preferred extensions (one where he's a pacifist, one where he's not). Skeptical reasoning draws no conclusion.

**CLAIR's approach**: With graded confidence, both lines contribute. If Quaker→pacifist has strength 0.7 and Republican→¬pacifist has strength 0.6, rebut comparison gives 0.7/(0.7+0.6) ≈ 0.54 confidence in pacifism.

---

## 3. Key Insight: Reinstatement is Compositional

**The central discovery of this exploration:**

> CLAIR doesn't need a separate reinstatement mechanism. Reinstatement **emerges naturally** from compositional bottom-up confidence propagation.

### 3.1 The Compositional Principle

When evaluating A's confidence in a chain A ← D ← E:

1. First compute D's *effective* confidence after its own defeaters: D_eff = D × (1 - E)
2. Then apply D's effective strength to A: A_final = A × (1 - D_eff)

Substituting:
```
A_final = A_base × (1 - D_base × (1 - E_base))
```

### 3.2 Worked Example

Given: A_base = 0.9, D_base = 0.8, E_base = 0.7

**Without counter-defeater E:**
```
A = 0.9 × (1 - 0.8) = 0.18
```

**With counter-defeater E:**
```
D_effective = 0.8 × (1 - 0.7) = 0.24
A_final = 0.9 × (1 - 0.24) = 0.684
```

The **reinstatement boost** is:
```
0.684 - 0.18 = 0.504
```

### 3.3 The Reinstatement Formula

**Theorem (Reinstatement Boost):**
```
reinstatement_boost(A, D, E) = A_base × D_base × E_base
```

The boost is the product of all three confidences. This makes intuitive sense:
- Strong original belief (high A) → more to recover
- Strong original defeater (high D) → more was lost
- Strong counter-defeater (high E) → more is recovered

**Verification**: 0.9 × 0.8 × 0.7 = 0.504 ✓

---

## 4. Chains of Arbitrary Length

### 4.1 Three-Level Chain

For A ← D₁ ← D₂ ← D₃:

```
D₂_effective = D₂ × (1 - D₃)
D₁_effective = D₁ × (1 - D₂_effective)
A_final = A × (1 - D₁_effective)
```

With A=0.9, D₁=0.8, D₂=0.7, D₃=0.6:
```
D₂_eff = 0.7 × 0.4 = 0.28
D₁_eff = 0.8 × 0.72 = 0.576
A_final = 0.9 × 0.424 = 0.3816
```

### 4.2 The Oscillation Property

In chains of undercuts:
- **Odd positions** (D₁, D₃, D₅...) attack A (reduce confidence)
- **Even positions** (D₂, D₄, D₆...) defend A (increase confidence)

This matches Dung's notion of "odd attack paths" vs "even attack paths."

### 4.3 Convergence for Infinite Chains

**Theorem (Defeat Chain Convergence):**

For an infinite chain of undercuts with constant strength d, the effective defeat strength converges to:
```
x* = d / (1 + d)
```

**Proof sketch:**
Let x be the effective strength. By self-similarity:
```
x = d × (1 - x)
x = d - dx
x(1 + d) = d
x = d/(1 + d)
```

For d = 0.5: x* = 1/3 ≈ 0.333

**Numerical verification:**
- f¹(0.5) = 0.25
- f²(0.5) = 0.375
- f³(0.5) = 0.3125
- f⁴(0.5) = 0.34375
- ...
- Converges to 0.333... ✓

---

## 5. Multiple Defeaters

### 5.1 Independent Defeaters

When A has multiple unrelated defeaters D₁, D₂:

From Thread 2.10, aggregate using ⊕:
```
D_combined = D₁ ⊕ D₂ = D₁ + D₂ - D₁ × D₂
A_final = A × (1 - D_combined)
```

### 5.2 Each Defeater Has Its Own Counter

If D₁ is countered by E₁ and D₂ is countered by E₂:
```
D₁_effective = D₁ × (1 - E₁)
D₂_effective = D₂ × (1 - E₂)
D_combined_effective = D₁_effective ⊕ D₂_effective
A_final = A × (1 - D_combined_effective)
```

This correctly handles independent lines of attack and defense.

---

## 6. Rebut Reinstatement

### 6.1 Weakening a Counter-Argument

When A faces a rebutting defeater R, and C attacks R:

```
Without C:
  result = A_for / (A_for + R)

With C undercutting R:
  R_effective = R × (1 - C)
  result = A_for / (A_for + R_effective)
```

### 6.2 Worked Example

A_for = 0.6, R = 0.7, C = 0.8

**Without defense:**
```
0.6 / (0.6 + 0.7) = 0.462
```

**With defense:**
```
R_eff = 0.7 × 0.2 = 0.14
0.6 / (0.6 + 0.14) = 0.811
```

Significant reinstatement! The argument for A is strengthened by weakening the counter-argument.

---

## 7. Mutual Defeat (Cycles in Defeat Graph)

### 7.1 The Problem

What if A undercuts B and B undercuts A?

Note: This is a cycle in the **defeat relation**, not the justification DAG. Thread 2 forbids justification cycles, but defeat cycles require separate analysis.

### 7.2 Fixed-Point Solution

For mutual undercut:
```
A = A_base × (1 - B)
B = B_base × (1 - A)
```

Solving:
```
A = A_base × (1 - B_base × (1 - A))
A(1 - A_base × B_base) = A_base × (1 - B_base)
A* = A_base × (1 - B_base) / (1 - A_base × B_base)
```

### 7.3 Examples

**Symmetric case** (A_base = B_base = d):
```
A* = d(1-d) / (1-d²) = d / (1+d)
```

Same formula as infinite chains! Mutual attack is like infinite alternation.

**Asymmetric case** (A_base = 0.8, B_base = 0.6):
```
A* = 0.8 × 0.4 / (1 - 0.48) = 0.32 / 0.52 ≈ 0.615
B* = 0.6 × 0.2 / (1 - 0.48) = 0.12 / 0.52 ≈ 0.231
```

The stronger original argument wins after stabilization.

### 7.4 Convergence Guarantee

**Theorem (Mutual Defeat Convergence):**

The fixed-point iteration for mutual undercuts converges for all A_base, B_base < 1.

**Proof sketch:**
The function f(x) = c × (1 - d × (1 - x)) is a contraction mapping on [0,1]:
- |f'(x)| = c × d < 1 when c, d < 1

By Banach fixed-point theorem, iteration converges to unique fixed point.

---

## 8. The Evaluation Algorithm

The belief revision algorithm from Thread 5 already handles reinstatement naturally:

```python
def evaluate_confidence(node, graph, memo={}):
    """Evaluate confidence with memoization."""
    if node in memo:
        return memo[node]

    if node.is_axiom:
        return node.base_confidence

    # Recursively evaluate dependencies first
    # This ensures attackers' effective strength reflects their own attackers

    # 1. Combine supports
    c = combine_supports([
        evaluate_confidence(s, graph, memo)
        for s in node.supporters
    ])

    # 2. Apply undercuts (using effective, not base, strengths)
    for undercut_node in node.undercuts:
        undercut_strength = evaluate_confidence(undercut_node, graph, memo)
        c = c * (1 - undercut_strength)

    # 3. Apply rebuts (using effective strengths)
    if node.rebuts:
        c_against = aggregate_rebuts([
            evaluate_confidence(r, graph, memo)
            for r in node.rebuts
        ])
        c = c / (c + c_against) if (c + c_against) > 0 else 0.5

    memo[node] = c
    return c
```

**Key insight**: By evaluating recursively bottom-up, when we use an attacker's confidence, it already reflects any counter-attacks. Reinstatement emerges automatically.

---

## 9. Comparison with Prior Art

| Approach | Reinstatement | Gradual? | Compositional? | CLAIR Match |
|----------|---------------|----------|----------------|-------------|
| Dung (grounded) | Binary: reinstated if all attackers defeated | No | No | Conceptual ancestor |
| Dung (preferred) | Extension-relative | No | No | Different paradigm |
| ASPIC+ | Via defense | No | Partially | Good structural match |
| h-categorizer | Via denominator accumulation | Yes | Yes | Similar spirit |
| TMS (JTMS) | On justification change | No | Yes | CLAIR generalizes |
| **CLAIR** | Via bottom-up propagation | Yes | Yes | Native |

---

## 10. Implications for CLAIR Design

### 10.1 No Special Mechanism Needed

The key finding: CLAIR's existing architecture handles reinstatement without modification.

Required components (all already designed):
1. DAG structure with labeled edges (Thread 2)
2. Undercut operation: c × (1 - d) (Thread 2.10)
3. Rebut operation: c_for / (c_for + c_against) (Thread 2.10)
4. Bottom-up evaluation with memoization (Thread 5)

### 10.2 Defeat Cycles Are Supported

Unlike justification cycles (which are forbidden), defeat cycles have well-defined fixed-point semantics. The system can compute stable confidence values even with mutual defeat.

### 10.3 Complexity Considerations

**Time**: O(V + E) for single evaluation with memoization (topological order)
**Space**: O(V) for memoization
**Incremental updates**: Only recompute affected subgraph (locality theorem from Thread 5)

---

## 11. Open Questions Remaining

### 11.1 Higher-Order Defeat

What if an argument attacks the *edge* between two other arguments, rather than an argument itself?

Example: "The inference from A to B is invalid" attacks the support edge, not A or B.

This may require extending the edge semantics.

### 11.2 Temporal Dynamics

If new information arrives that defeats a defeater, should the reinstated belief have exactly the same confidence as before, or is there hysteresis?

Current answer: Yes, same confidence (deterministic evaluation). But an alternative with "belief momentum" might model psychological realism.

### 11.3 Correlated Counter-Defeaters

If E₁ and E₂ both defend A by attacking D, and E₁ and E₂ are correlated (not independent), how should their combined defense be computed?

This connects to Task 2.13 (correlated evidence).

---

## 12. Formalization Status

### 12.1 Ready for Lean 4

**Fixed-point equation for mutual undercut:**
```lean
theorem mutual_undercut_fixed_point (a b : Confidence) (h : a.val * b.val < 1) :
    let a' := a.val * (1 - b.val) / (1 - a.val * b.val)
    let b' := b.val * (1 - a.val) / (1 - a.val * b.val)
    a' = a.val * (1 - b') ∧ b' = b.val * (1 - a') := by
  sorry  -- Algebraic verification
```

**Reinstatement boost formula:**
```lean
theorem reinstatement_boost (a d e : Confidence) :
    let without_e := a.val * (1 - d.val)
    let with_e := a.val * (1 - d.val * (1 - e.val))
    with_e - without_e = a.val * d.val * e.val := by
  ring
```

**Convergence of infinite chains:**
```lean
theorem chain_limit (d : Confidence) (hd : d.val < 1) :
    let limit := d.val / (1 + d.val)
    -- Sequence converges to limit
    sorry
```

### 12.2 Not Yet Ready

- General n-ary defeat cycle fixed points
- Incremental update complexity proofs
- Connection to gradual argumentation semantics literature

---

## 13. Conclusions

### 13.1 Core Answer

**What happens when a defeater is itself defeated?**

The original belief is **partially reinstated** according to the compositional formula:
```
A_final = A_base × (1 - D_effective)
where D_effective = D_base × (1 - E_base)
```

The reinstatement boost is exactly A_base × D_base × E_base.

### 13.2 Key Insights

1. **Reinstatement is compositional** — No special mechanism needed; it emerges from bottom-up propagation
2. **Gradual, not binary** — Partial reinstatement proportional to counter-defeater strength
3. **Chains converge** — Infinite alternating defeat converges to d/(1+d)
4. **Cycles have fixed points** — Mutual defeat is well-defined
5. **Prior art alignment** — Matches Dung defense concept, generalizes TMS, extends to gradual semantics

### 13.3 Impact on Other Threads

- **Thread 5**: Belief revision algorithm already handles reinstatement
- **Thread 8**: New theorems ready for Lean formalization
- **Task 2.13**: Correlated counter-defeaters need further work

---

## 14. References

### Primary Sources

- Dung, P.M. (1995). "On the acceptability of arguments." *Artificial Intelligence*, 77, 321-357.
- Pollock, J. (1987). "Defeasible Reasoning." *Cognitive Science*, 11(4), 481-518.
- Pollock, J. (2001). "Defeasible Reasoning with Variable Degrees of Justification." *Artificial Intelligence*, 133, 233-282.
- Prakken, H. (2010). "An abstract framework for argumentation with structured arguments." *Argument and Computation*, 1:93–124.
- Doyle, J. (1979). "A Truth Maintenance System." *Artificial Intelligence*, 12(3), 231-272.

### Secondary Sources

- Horty, J. (2001). "Argument construction and reinstatement in logics for defeasible reasoning." *Artificial Intelligence and Law*.
- Amgoud, L. & Ben-Naim, J. (2018). "Weighted Bipolar Argumentation Graphs: Axioms and Semantics." *IJCAI Proceedings*.
- Caminada, M. (2006). "On the issue of reinstatement in argumentation." *JELIA*.
- Besnard, P. & Hunter, A. (2001). "A logic-based theory of deductive arguments." *Artificial Intelligence*, 128, 203-235.

### Online Resources

- [Stanford Encyclopedia: Defeasible Reasoning](https://plato.stanford.edu/entries/reasoning-defeasible/)
- [Stanford Encyclopedia: Non-monotonic Logic](https://plato.stanford.edu/entries/logic-nonmonotonic/)
- [Wikipedia: Argumentation Framework](https://en.wikipedia.org/wiki/Argumentation_framework)

---

*Thread 2.12 Status: Substantially explored. Reinstatement emerges compositionally from bottom-up evaluation. Mathematical properties characterized. Ready for Lean formalization. New questions about correlated counter-defeaters and temporal dynamics identified.*
