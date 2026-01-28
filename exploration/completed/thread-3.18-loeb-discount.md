# Thread 3.18: Graded Löb Discount Function

> **Status**: Explored (Session 26)
> **Question**: What is the right discount function g(c) for the graded Löb axiom?
> **Priority**: HIGH — Determines how self-soundness claims cap confidence in CPL
> **Prior Threads**: Thread 3.13 (CPL design), Thread 3.16 (CPL decidability), Thread 8 (confidence operations)

---

## 1. The Problem

Thread 3.13 proposed the **Graded Löb Axiom** for CPL:

```
B_c(B_c φ → φ) → B_{g(c)} φ   where g(c) ≤ c
```

The function g(c) is the **discount function**—it determines how much confidence is preserved when deriving a belief from a self-soundness claim. The constraint g(c) ≤ c ensures **anti-bootstrapping**: you cannot gain confidence from claiming your own beliefs are sound.

**Core question:** What is the right choice for g(c)?

### 1.1 Candidates Identified in Thread 3.13

| Candidate | Formula | Properties |
|-----------|---------|------------|
| Identity | g(c) = c | No discount; preserves all confidence |
| Quadratic | g(c) = c² | Significant discount; steeper at high c |
| Parabolic | g(c) = c × (1-c) | Maximum discount at c = 0.5 |
| Constant offset | g(c) = c - ε | Constant discount; may go negative |
| Product | g(c) = c × d | Discount by fixed factor d < 1 |

### 1.2 Desiderata for g(c)

From the semantic intent of the Graded Löb axiom, g(c) should satisfy:

1. **Boundedness**: g : [0,1] → [0,1]
2. **Non-amplification**: g(c) ≤ c for all c ∈ [0,1]
3. **Monotonicity**: c₁ ≤ c₂ ⟹ g(c₁) ≤ g(c₂)
4. **Anchoring**: g(0) = 0 and g(1) = 1 (or g(1) < 1)
5. **Non-triviality**: g(c) > 0 for c > 0 (unless we want self-soundness to annihilate confidence)

**Semantic desiderata** (less formal):
- g should capture "claiming your own soundness cannot increase your epistemic position"
- g should reflect the epistemic cost of self-reference
- g should align with CLAIR's existing confidence operations

---

## 2. Prior Art Survey

### 2.1 Classical Löb's Theorem

Classical Löb's theorem is binary: □(□A → A) → □A. There is no "discounting"—the derivation either succeeds (confidence 1) or fails (confidence 0).

The graded version is genuinely novel (as established in Thread 3.13—there is no prior work on graded provability logic).

### 2.2 Subjective Logic Discounting

[Jøsang's Subjective Logic](https://www.auai.org/uai2016/tutorials_pres/subj_logic.pdf) has a **discounting operator** for trust propagation:

```
ω'_y = ω_t ⊗ ω_y
```

Where ω_t is the trust in the source and ω_y is the source's opinion. The belief component becomes:

```
b' = b_t × b_y
```

**Key insight:** Subjective Logic uses **multiplicative discounting**—the "trust" acts as a multiplier on the source's belief.

This suggests: **g(c) = c × d** where d is the "discount factor" for self-referential claims.

### 2.3 Löb-Safe Logics (Xue et al. 2024)

[Recent work on Löb-safe logics](https://arxiv.org/html/2408.09590) addresses self-reference in epistemic logic by:
- Removing positive introspection (Axiom 4)
- Using "Reasonable Belief" constraints

However, this work operates in classical modal logic—no graded/fuzzy extension. No discount function is proposed.

### 2.4 Fuzzy Modal Logic

Work on fuzzy modal logics ([van Benthem theorem for fuzzy logic](https://arxiv.org/pdf/1802.00478), etc.) uses graded accessibility relations:

```
V_w(□φ) = inf_{w'} max{1 - R(w,w'), V_{w'}(φ)}
```

The "1 - R(w,w')" term is a form of discounting by accessibility strength.

**Insight:** The complement (1 - x) appears naturally in fuzzy modal semantics.

### 2.5 Ranking Theory (Spohn)

[Spohn's ranking theory](https://link.springer.com/book/10.1007/978-94-007-0613-9) uses ordinal ranks (non-negative integers or infinity) rather than [0,1] values. Conditional ranks are computed via:

```
κ(A|B) = κ(A ∧ B) - κ(B)   if κ(B) < ∞
```

This is additive discounting in the ranking domain, which corresponds to **multiplicative** discounting in probability space (via the transformation x = exp(-κ)).

### 2.6 Summary of Prior Art

| Source | Discounting Style | Formula |
|--------|-------------------|---------|
| Subjective Logic | Multiplicative | b' = b_t × b |
| Fuzzy Modal | Complement-based | 1 - R(w,w') |
| Ranking Theory | Additive (ordinal) | κ - offset |
| None | Identity | c |

**No prior work directly addresses the graded Löb discount function.** We must reason from first principles and semantic desiderata.

---

## 3. Mathematical Analysis of Candidates

### 3.1 Candidate 1: Identity — g(c) = c

**Properties:**
- Boundedness: ✓ (trivially)
- Non-amplification: ✓ (g(c) = c ≤ c)
- Monotonicity: ✓
- g(0) = 0, g(1) = 1 ✓
- Non-triviality: ✓

**Semantic evaluation:**

This says: "If you believe at confidence c that your c-confidence beliefs are sound, you can derive φ at confidence c."

**Problem:** This is essentially no discount at all. It says self-soundness claims are cost-free. This seems to violate the spirit of Löb—the whole point is that self-soundness claims should not be a "free lunch."

**Verdict:** ✗ Too weak. Does not capture the epistemic cost of self-reference.

### 3.2 Candidate 2: Quadratic — g(c) = c²

**Properties:**
- Boundedness: ✓ (c ∈ [0,1] ⟹ c² ∈ [0,1])
- Non-amplification: ✓ (c² ≤ c for c ∈ [0,1])
- Monotonicity: ✓ (c² is increasing on [0,1])
- g(0) = 0, g(1) = 1 ✓
- Non-triviality: ✓

**Discount profile:**
```
c     g(c) = c²   discount = c - c²
0.1   0.01        0.09  (90% lost)
0.3   0.09        0.21  (70% lost)
0.5   0.25        0.25  (50% lost)
0.7   0.49        0.21  (30% lost)
0.9   0.81        0.09  (10% lost)
1.0   1.00        0.00  (0% lost)
```

**Semantic evaluation:**

This says: "Self-soundness claims are costly, especially at low confidence. At high confidence, the cost is minimal."

The discount c - c² = c(1-c) is the **parabolic** function—maximum at c = 0.5.

**Interpretation:** The most "dangerous" regime for self-reference is around 0.5 (maximal uncertainty). At very low c, you're already uncertain so the discount is small in absolute terms. At very high c, you're confident enough that the discount is also small.

**Alignment with CLAIR:** c² matches the multiplication operation (c × c). This could be interpreted as: "The derived confidence is the confidence squared—as if you need to justify both the claim AND the self-reference."

**Verdict:** ✓ Strong candidate. Principled semantics, matches CLAIR's multiplicative structure.

### 3.3 Candidate 3: Parabolic — g(c) = c × (1-c)

**Properties:**
- Boundedness: ✓ (c(1-c) ∈ [0, 0.25] ⊂ [0,1])
- Non-amplification: ✓ (c(1-c) ≤ c iff (1-c) ≤ 1, always true)
- Monotonicity: ✗ **FAILS**! c(1-c) is not monotonic—it increases to c=0.5 then decreases.
- g(0) = 0, g(1) = 0 ✗ (g(1) = 0, not 1)
- Non-triviality: ✓ for c ∈ (0,1)

**Monotonicity failure:**
```
c=0.3: g(0.3) = 0.21
c=0.5: g(0.5) = 0.25
c=0.7: g(0.7) = 0.21

0.3 < 0.7 but g(0.3) = g(0.7) — not strictly monotonic
```

**g(1) = 0 problem:**

If you have perfect confidence (c=1) in your own soundness, the derived belief has confidence 0! This seems backwards—perfect confidence in self-soundness should yield the strongest (not weakest) derived confidence.

**Verdict:** ✗ Fails monotonicity and anchoring. Mathematically unsuitable.

### 3.4 Candidate 4: Constant Offset — g(c) = c - ε

**Properties:**
- Boundedness: ✗ May go negative for c < ε
- Non-amplification: ✓ if ε > 0
- Monotonicity: ✓
- g(0) = -ε < 0 ✗
- Non-triviality: Depends on c

**Boundedness fix:** g(c) = max(0, c - ε)

With the fix:
- Boundedness: ✓
- Monotonicity: ✓
- g(0) = 0 ✓
- g(1) = 1 - ε < 1 (This is a choice—self-soundness never yields full confidence)

**Discount profile (ε = 0.1):**
```
c     g(c)    discount
0.0   0.0     0.0
0.1   0.0     0.1  (capped at 0)
0.3   0.2     0.1
0.5   0.4     0.1
0.7   0.6     0.1
0.9   0.8     0.1
1.0   0.9     0.1
```

**Semantic evaluation:**

This says: "Self-soundness claims have a fixed epistemic cost ε, regardless of initial confidence level."

**Problem:** The constant discount doesn't scale with uncertainty. Low-confidence self-soundness is penalized the same as high-confidence self-soundness (in absolute terms). This seems semantically wrong—surely the epistemic risk of self-reference depends on your confidence level?

**Verdict:** ⚠ Acceptable but not ideal. The constant discount is arbitrary and doesn't scale naturally.

### 3.5 Candidate 5: Product — g(c) = c × d (for fixed d ∈ (0,1))

**Properties:**
- Boundedness: ✓
- Non-amplification: ✓ (since d < 1)
- Monotonicity: ✓
- g(0) = 0 ✓
- g(1) = d < 1 (self-soundness never yields full confidence)
- Non-triviality: ✓

**Discount profile (d = 0.9):**
```
c     g(c)    discount (%)
0.1   0.09    10%
0.3   0.27    10%
0.5   0.45    10%
0.7   0.63    10%
0.9   0.81    10%
1.0   0.90    10%
```

**Semantic evaluation:**

This says: "Self-soundness claims discount confidence by a fixed percentage."

**Alignment with CLAIR:** This matches the **undercut** operation from Thread 2.10:
```
undercut(c, d) = c × (1 - d)
```

Where d is the defeat strength. If we set g(c) = c × (1 - ε) for small ε, this is exactly the undercut formula with ε being the "self-referential defeat strength."

**Interpretation:** Self-referential claims have a built-in "undercut" that weakens the inference. The undercut strength is a design parameter.

**Verdict:** ✓ Strong candidate. Aligns with CLAIR's undercut semantics, has natural interpretation.

### 3.6 Candidate 6: Self-Application — g(c) = c × c_claim

Where c_claim is the confidence in the self-soundness claim itself.

**Properties:**
- Not a fixed function of c alone—depends on the specific claim's confidence
- More fine-grained than fixed discount

**Semantic evaluation:**

In the Graded Löb axiom:
```
B_c(B_c φ → φ) → B_{g(c)} φ
```

The antecedent has confidence c (the confidence in "if I believe φ at c, then φ"). So c_claim = c.

This gives: g(c) = c × c = c² — which is **Candidate 2**!

**Verdict:** This interpretation supports the quadratic discount as the semantically natural choice.

---

## 4. Deeper Semantic Analysis

### 4.1 What Does the Graded Löb Axiom Mean?

Classical Löb says: If PA ⊢ (Prov(⌜φ⌝) → φ), then PA ⊢ φ.

The graded version: If you believe at confidence c that "my believing φ at c implies φ is true," then you can derive φ at confidence g(c).

**Key insight:** The discount function captures the epistemic gap between:
1. Believing something about your own believing
2. Actually believing the object-level claim

### 4.2 The Self-Reference Penalty

Self-reference is epistemically risky because:
1. **Circularity risk:** You're using your own reliability to justify your own reliability
2. **No external grounding:** Unlike ordinary derivation, there's no independent support
3. **Löbian trap proximity:** Self-validating beliefs are a slippery slope to paradox

The discount g(c) < c captures this risk. But how much?

### 4.3 Scaling with Confidence

Consider two cases:
- **Low confidence (c = 0.3):** You're uncertain about your own soundness. Self-referential derivation should be heavily penalized.
- **High confidence (c = 0.9):** You're quite confident in your soundness. Self-referential derivation is less risky but still not free.

This suggests the discount should be **proportional to uncertainty**:
```
penalty = f(1 - c)
```

For high c (low uncertainty), the penalty is small. For low c (high uncertainty), the penalty is large.

### 4.4 Derivation: The Natural Discount

If we want the penalty to be proportional to c (the risk of self-reference) AND to (1-c) (the residual uncertainty), we get:

```
discount = c × (1 - c)
```

And thus:

```
g(c) = c - discount = c - c(1-c) = c × c = c²
```

**This derivation strongly supports g(c) = c² as the natural choice.**

### 4.5 Alternative Derivation via Multiplication

In CLAIR, derivation combines confidence via multiplication:
```
conf(A ∧ B) = conf(A) × conf(B)
```

For the Graded Löb axiom:
```
B_c(B_c φ → φ)
```

The antecedent has two components:
1. The confidence c in the outer belief
2. The confidence c in the inner belief (since it's B_c φ)

If these combine multiplicatively: c × c = c².

**This confirms g(c) = c² from CLAIR's algebraic structure.**

---

## 5. The Recommended Choice: g(c) = c²

### 5.1 Summary of Analysis

| Criterion | g(c) = c | g(c) = c² | g(c) = c(1-c) | g(c) = c - ε | g(c) = c×d |
|-----------|----------|-----------|---------------|--------------|------------|
| Boundedness | ✓ | ✓ | ✓ | ⚠ | ✓ |
| Non-amplification | ✓ | ✓ | ✓ | ✓ | ✓ |
| Monotonicity | ✓ | ✓ | ✗ | ✓ | ✓ |
| Anchoring | ✓ | ✓ | ✗ | ⚠ | ⚠ |
| Non-triviality | ✓ | ✓ | ✓ | ✓ | ✓ |
| Captures self-ref cost | ✗ | ✓ | ✓ | ⚠ | ✓ |
| Aligns with CLAIR ops | ✗ | ✓ | ⚠ | ✗ | ✓ |
| Natural derivation | ✗ | ✓ | ✗ | ✗ | ⚠ |

**Winner: g(c) = c²**

### 5.2 Properties of g(c) = c²

**Mathematical:**
- g : [0,1] → [0,1]
- g(0) = 0, g(1) = 1
- g is strictly increasing: g'(c) = 2c > 0 for c > 0
- g is convex: g''(c) = 2 > 0
- g(c) ≤ c with equality only at c = 0, 1

**Semantic:**
- Self-soundness claims preserve confidence non-linearly
- Low-confidence self-soundness is heavily penalized (0.3 → 0.09)
- High-confidence self-soundness is mildly penalized (0.9 → 0.81)
- Perfect confidence is preserved (1 → 1)
- No confidence yields no confidence (0 → 0)

**Algebraic:**
- Matches CLAIR's multiplicative combination: c² = c × c
- Can be written as: g(c) = c × c (self-application)
- Commutes with multiplication: (a × b)² = a² × b²
- Forms a monoid homomorphism from ([0,1], ×, 1) to itself

### 5.3 The Anti-Bootstrapping Theorem (Revisited)

With g(c) = c²:

**Theorem:** If conf(B(Bφ → φ)) = c, then conf(Bφ) ≤ c².

**Corollary:** For c < 1, repeated self-soundness claims diminish confidence:
```
c → c² → c⁴ → c⁸ → ... → 0
```

**Interpretation:** You cannot bootstrap to certainty via self-soundness claims. Each layer of self-reference costs a multiplicative penalty.

**Example:** Starting with c = 0.9:
- After 1 self-soundness claim: 0.81
- After 2: 0.6561
- After 3: 0.4305
- After 4: 0.1853
- ...
- Limit: 0

---

## 6. Alternative: The Product Discount g(c) = c × d

While c² is the recommended primary choice, the product discount g(c) = c × d has merits for practical use:

### 6.1 When to Use Product Discount

If CLAIR wants a **tunable** discount rather than a fixed mathematical formula:
- d = 0.9: Mild penalty (10% confidence loss)
- d = 0.7: Moderate penalty (30% confidence loss)
- d = 0.5: Severe penalty (50% confidence loss)

### 6.2 Relationship to c²

The product discount g(c) = c × d is equivalent to c² when d = c.

More generally:
- c² is a **variable** discount (d = c)
- c × d is a **fixed** discount (d is constant)

For most applications, c² is more principled. The product discount is useful when:
- The self-reference penalty should be uniform across confidence levels
- The system needs to tune the penalty empirically

### 6.3 Connection to Undercut

The product discount aligns exactly with CLAIR's undercut operation:
```
undercut(c, strength) = c × (1 - strength)
```

With g(c) = c × d, we have d = 1 - strength, so:
```
g(c) = undercut(c, 1 - d)
```

**Interpretation:** Self-soundness claims have an inherent undercut with strength (1 - d).

For c² = c × c, this would require dynamic undercut strength = 1 - c.

---

## 7. Formalization in Lean 4

Building on Thread 8's confidence type:

```lean4
namespace Confidence

/-- The graded Löb discount function: g(c) = c² -/
def loeb_discount (c : Confidence) : Confidence :=
  c * c

/-- Alternative: fixed product discount g(c) = c × d -/
def product_discount (d : Confidence) (c : Confidence) : Confidence :=
  c * d

-- Key theorems

/-- Löb discount preserves bounds -/
theorem loeb_discount_bounded (c : Confidence) :
    0 ≤ (loeb_discount c).val ∧ (loeb_discount c).val ≤ 1 :=
  (loeb_discount c).property

/-- Löb discount is non-amplifying: g(c) ≤ c -/
theorem loeb_discount_le (c : Confidence) :
    (loeb_discount c).val ≤ c.val := by
  unfold loeb_discount
  simp only [HMul.hMul, Mul.mul]
  have h1 : c.val ≤ 1 := c.property.2
  have h2 : c.val ≥ 0 := c.property.1
  nlinarith

/-- Löb discount is monotonic -/
theorem loeb_discount_mono {c₁ c₂ : Confidence} (h : c₁.val ≤ c₂.val) :
    (loeb_discount c₁).val ≤ (loeb_discount c₂).val := by
  unfold loeb_discount
  simp only [HMul.hMul, Mul.mul]
  have h1 : c₁.val ≥ 0 := c₁.property.1
  have h2 : c₂.val ≥ 0 := c₂.property.1
  nlinarith

/-- Löb discount fixed points are 0 and 1 -/
theorem loeb_discount_fixed_points (c : Confidence) :
    loeb_discount c = c ↔ c.val = 0 ∨ c.val = 1 := by
  unfold loeb_discount
  constructor
  · intro h
    have heq : c.val * c.val = c.val := by
      have := congrArg Subtype.val h
      simpa using this
    -- c² = c ⟺ c(c-1) = 0 ⟺ c = 0 or c = 1
    nlinarith [c.property.1, c.property.2]
  · intro h
    cases h with
    | inl hz => simp [hz]; ext; simp [Zero.zero, hz]
    | inr ho => simp [ho]; ext; simp [One.one, ho]

/-- Anti-bootstrapping: iterated Löb discount converges to 0 for c < 1 -/
theorem loeb_discount_iter_limit {c : Confidence} (hc : c.val < 1) :
    ∀ ε > 0, ∃ n : ℕ, (loeb_discount^[n] c).val < ε := by
  -- c^(2^n) → 0 as n → ∞ for c < 1
  sorry -- requires analysis of geometric decay

end Confidence
```

---

## 8. Integration with CPL

### 8.1 The Graded Löb Axiom (Final Form)

With g(c) = c²:

```
B_c(B_c φ → φ) → B_{c²} φ
```

**Reading:** "If you believe at confidence c that your c-beliefs are sound, you can believe φ at confidence c²."

### 8.2 Anti-Bootstrapping Constraint

The confidence in any belief derived via self-soundness claims is bounded:

```
conf(φ) ≤ conf(self-soundness)²
```

For CLAIR, this means:
- No belief should have confidence > 0.9² = 0.81 if it depends on self-soundness
- Recursive self-soundness rapidly degrades: 0.9 → 0.81 → 0.66 → 0.43 → ...

### 8.3 Implementation in CLAIR Type System

From Thread 3.13's proposal:

```clair
-- Type-level constraint: self-soundness claims cap confidence
type SelfSoundnessGuard<c : Confidence> =
  Guard (all_derived_confidences ≤ c²)

-- Compile-time detection of Löbian claims
let trap = belief(
  value: "all my 0.9-confidence beliefs are true",
  confidence: 0.9
)
-- Warning: Derived confidences capped at 0.81

-- Runtime confidence ceiling
let ceiling : Confidence = estimate_self_soundness()
-- All beliefs: confidence ≤ ceiling²
```

### 8.4 Decidability Implications

From Thread 3.16: Full CPL is likely undecidable, but decidable fragments exist.

The quadratic discount g(c) = c² doesn't affect decidability—the undecidability comes from transitivity + continuous values, not from the specific discount function.

For **CPL-finite** (discrete confidence values), the discount function is simply applied pointwise:

```
Values: {0, 0.25, 0.5, 0.75, 1.0}
Discounts: {0, 0.0625, 0.25, 0.5625, 1.0}
```

Note: 0.5² = 0.25 stays in the set, but 0.75² = 0.5625 doesn't. This might require rounding or extending the value set.

---

## 9. Open Questions

### 9.1 Should g(1) = 1?

The quadratic discount has g(1) = 1: perfect confidence in self-soundness yields perfect confidence in derived beliefs.

**Alternative view:** Perhaps even perfect confidence should be discounted slightly:
```
g(c) = c² × (1 - ε)
```

This would express: "Even with full confidence in self-soundness, you can never achieve full confidence in derived beliefs."

**My view:** The current g(c) = c² is fine. If c = 1 represents "certain," then g(1) = 1 is appropriate. The issue is that no belief should have c = 1 in the first place (Thread 4: honest uncertainty).

### 9.2 Higher-Order Self-Reference

What about beliefs about beliefs about beliefs?

```
B_c(B_c(B_c φ → φ) → (B_c φ → φ)) → B_{???} φ
```

With g(c) = c², this would yield c⁴ (applying the discount twice). Is this the right semantics?

**Tentative answer:** Yes. Each level of self-reference applies the discount multiplicatively. This matches the iterative convergence to 0.

### 9.3 Context-Dependent Discount

Should the discount depend on the proposition φ?

For example:
- Mathematical claims: mild discount (g(c) = c × 0.95)
- Empirical claims: moderate discount (g(c) = c²)
- Self-referential claims: severe discount (g(c) = c³)

**My view:** The uniform g(c) = c² is simpler and more principled. Context-dependence adds complexity without clear benefit.

---

## 10. Summary: What This Exploration Establishes

### 10.1 Key Finding

**The recommended discount function is g(c) = c² (quadratic).**

This is supported by:
1. **Mathematical properties:** Bounded, monotonic, anchored at 0 and 1
2. **Semantic derivation:** Penalty proportional to c(1-c), yielding c - c(1-c) = c²
3. **Algebraic alignment:** Matches CLAIR's multiplicative combination (c × c)
4. **Anti-bootstrapping:** Iterated application converges to 0 for c < 1

### 10.2 Alternative

For systems requiring tunable discount, **g(c) = c × d** (product discount) is acceptable. This aligns with CLAIR's undercut operation and allows empirical adjustment of the self-reference penalty.

### 10.3 Formalization Ready

The discount function is simple to formalize in Lean 4:
```lean4
def loeb_discount (c : Confidence) : Confidence := c * c
```

Key theorems (boundedness, monotonicity, fixed points) are straightforward.

### 10.4 Integration with CPL

The graded Löb axiom with g(c) = c²:
```
B_c(B_c φ → φ) → B_{c²} φ
```

Captures the anti-bootstrapping essence: self-soundness claims cannot increase confidence, and repeated self-reference rapidly degrades confidence toward 0.

---

## 11. Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| g(c) = c² is mathematically suitable | 0.95 | All desiderata satisfied |
| g(c) = c² captures anti-bootstrapping semantics | 0.85 | Derivation from first principles |
| g(c) = c² aligns with CLAIR operations | 0.90 | Matches multiplicative structure |
| Alternative g(c) = c×d is also acceptable | 0.80 | Different trade-offs, also principled |
| g(c) = c(1-c) is unsuitable | 0.95 | Monotonicity failure is disqualifying |
| g(c) = c is unsuitable | 0.85 | Fails to capture self-reference cost |
| Task 3.18 is substantially answered | 0.90 | Clear recommendation with justification |

---

## 12. References

### Sources Consulted

- [Wikipedia: Löb's theorem](https://en.wikipedia.org/wiki/L%C3%B6b's_theorem) — Classical foundations
- [Jøsang (2016), Subjective Logic tutorial](https://www.auai.org/uai2016/tutorials_pres/subj_logic.pdf) — Discounting operator
- [arXiv:2408.09590, Löb-Safe Logics for Reflective Agents](https://arxiv.org/html/2408.09590) — Modern approaches to Löb's obstacle
- [Stanford Encyclopedia: Provability Logic](https://plato.stanford.edu/entries/logic-provability/) — GL foundations
- [arXiv:1802.00478, A van Benthem Theorem for Fuzzy Modal Logic](https://arxiv.org/pdf/1802.00478) — Fuzzy modal semantics

### CLAIR Internal References

- exploration/thread-3.13-graded-provability-logic.md — CPL design
- exploration/thread-3.16-cpl-decidability.md — CPL decidability analysis
- exploration/thread-8-verification.md — Confidence operations
- exploration/thread-2.10-defeat-confidence.md — Undercut formula

---

*Thread 3.18 Status: Substantially explored. Recommended g(c) = c². Formalization ready.*
