# D4: Confidence Algebra in Practice

## Research Question

The confidence algebra (×, ⊕, undercut, rebut, min) is fully proven in Lean with 40+ theorems. But do these operations actually model how confidence should behave in real CLAIR traces? This exploration tests whether the algebra produces **intuitive results** when applied to concrete reasoning scenarios.

**Thesis Connection:** If the algebra produces counterintuitive results in practice, CLAIR's confidence mechanism becomes a liability — Assemblers might misinterpret signals or Thinkers might assign values that don't behave as expected. This directly tests whether the formal foundation connects to practical IR viability.

**Validation Criteria:**
- Test each operation (×, ⊕, undercut, rebut, min) against ≥2 real trace scenarios
- Document counterintuitive results and their practical impact
- Map each Lean theorem to its IR-model implication
- Identify whether issues are fundamental (algebra is wrong) or operational (misuse)
- Connection to thesis (supports, undermines, or refines)

---

## Background: The Lean Algebra

### Operations Defined

| Operation | Formula | Interpretation | Lean File |
|-----------|---------|----------------|-----------|
| **×** (mul) | `a × b` | Derivation: confidence decreases when reasoning extends | `Basic.lean` |
| **⊕** (oplus) | `a + b - ab` | Aggregation: independent evidence combined | `Oplus.lean` |
| **undercut** | `c × (1-d)` | Defeat: attack on inferential link | `Undercut.lean` |
| **rebut** | `c_for / (c_for + c_against)` | Rebuttal: competing evidence comparison | `Rebut.lean` |
| **min** | `if a ≤ b then a else b` | Conservative: weakest link | `Min.lean` |

### Key Theorems (Proven)

From `formal/lean/CLAIR/Confidence/`:

1. **Derivation decreases confidence:** `mul_le_left`, `mul_le_right`
2. **Aggregation is order-independent:** `oplus_comm`, `oplus_assoc`
3. **Non-distributivity:** `mul_oplus_not_distrib` (a=b=c=0.5 is counterexample)
4. **Sequential defeat composes:** `undercut_compose` (undercut(undercut(c,d₁),d₂) = undercut(c,d₁⊕d₂))
5. **Equal evidence balances:** `rebut_eq` (rebut(c,c) = 0.5)
6. **Min ≥ multiplication:** `mul_le_min` (min is more optimistic)

---

## Test 1: Multiplication (×) — Derivation Chains

### Scenario: Algorithm Selection from A1

**Trace (simplified):**
```clair
b2 .95 L0 @self <b1 "input: array of integers (unspecified size)"
b7 .6 L0 @self <b2 "merge sort: O(n log n), stable, needs extra space"
b12 .7 L0 @self <b7 "for general purpose: implement merge sort"
```

### Algebra Check

**Question:** If b7 is justified by b2, and b12 is justified by b7, what should their confidences be?

**Per the algebra (multiplicative derivation):**
```
conf(b7) ≤ conf(b2) × confidence_of_inference
conf(b12) ≤ conf(b7) × confidence_of_inference
```

**Actual trace:**
- `conf(b2) = 0.95`
- `conf(b7) = 0.6` (should be ≤ 0.95 × something)
- `conf(b12) = 0.7` (should be ≤ 0.6 × something)

**Problem:** `conf(b12) = 0.7 > conf(b7) = 0.6` — **confidence increased through derivation!**

This violates `mul_le_left`: derivation can only decrease confidence.

### Analysis

**What happened?** The trace author intuited "merge sort is the best choice" (0.7) without considering that b12's confidence is bounded by b7's confidence.

**Correct application:**
```
conf(b7) = 0.6 (given)
conf(b12) ≤ 0.6 × (confidence that b7 → b12)
conf(b12) ≤ 0.6 × 0.9 = 0.54  (if inference is 0.9 strong)
```

But the trace has `conf(b12) = 0.7`, which is **impossible** under the algebra.

### Counter-Example: Overly Long Derivation Chains

**Trace:**
```clair
b1 1.0 L0 @user "sort an array"
b2 .95 L0 @self <b1 "need sorting algorithm"
b3 .9 L0 @self <b2 "consider merge sort"
b4 .85 L0 @self <b3 "merge sort is O(n log n)"
b5 .8 L0 @self <b4 "O(n log n) is efficient"
b6 .75 L0 @self <b5 "therefore use merge sort"
```

**Algebra check:**
```
conf(b6) ≤ conf(b5) × ...
         ≤ conf(b4) × ... × ...
         ≤ conf(b3) × ... × ... × ...
         ≤ conf(b2) × ... × ... × ... × ...
         ≤ conf(b1) × ... × ... × ... × ... × ...
```

**Result:** Even if each step has 0.95 inference confidence:
```
conf(b6) ≤ 1.0 × 0.95^5 ≈ 0.77
```

But if any step is weaker (say 0.8), confidence collapses:
```
conf(b6) ≤ 1.0 × 0.95^4 × 0.8 ≈ 0.65
```

**Practical implication:** **Long derivation chains destroy confidence.**

A 10-step chain with 0.9 inference confidence per step:
```
conf(final) ≤ 0.9^10 ≈ 0.35
```

The conclusion is "barely more confident than maximal uncertainty (0.5)!"

### Verdict

**Does `0.9 × 0.8 = 0.72` represent how confidence should propagate?**

✅ **YES** for objective, error-prone reasoning:
- Each step might be wrong
- Errors compound
- Long chains should be viewed skeptically

❌ **NO** for mathematical deduction:
- Mathematical steps are certain (if they follow)
- 0.95 × 0.95 × ... misrepresents mathematical certainty
- This is A4's finding: mathematical reasoning should use 1.0 for deductive steps

**Thesis Impact:** **REFINES** — The algebra is correct for **fallible reasoning** but hand-authored traces often violate it. Thinkers need training:
1. Don't let confidence increase through derivation
2. Be aware of chain-length penalty
3. Use 1.0 for axioms and deductive certainty

---

## Test 2: Oplus (⊕) — Independent Evidence Aggregation

### Scenario: Multiple Bug Diagnoses

**Trace (modified from A1):**
```clair
; Two independent sources suggest the same bug
b13 .2 L0 @self <b1 "result variable is None"
b13b .7 L0 @self <b1 "missing return statement (most likely)"
b13c .6 L0 @self <b1 "missing return statement (alternative phrasing)"
```

**Question:** If we have two independent beliefs about the same conclusion ("missing return"), how should they combine?

### Algebra Check

**Using oplus:**
```
conf(missing return) = conf(b13b) ⊕ conf(b13c)
                     = 0.6 ⊕ 0.7
                     = 0.6 + 0.7 - 0.6×0.7
                     = 1.3 - 0.42
                     = 0.88
```

**Intuition check:** Two pieces of evidence at 0.6 and 0.7 combine to 0.88 — this feels right. Independent evidence should increase confidence.

### Counter-Example: Non-Independent Evidence

**Trace:**
```clair
b5 .8 L0 @self "merge sort: O(n log n), stable"
b5b .75 L0 @self "merge sort: efficient, stable"
b5c .7 L0 @self "merge sort: divide and conquer, stable"
```

**Question:** These are all saying the same thing with different wording. Are they "independent"?

**If we combine them with ⊕:**
```
conf(use merge sort) = 0.8 ⊕ 0.75 ⊕ 0.7
                     = 0.8 + 0.75 - 0.8×0.75
                     = 1.55 - 0.6
                     = 0.95
                     = 0.95 ⊕ 0.7
                     = 0.95 + 0.7 - 0.95×0.7
                     = 1.65 - 0.665
                     = 0.985
```

**Problem:** We've inflated confidence by **rephrasing the same belief**.

The algebra assumes independence, but these beliefs are **correlated** (they all derive from the same knowledge about merge sort).

### Verdict

**Does ⊕ model how evidence should aggregate?**

✅ **YES** when evidence is truly independent:
- Different tests pointing to the same bug
- Different sources confirming the same fact
- Different arguments for the same conclusion

❌ **NO** when evidence is correlated:
- Rephrasing the same point (common in LLM outputs)
- Derivations from the same premise
- Circular justifications

**Lean theorem connection:**
- `oplus_comm`, `oplus_assoc`: Order doesn't matter (true)
- `max_le_oplus`: Aggregation never decreases confidence (true)
- `one_oplus`: One confidence absorbs to 1 (true)

**Thesis Impact:** **REFINES** — ⊕ is correct for **independent** evidence, but Thinkers must avoid double-counting correlated beliefs. This is an operational constraint, not an algebra flaw.

**Recommendation:** Add warning to spec about "independence assumption" for ⊕.

---

## Test 3: Non-Distributivity — The 0.5×0.5×0.5 Counterexample

### Lean Theorem: `mul_oplus_not_distrib`

**Proof:**
```lean
a = b = c = 0.5
a × (b ⊕ c) = 0.5 × (0.5 + 0.5 - 0.25) = 0.5 × 0.75 = 0.375
(a × b) ⊕ (a × c) = 0.25 ⊕ 0.25 = 0.25 + 0.25 - 0.0625 = 0.4375
0.375 ≠ 0.4375
```

### Practical Interpretation

**Scenario:** A belief is justified by aggregated evidence, and we want to derive from it.

**Trace:**
```clair
; Evidence 1 and 2 are aggregated
b1 .5 L0 @self "evidence A: merge sort is stable"
b2 .5 L0 @self "evidence B: merge sort is O(n log n)"
b3 .5 ⊕ L0 @self <b1,b2 "merge sort is good choice (aggregates A and B)"

; Now derive from b3
b4 .8 L0 @self <b3 "use merge sort for this problem"
```

**What's the confidence bound on b4?**

**Path 1:** `conf(b4) ≤ conf(b3) × inference_conf = 0.75 × 0.8 = 0.6`

**Path 2:** What if we "distribute" the derivation?
```
conf(b4) ≤ (conf(b1) × inference_conf) ⊕ (conf(b2) × inference_conf)
         ≤ (0.5 × 0.8) ⊕ (0.5 × 0.8)
         ≤ 0.4 ⊕ 0.4
         = 0.4 + 0.4 - 0.16
         = 0.64
```

**Problem:** We get different bounds (0.6 vs 0.64) depending on how we apply the algebra!

### Analysis

**Is this a bug?** No — it's mathematically fundamental. (⊕, ×) do NOT form a semiring.

**Does it matter in practice?**

**Most of the time: NO** — The difference (0.6 vs 0.64) is within typical confidence granularity (0.05-0.1).

**Sometimes: YES** — When precision matters:
- Safety-critical decisions (0.6 vs 0.64 could change a threshold trigger)
- Confidence aggregation at scale (many small differences compound)

### Verdict

**Does non-distributivity cause practical problems?**

⚠️ **MAYBE** — It's mathematically correct but operationally tricky:
- Thinkers must be consistent about when to apply × vs ⊕
- Assemblers must understand that confidence bounds aren't unique
- Tooling must enforce a specific evaluation order

**Thesis Impact:** **SUPPORTS with refinement** — The algebra is sound, but CLAIR needs a **canonical evaluation order** specification:
1. Compute ⊕ aggregations first (combine all evidence)
2. Then apply × derivation bounds

Or the reverse — but it must be specified.

**Recommendation:** Add "evaluation order" to spec v0.2.

---

## Test 4: Undercut — Sequential Defeat

### Lean Theorem: `undercut_compose`

**Proof:**
```lean
undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)
```

**Interpretation:** Sequential defeats combine via ⊕.

### Scenario: Cascading Defeaters

**Trace:**
```clair
; Original belief
b7 .85 L0 @self "use JWT for authentication"

; Defeater 1: JWT is stateless
d1 .6 L0 @self "stateless auth can't revoke tokens"

; Defeater 2: JWT has size limits
d2 .4 L0 @self "JWT size limits prevent large payloads"

; Apply defeats sequentially
b7d1 = undercut(b7, d1) = 0.85 × (1 - 0.6) = 0.85 × 0.4 = 0.34
b7d2 = undercut(b7d1, d2) = 0.34 × (1 - 0.4) = 0.34 × 0.6 = 0.204
```

**Using composition theorem:**
```
undercut(b7, d1 ⊕ d2) = undercut(0.85, 0.6 ⊕ 0.4)
                      = undercut(0.85, 0.76)
                      = 0.85 × (1 - 0.76)
                      = 0.85 × 0.24
                      = 0.204
```

**Match!** Sequential application equals single combined defeat.

### Counter-Example: Over-Defeat

**Trace:**
```clair
b7 .85 L0 @self "use JWT"
d1 .9 L0 @self "JWT can't be revoked"
d2 .8 L0 @self "JWT size limits"
d3 .7 L0 @self "JWT security concerns"
```

**Combined defeat:**
```
d_combined = 0.9 ⊕ 0.8 ⊕ 0.7
           = 0.9 ⊕ 0.8 = 0.98
           = 0.98 ⊕ 0.7 = 0.994
```

**Final confidence:**
```
undercut(0.85, 0.994) = 0.85 × (1 - 0.994) = 0.85 × 0.006 = 0.0051
```

**Problem:** Three moderate defeats have **annihilated** a high-confidence belief to nearly zero.

**Intuition check:** Is this correct? If JWT has three problems, should confidence drop to ~0?

**Maybe:**
- ✅ If problems are fatal (can't revoke + size + security → don't use JWT)
- ❌ If problems are minor (each is surmountable individually)

### Verdict

**Does undercut model defeat correctly?**

✅ **YES** for fatal, independent defeaters:
- Each defeater reduces confidence multiplicatively
- Sequential defeats compose correctly (proven)
- Multiple defeaters can properly eliminate a belief

⚠️ **CAUTION** for non-fatal defeaters:
- Small defeaters (0.3, 0.4) compound more than intuition suggests
- `undercut(0.9, 0.3) = 0.9 × 0.7 = 0.63` — 30% defeater → 37% confidence loss

**Thesis Impact:** **SUPPORTS with operational guidance** — The algebra is sound, but Thinkers need guidance:
1. Use defeater strength 0.7-1.0 for fatal flaws
2. Use defeater strength 0.3-0.6 for concerns
3. Be aware that multiple "concerns" (0.4 each) compound to致命 levels

---

## Test 5: Rebut — Competing Evidence

### Lean Theorem: `rebut_eq` and `rebut_add_rebut_swap`

**Proof:**
```lean
rebut(c, c) = 0.5  (equal evidence → maximal uncertainty)
rebut(a, b) + rebut(b, a) = 1  (anti-symmetric)
```

### Scenario: Algorithm Comparison

**Trace:**
```clair
; Evidence FOR merge sort
b_for .8 L0 @self "merge sort: O(n log n), stable"

; Evidence AGAINST merge sort
b_against .6 L0 @self "merge sort: needs extra space"

; Rebuttal comparison
b_final = rebut(b_for, b_against) = 0.8 / (0.8 + 0.6) = 0.571
```

**Intuition check:** 0.8 evidence for, 0.6 evidence against → 0.571 net confidence. This feels right — stronger "for" evidence wins, but not by much.

### Counter-Example: Evidence Ratios

**What creates 0.5 (maximal uncertainty)?**

| For | Against | Rebut Result | Interpretation |
|-----|---------|--------------|----------------|
| 0.9 | 0.1 | 0.9 | Overwhelming for |
| 0.7 | 0.3 | 0.7 | Strong for |
| 0.6 | 0.4 | 0.6 | Moderate for |
| 0.5 | 0.5 | 0.5 | **Balanced** |
| 0.4 | 0.6 | 0.4 | Moderate against |
| 0.1 | 0.9 | 0.1 | Overwhelming against |

**Observation:** When `for = against`, result is 0.5 (uncertainty). But result depends on **ratio**, not absolute values:

```
rebut(0.1, 0.1) = 0.1/0.2 = 0.5  (both weak → uncertainty)
rebut(0.9, 0.9) = 0.9/1.8 = 0.5  (both strong → uncertainty)
```

**Is this correct?**

- ✅ If both arguments are equally strong, we're uncertain which to pick
- ❌ But weak-equality (0.1 vs 0.1) is different from strong-equality (0.9 vs 0.9)
  - Weak: "I don't have good reasons either way" → should be 0.5
  - Strong: "Both have compelling cases" → should ALSO be 0.5?

Actually, rebut handles this correctly — both cases yield 0.5, but for different reasons.

### Verdict

**Does rebut model competing evidence correctly?**

✅ **YES** — The "market share" interpretation is intuitive:
- `rebut(a, b)` = "what portion of total evidence supports a?"
- Balanced evidence → 0.5
- Skewed evidence →偏向 stronger side

⚠️ **One edge case:** `rebut(0, 0) = 0.5` by definition (both zero → uncertainty)

**Thesis Impact:** **SUPPORTS** — Rebut is well-designed for binary choices. No practical issues found.

---

## Test 6: Min vs Multiplication

### Lean Theorem: `mul_le_min`

**Proof:**
```lean
a × b ≤ min(a, b)  for all a, b ∈ [0,1]
```

**Interpretation:** Multiplication is MORE pessimistic than min.

### Scenario: Which to Use?

**Trace (multi-justification):**
```clair
b7 .6 L0 @self "merge sort: O(n log n)"
b10 .85 L0 @self "insertion sort: good for small n"
b12 ? L0 @self <b7,b10 "use merge sort for general purpose"
```

**Question:** What should `conf(b12)` be?

**Option 1: Multiplication (derivation chain)**
```
conf(b12) ≤ conf(b7) × conf(b10) × inference
         ≤ 0.6 × 0.85 × inference
         ≤ 0.51 × inference
         ≈ 0.46 (if inference = 0.9)
```

**Option 2: Min (weakest link)**
```
conf(b12) ≤ min(conf(b7), conf(b10))
         ≤ min(0.6, 0.85)
         = 0.6
```

**Difference:** min (0.6) is MORE optimistic than multiplication (0.46).

**Which is correct?**

It depends on the **justification semantics**:
- **Conjunctive:** b12 requires BOTH b7 AND b10 to be true → use multiplication
- **Disjunctive:** b12 is supported by b7 OR b10 → use oplus (not min)
- **Weakest link:** b12 is no stronger than its weakest justification → use min

The trace `<b7,b10` doesn't specify which semantics!

### Verdict

**Does min or multiplication better model derivation?**

✅ **Multiplication** for conjunctive derivation:
- "If A AND B are true, then C"
- Each step adds uncertainty
- Correct for chains

✅ **Min** for "no stronger than weakest":
- "C is at most as confident as its least-confident justification"
- Doesn't compound uncertainty
- Correct for multi-parent beliefs where parents aren't conjoined

⚠️ **Problem:** CLAIR spec doesn't distinguish these semantics!

**Recommendation:** Clarify `<b1,b2>` in spec v0.2:
- `<(b1 ∧ b2)` for conjunctive (multiplication bound)
- `<(b1 ∨ b2)` for disjunctive (oplus aggregation)
- `<min(b1, b2)` for weakest-link (min bound)

**Thesis Impact:** **REFINES** — The algebra has both operations, but the spec needs clearer semantics for multi-justification.

---

## Summary: Lean Theorem → IR Implications Mapping

### Multiplication Theorems

| Lean Theorem | IR Implication | Constrains Traces? |
|--------------|----------------|-------------------|
| `mul_le_left`, `mul_le_right` | Derivation chains decrease confidence | ✅ YES — conf(child) ≤ conf(parent) |
| `mul_mem'` | Multiplication stays in [0,1] | ✅ YES — always valid |
| `nonneg`, `le_one` | Confidence is bounded | ✅ YES — syntax constraint |

**Practical issue:** Traces often violate `mul_le_left` (confidence increases through derivation). This is a **trace quality problem**, not an algebra problem.

### Oplus Theorems

| Lean Theorem | IR Implication | Constrains Traces? |
|--------------|----------------|-------------------|
| `oplus_comm`, `oplus_assoc` | Aggregation order doesn't matter | ✅ YES — can combine in any order |
| `max_le_oplus` | Aggregation increases confidence | ✅ YES — confirms ⊕ is for evidence combination |
| `zero_oplus`, `one_oplus` | 0 is identity, 1 absorbs | ✅ YES — edge cases handled |
| `mul_oplus_not_distrib` | Can't distribute × through ⊕ | ⚠️ OPERATIONAL — need evaluation order |

**Practical issue:** ⊕ assumes independence. Correlated evidence inflates confidence. This is an **operational constraint**, not an algebra problem.

### Undercut Theorems

| Lean Theorem | IR Implication | Constrains Traces? |
|--------------|----------------|-------------------|
| `undercut_compose` | Sequential defeats combine via ⊕ | ✅ YES — d₁ then d₂ = d₁ ⊕ d₂ |
| `undercut_le` | Defeat never increases confidence | ✅ YES — sanity check |
| `undercut_zero`, `undercut_one` | 0 = no defeat, 1 = complete defeat | ✅ YES — edge cases |

**Practical issue:** Multiple moderate defeaters (0.3-0.5 each) compound severely. This is mathematically correct but **operationally tricky**.

### Rebut Theorems

| Lean Theorem | IR Implication | Constrains Traces? |
|--------------|----------------|-------------------|
| `rebut_eq` | Equal evidence → 0.5 (uncertainty) | ✅ YES — balanced case |
| `rebut_add_rebut_swap` | Anti-symmetric: rebut(a,b) + rebut(b,a) = 1 | ✅ YES — consistency check |
| `rebut_mono_for`, `rebut_anti_against` | Monotonicity | ✅ YES — more "for" evidence increases result |

**Practical issue:** None found. Rebut works as expected.

### Min Theorems

| Lean Theorem | IR Implication | Constrains Traces? |
|--------------|----------------|-------------------|
| `mul_le_min` | Min ≥ multiplication (more optimistic) | ⚠️ OPERATIONAL — when to use which? |
| `min_comm`, `min_assoc` | Min is commutative, associative | ✅ YES — order doesn't matter |
| `one_min`, `zero_min` | 1 is identity, 0 absorbs | ✅ YES — edge cases |

**Practical issue:** Spec doesn't distinguish when to use min vs × for multi-justification.

---

## Counterintuitive Results Catalog

### 1. Chain-Length Collapse

**Phenomenon:** 10-step derivation chain with 0.9 per-step confidence → final confidence ≤ 0.35

**Counterintuitive because:** "Each step is 90% confident, so the conclusion should be highly confident"

**Actually correct:** "Each step might be wrong, so after 10 steps, we're not sure"

**Verdict:** Algebra is RIGHT, intuition is WRONG.

### 2. Non-Distributivity (0.375 vs 0.4375)

**Phenomenon:** `0.5 × (0.5 ⊕ 0.5) ≠ (0.5 × 0.5) ⊕ (0.5 × 0.5)`

**Counterintuitive because:** In normal algebra, a(b+c) = ab+ac

**Actually:** ⊕ is not + — it's probabilistic OR, which doesn't distribute

**Verdict:** Algebra is RIGHT, but operationally requires canonical evaluation order.

### 3. Multiple Moderate Defeaters → Zero

**Phenomenon:** Three 0.4 defeaters → confidence drops from 0.9 to ~0.05

**Counterintuitive because:** "These are minor concerns, why is confidence destroyed?"

**Actually:** Multiple independent concerns compound multiplicatively

**Verdict:** Algebra is RIGHT, but Thinkers need to calibrate defeater strength (use 0.3-0.5 for minor, 0.7-1.0 for fatal).

### 4. Rebut(0.1, 0.1) = 0.5 = Rebut(0.9, 0.9)

**Phenomenon:** Weak-balance and strong-balance both yield 0.5

**Counterintuitive because:** "Weak uncertainty ≠ Strong uncertainty"

**Actually:** Both are balanced — absolute strength doesn't matter, only ratio

**Verdict:** Algebra is RIGHT — 0.5 means "balanced", not "weakly balanced".

### 5. Confidence Inflation Through Rephrasing

**Phenomenon:** Same belief rephrased 3 times → confidence inflated via ⊕

**Counterintuitive because:** "I said the same thing 3 times, why is confidence higher?"

**Actually:** ⊕ assumes independence — correlated evidence breaks this assumption

**Verdict:** Algebra is RIGHT, but Thinkers must avoid double-counting correlated beliefs.

---

## Thesis Connection

### Does the algebra support or undermine CLAIR viability?

**SUPPORTS with operational refinements:**

1. **The algebra is mathematically sound** — All 40+ theorems are correct and proven
2. **Operations model intuition correctly** — When understood and applied properly
3. **Counterintuitive results are actually correct** — They reveal biases in human reasoning

**Refinements needed:**

1. **Spec v0.2 additions:**
   - Clarify multi-justification semantics (<a,b> vs <a∧b> vs <a∨b>)
   - Specify canonical evaluation order (× before ⊕ or vice versa)
   - Add warnings: ⊕ assumes independence, defeaters compound
   - Add guidance: use × for conjunctive, min for weakest-link

2. **Thinker training:**
   - Don't let confidence increase through derivation
   - Be aware of chain-length penalty
   - Avoid correlated evidence with ⊕
   - Calibrate defeater strength (0.7-1.0 for fatal, 0.3-0.6 for concerns)

3. **Assembler expectations:**
   - Confidence bounds, not exact values
   - Multiple valid bounds possible (non-distributivity)
   - Low confidence from long chains is expected, not error

### Verdict: Is the algebra viable?

**YES.** The algebra is not the problem. The problem is:
1. Hand-authored traces often violate it (human error)
2. Spec doesn't fully clarify semantics (ambiguity)
3. Thinkers need training (operational gap)

These are **fixable**, not fundamental.

---

## Open Questions

1. **Evaluation order:** Should spec canonicalize ×-then-⊕ or ⊕-then-×? Does it matter?

2. **Multi-justification semantics:** Should `<b1,b2>` mean:
   - Conjunction (both required) → multiplication bound?
   - Disjunction (either sufficient) → oplus aggregation?
   - Weakest link → min bound?
   - Belief-specific (Thinker chooses)?

3. **Confidence granularity:** If differences of 0.06 (0.375 vs 0.4375) rarely matter, should we use coarser granularity (0.0, 0.25, 0.5, 0.75, 1.0)?

4. **Defeater calibration:** How should Thinkers decide between 0.4 (concern) vs 0.8 (fatal)? Need rubric.

5. **Independence testing:** How can Assemblers detect when ⊕ was applied to correlated evidence?

6. **Chain-length threshold:** At what chain length should we warn Thinkers about confidence collapse?

---

## Examples (≥3 per operation)

### Multiplication Examples

1. **Valid derivation:** `b2 .95 → b7 .6 → b12 .54` (correctly decreasing)
2. **Invalid derivation:** `b2 .95 → b7 .6 → b12 .7` (increased, violates algebra)
3. **Long chain collapse:** 10 steps × 0.9 each → final ≤ 0.35

### Oplus Examples

1. **Independent evidence:** Bug diagnosis from two sources → 0.6 ⊕ 0.7 = 0.88
2. **Correlated evidence:** Rephrasing same point → inflated confidence (don't do this)
3. **Many small evidences:** 0.3 ⊕ 0.3 ⊕ 0.3 ⊕ 0.3 = 0.76 (accumulates)

### Undercut Examples

1. **Single defeat:** 0.85 undercut by 0.6 → 0.34
2. **Sequential defeat:** 0.85 → 0.6 → 0.4 = 0.85 undercut by 0.76 → 0.204
3. **Over-defeat:** Three 0.4 defeaters → 0.9 → 0.005 (near zero)

### Rebut Examples

1. **Skewed:** 0.8 for vs 0.6 against → 0.571 (for wins)
2. **Balanced:** 0.5 vs 0.5 → 0.5 (uncertainty)
3. **Overwhelming:** 0.9 for vs 0.1 against → 0.9 (for dominates)

### Min Examples

1. **Weakest link:** min(0.6, 0.85) = 0.6 (bounded by worst parent)
2. **Min vs mul:** min(0.9, 0.9) = 0.9 vs 0.9 × 0.9 = 0.81 (min is optimistic)
3. **Many parents:** min(0.3, 0.7, 0.9, 0.5) = 0.3 (one weak parent drags down)

---

## Counter-Examples (≥1 per operation)

### Multiplication Counter-Example

**Issue:** Mathematical deduction shouldn't compound uncertainty
- Trace: "if a=b and b=c then a=c" (deductive certainty)
- Algebra: 0.95 × 0.95 × 0.95 = 0.86 (suggests uncertainty)
- Resolution: Use 1.0 for deductive steps (A4 finding)

### Oplus Counter-Example

**Issue:** Correlated evidence inflates confidence
- Trace: Same belief rephrased 3 times
- Algebra: 0.7 ⊕ 0.75 ⊕ 0.8 = 0.985 (overconfidence)
- Resolution: Thinkers must ensure independence

### Undercut Counter-Example

**Issue:** Moderate defeaters over-penalize
- Trace: Three 0.4 defeaters (minor concerns)
- Algebra: 0.9 → 0.005 (annihilated)
- Resolution: Use 0.7+ for fatal, 0.3-0.5 for minor

### Rebut Counter-Example

**Issue:** None found — rebut works well

### Min Counter-Example

**Issue:** Spec doesn't clarify when to use min vs ×
- Trace: `<b1,b2>` with conf(b1)=0.6, conf(b2)=0.85
- Question: Is bound = 0.6 (min) or 0.51 (mul)?
- Resolution: Spec v0.2 should clarify semantics

---

## Key Findings

1. **The algebra is sound** — All 40+ Lean theorems are correct and applicable

2. **Practical issues are operational, not fundamental:**
   - Traces violate `mul_le_left` (confidence increases through derivation)
   - ⊕ assumes independence, but Thinkers provide correlated evidence
   - Spec doesn't clarify multi-justification semantics
   - Evaluation order unspecified (non-distributivity)

3. **Counterintuitive results are often correct:**
   - Chain-length collapse: long chains SHOULD be uncertain
   - Non-distributivity: mathematically fundamental, not a bug
   - Multiple defeaters: SHOULD compound (independence assumption)

4. **Spec v0.2 needs:**
   - Multi-justification semantics (<a∧b> vs <a∨b> vs min)
   - Canonical evaluation order
   - Independence warning for ⊕
   - Defeater calibration rubric
   - Chain-length warnings

5. **Thinker training is essential:**
   - Confidence can't increase through derivation
   - Correlated evidence breaks ⊕
   - Defeater strength matters (0.7+ for fatal)
   - Use 1.0 for deductive certainty

**Thesis:** **SUPPORTS with refinement** — The confidence algebra is a viable foundation for CLAIR IR. Practical issues are addressable through spec clarification and Thinker training, not fundamental flaws.

---

## Connection to R1: Confidence Algebra Mapping

This exploration (D4) directly feeds into **R1: Confidence algebra mapping**. Each Lean theorem analyzed here maps to an IR-model implication:

| R1 Task | D4 Contribution |
|---------|-----------------|
| `mul_le_left` → derivation chains decrease | Test 1: Chain-length collapse |
| `oplus_comm`/`oplus_assoc` → order doesn't matter | Test 2: Independence assumption |
| `mul_oplus_not_distrib` → can't distribute | Test 3: Evaluation order needed |
| `undercut_compose` → sequential defeats | Test 4: Defeater compounding |
| `rebut_eq` → equal evidence → 0.5 | Test 5: Balanced evidence |

D4 provides the **practical context** for R1's theoretical mapping.

---

**End of D4 Exploration**
