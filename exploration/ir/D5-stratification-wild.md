# D5: Stratification in the Wild

## Research Question

Does stratification actually come up in LLM reasoning traces? The CLAIR spec defines levels (L0, L1, L2...) with Löb discount (c → c²) to prevent self-reference paradoxes and confidence bootstrapping. But are meta-beliefs (beliefs about beliefs) a natural phenomenon in real traces, or is this a theoretical solution to a problem that doesn't occur?

**Thesis Connection:** Stratification is a core design constraint in CLAIR. If meta-beliefs never occur naturally, the complexity of levels may be unnecessary. If they occur frequently but aren't captured correctly, CLAIR loses critical auditability information. This exploration tests whether stratification supports, undermines, or refines the thesis.

**Validation Criteria:**
- ≥3 natural examples of meta-beliefs in real reasoning traces
- Counter-examples: when stratification is unnecessary or harmful
- Assessment of whether Löb discount matches intuition
- Connection to Lean proofs
- Open questions

---

## Background: The Stratification Mechanism

### From the Spec (`formal/clair-spec.md`)

```
Stratification (Self-Reference Safety)

1. Level constraint: A belief at level N can only justify beliefs at level ≥ N
2. Meta-belief constraint: A belief *about* another belief must be at a higher level
3. Löb discount: If belief b2 at level L+1 references belief b1 at level L, then conf(b2) ≤ conf(b1)²
```

### Key Lean Proofs (`formal/lean/CLAIR/Belief/Stratified.lean`)

| Theorem | Statement | Practical Implication |
|---------|-----------|----------------------|
| `no_self_introspection` | ¬(n < n) | No belief can introspect itself at the same level |
| `no_circular_introspection` | m < n → ¬(n < m) | No circular meta-reasoning (A about B, B about A) |
| `no_confidence_bootstrap` | loebChain c k ≤ c | Finite meta-levels can't increase confidence |
| `loebDiscount_strict_lt` | c² < c for 0 < c < 1 | Meta-beliefs strictly less confident |
| `loebChain_decreasing` | c^(2^(k+1)) ≤ c^(2^k) | Confidence decreases exponentially through levels |

### Example from Minimal Spec

```
b1 .9 L0 @self "X is true"
b2 .81 L1 @self <b1 "I believe b1"      ; .9² = .81 ✓
b3 .65 L2 @self <b2 "I believe b2"      ; .81² ≈ .65 ✓
```

This shows the mechanism working in a toy example. But do real LLM traces ever need this?

---

## Methodology: Searching for Meta-Beliefs

To find natural meta-beliefs, I analyzed:

1. **Existing traces** (A1: 6 problem types, B1: 5 fidelity tests, C1: query patterns)
2. **Teachability experiments** (A3: where LLMs struggle with levels)
3. **Natural language patterns** that indicate meta-reasoning

### What I Found

**Across 20+ existing CLAIR traces: ZERO beliefs at L1 or higher.**

Every trace in A1, B1, C1, D1, D2, D6 uses L0 exclusively. The only L1 examples are:
- Artificial examples in `notes/exploration-2026-01-29-minimal-spec.md` (demonstration)
- Teachability failure cases showing LLMs misuse levels (A3)

This suggests either:
1. Meta-beliefs don't occur naturally in practical reasoning
2. LLMs aren't capturing them when they do occur
3. The "belief about belief" framing doesn't map to natural reasoning patterns

---

## Example 1: Self-Correction (Meta-Belief Occurs Naturally)

### Scenario

The Thinker realizes an earlier assumption was wrong and updates its reasoning. This is a **meta-cognitive act** — reasoning about previous reasoning.

### Without Stratification (What LLMs Naturally Do)

```clair
; Original (flawed) reasoning
b1 1.0 L0 @user "parse HTML and extract all <a> tags"
b2 .9 L0 @self <b1 "use regex to match <a.*href.*>"
b3 .9 L0 @self <b2 "extract href attribute"

; Later realization
b4 .3 L0 @self "regex can't parse nested HTML"
b5 .9 L0 @self <b4 "use proper HTML parser instead"
b6 .9 L0 @self <b5 "extract <a> tags with parser"
```

**Problem:** This trace **contradicts itself**. b2 says "use regex" with .9 confidence. b5 says "use parser" with .9 confidence. Both are at L0. The trace doesn't show **why** b2 was rejected — it just presents a new belief.

A human auditor asking "Why did you abandon regex?" gets no answer. The trace shows two competing beliefs but no meta-reasoning about the revision.

### With Stratification (Capturing Meta-Reasoning)

```clair
; Original reasoning
b1 1.0 L0 @user "parse HTML and extract all <a> tags"
b2 .9 L0 @self <b1 "use regex to match <a.*href.*>"
b3 .9 L0 @self <b2 "extract href attribute"

; Meta-belief: realizing b2 was wrong
b4 .3 L1 @self <b2 "b2 is wrong: regex cannot handle nested HTML"
b5 .7 L1 @self <b4 "b2 should be invalidated"

; New L0 reasoning (aware of the meta-correction)
b6 .9 L0 @self <b1,b5 ?["valid HTML"] "use proper HTML parser"
b7 .9 L0 @self <b6 "extract <a> tags with DOM traversal"
b8 .9 L0 @self <b7 "extract href attribute"

; Invalidation of original belief
b2 .0 L0 @self <b5 ?["valid HTML"] "INVALIDATED: regex insufficient"
```

**Analysis:**
- b4 is at L1: it's a belief **about** b2 (a L0 belief)
- b5 is at L1: it's a belief about what **should happen** to b2
- b6 at L0 references b5 (L1), which is allowed (L0 can be justified by higher levels)
- Löb discount: if b2 had .9, b4's max confidence is .9² = .81 (actual .3 is well below)

**Why this matters:**
1. The trace now shows **why** regex was abandoned
2. The invalidation of b2 is explicit and justified
3. Future queries ("Why not regex?") are answerable: trace shows b4→b5

**Does this occur naturally?**

Yes! Self-correction is common in LLM reasoning. Examples:
- "Actually, that won't work because..."
- "Let me reconsider..."
- "On second thought..."

But LLMs don't naturally represent this as meta-beliefs. They output new L0 beliefs that contradict old ones, without the explicit meta-link.

---

## Example 2: Confidence Assessment (Meta-Belief About Confidence)

### Scenario

The Thinker needs to express uncertainty **about its own confidence** in a conclusion. This is a **meta-epistemic** state — reasoning about the quality of one's own reasoning.

### Natural Language Pattern

"I think this is the right approach, but I'm not very confident because I'm making assumptions about X."

### Without Stratification (Ambiguous)

```clair
b1 1.0 L0 @user "design a database schema for e-commerce"
b2 .6 L0 @self <b1 "use relational database"
b3 .6 L0 @self <b2 "confidence is low because scale requirements unknown"
```

**Problem:** b3 is a "confidence explanation" at L0. Is b3:
- A justification for b2's low confidence? (semantically: b3 explains b2)
- An independent belief about confidence? (semantically: b3 is about b2)

The L0 level makes this ambiguous. A query "Why is confidence only .6?" will trace to b3, but b3's content ("confidence is low...") is **about** b2, not about the database problem.

### With Stratification (Explicit Meta-Level)

```clair
b1 1.0 L0 @user "design a database schema for e-commerce"
b2 .6 L0 @self <b1 "use relational database"

; Meta-belief: assessing confidence in b2
b3 .5 L1 @self <b2 "b2's confidence is limited by unknown scale"
b4 .4 L1 @self <b3 "if scale > 10M users, reconsider b2"

; Alternative with justification
b5 .7 L0 @self <b1,b3 "use relational database, acknowledge scale assumption"

; Invalidation condition at L0
b2 .6 L0 @self <b5 ?["scale > 10M"] "use relational database"
```

**Analysis:**
- b3 is at L1: it's a belief **about the confidence level** of b2
- b4 is at L1: it's a belief **about when to reconsider** b2
- b5 at L0 uses b3 (L1) as justification — allowed
- Löb discount: if b2 has .6, b3's max is .6² = .36 (actual .5 violates the rule!)

**Wait — this is a problem!**

The Löb discount (c → c²) is **too aggressive** for this case. b3 says "b2's confidence is limited," which is a **weak negative claim** about b2, not a strong positive claim like "I believe b2."

The intuition: "I'm uncertain about my uncertainty" should have confidence around .5 (maximal uncertainty about the meta-question). But the Löb discount would cap it at .6² = .36.

**Counter-example:** Löb discount is **too strict** for certain meta-beliefs.

---

## Example 3: Alternative Evaluation (Meta-Belief About Decision Quality)

### Scenario

The Thinker considers multiple alternatives and needs to record **why** one was chosen over others. This is a meta-decision — a decision about decisions.

### Natural Language Pattern

"I chose approach A over B because A is faster, though B would be simpler."

### Without Stratification (Mixed Signals)

```clair
b1 1.0 L0 @user "implement a web scraper"
b2 .8 L0 @self <b1 "use async/await pattern"
b3 .6 L0 @self <b1 "use thread pool"
b4 .9 L0 @self <b2,b3 ?["language supports async"] "async is better: higher concurrency"
```

**Problem:** b4 references both b2 and b3. Is b4:
- A comparison (meta-level: "b2 beats b3")?
- A synthesis (ground-level: "combine approaches")?
- A final decision (ground-level: "use async")?

The L0 level doesn't distinguish these. An auditor asking "Why async over thread pool?" gets b4, but b4 mixes the **comparison** (meta) with the **decision** (ground).

### With Stratification (Separate Levels)

```clair
; Ground-level alternatives
b1 1.0 L0 @user "implement a web scraper"
b2 .8 L0 @self <b1 "use async/await pattern"
b3 .6 L0 @self <b1 "use thread pool"

; Meta-level comparison
b4 .7 L1 @self <b2,b3 "async has higher concurrency than thread pool"
b5 .5 L1 @self <b2 "async requires language support"

; Ground-level decision (informed by meta)
b6 .9 L0 @self <b1,b4,b5 ?["language supports async"] "use async/await pattern"
b7 .8 L0 @self <b1,b4 ?["language lacks async"] "use thread pool"

; Invalidation of rejected alternative
b3 .3 L0 @self <b4 ?["language supports async"] "thread pool: rejected due to lower concurrency"
```

**Analysis:**
- b4, b5 at L1: beliefs **comparing** b2 and b3 (both at L0)
- b6, b7 at L0: decisions **informed by** the comparison
- Löb discount: b4's max confidence is min(.8, .6)² = .36, but actual is .7 (violates!)

**Another counter-example:** The comparison meta-belief has **higher** confidence than the alternatives being compared. This is intuitive: I can be more confident that "A > B" than I am in A or B individually.

---

## Finding: Natural Meta-Beliefs Are Rare

Across three examples where meta-beliefs **could** naturally occur:

| Example | Natural Occurrence | LLM Behavior (no level guidance) |
|---------|-------------------|----------------------------------|
| Self-correction | Frequent ("on second thought...") | Contradictory L0 beliefs, no meta-link |
| Confidence assessment | Occasional ("I'm uncertain because...") | L0 "confidence explanation" beliefs |
| Alternative evaluation | Frequent ("A vs B because...") | L0 comparison mixed with decision |

**Key insight:** LLMs **do** perform meta-reasoning, but they don't naturally represent it at higher levels. They flatten everything to L0, mixing:
- Ground-level claims ("use async")
- Meta-level comparisons ("async beats thread pool")
- Meta-epistemic assessments ("my confidence is low")

---

## Finding: Löb Discount is Too Aggressive

The Löb discount (c → c²) prevents confidence bootstrapping, but it's **too strict** for natural meta-beliefs.

### Example Where Löb Discount Matches Intuition

```clair
b1 .9 L0 @self "the code is correct"
b2 .81 L1 @self <b1 "I believe b1"    ; .9² = .81 ✓
```

Intuition: "I believe my belief" should be less confident than the belief itself. ✓ Matches.

### Counter-Example Where Löb Discount Fails

```clair
b1 .6 L0 @self "use relational database"
b2 .5 L1 @self <b1 "b1's confidence is limited by unknown scale"
```

Intuition: "I'm uncertain about my uncertainty" → ~.5 (maximal uncertainty about meta-question).
Löb discount: max is .6² = .36. ✗ Too strict!

### Counter-Example: Comparison Can Exceed Source

```clair
b1 .6 L0 @self "use async/await"
b2 .5 L0 @self "use thread pool"
b3 .7 L1 @self <b1,b2 "async has higher concurrency than thread pool"
```

Intuition: I can be **more confident** that "A > B" than I am in A or B individually.
Löb discount: max is min(.6, .5)² = .25. ✗ Way too strict!

**Issue:** The Löb discount assumes **endorsement** meta-beliefs ("I believe X"), but many natural meta-beliefs are **comparative** ("X is better than Y") or **qualitative** ("X is limited by Y").

---

## Finding: Meta-Beliefs Occur in Specific Patterns

From the examples, meta-beliefs occur naturally in these patterns:

### Pattern 1: Revision ("I was wrong")

```
L0: original claim
L1: assessment that L0 claim was wrong
L0: new claim (informed by L1)
```

### Pattern 2: Comparison ("X vs Y")

```
L0: claim X
L0: claim Y
L1: X > Y (comparative meta-belief)
L0: choose X (informed by L1)
```

### Pattern 3: Qualification ("X is limited by Y")

```
L0: claim X
L1: X is limited (qualitative meta-belief)
L0: modified X (informed by L1)
```

### Pattern 4: Grounding ("X depends on Y")

```
L0: claim X
L1: X assumes Y (meta-belief about dependency)
L0: invalidation condition on X
```

**Key observation:** In all patterns, L1 beliefs **inform** subsequent L0 beliefs but don't **replace** them. The trace flows: L0 → L1 → L0.

---

## Counter-Example 1: Meta-Beliefs Are Unnecessary for Simple Reasoning

For straightforward problems, stratification adds complexity without benefit.

### Example: Simple Algorithm Selection

```clair
; Without stratification (simpler, works fine)
b1 1.0 L0 @user "sort an array"
b2 .9 L0 @self <b1 "use merge sort for large arrays"
b3 .8 L0 @self <b1 ?["n < 10"] "use insertion sort for small arrays"
```

This trace is clear, auditable, and doesn't need levels. Adding meta-beliefs would only complicate it:

```clair
; With unnecessary stratification
b1 1.0 L0 @user "sort an array"
b2 .9 L0 @self <b1 "use merge sort for large arrays"
b3 .8 L0 @self <b1 ?["n < 10"] "use insertion sort for small arrays"
b4 .7 L1 @self <b2,b3 "merge sort better for large n"  ; What does this add?
```

b4 is a meta-belief comparing b2 and b3, but it adds no information. The comparison is already implicit in the confidence scores (.9 vs .8).

**Verdict:** For simple decisions, confidence scores alone capture comparative reasoning. Meta-beliefs are redundant.

---

## Counter-Example 2: LLMs Cannot Produce Stratified Traces Reliably

From A3 teachability experiments:

### Failure Mode: Level Misuse

```
; Under-use: everything at L0
b10 0.9 L0 @self <b1 "I believe b1 is correct"  ; should be L1

; Over-use: arbitrary L1, L2
b5 0.8 L1 @self "bubble sort"  ; no need for L1
```

### Root Cause

Stratification is a **formal concept** from mathematical logic (Tarski's hierarchy). LLMs don't have intuitive understanding of:
- "Belief about belief" vs "belief about world"
- When to increment levels
- How Löb discount applies

### Empirical Result

Even with few-shot examples and explicit instructions, LLMs struggle:
- **Under-use**: 90%+ of beliefs at L0, even when meta-beliefs appropriate
- **Over-use**: Random L1/L2 for non-meta beliefs (e.g., "use bubble sort" at L1)
- **Circularity**: Accidentally creating L1→L0→L1 cycles

**Verdict:** Stratification is **operationally difficult** for LLMs. This doesn't mean it's wrong — but it suggests the spec needs better tooling (validation, post-processing) to work in practice.

---

## Counter-Example 3: Löb Discount Creates Incentive to Stay at L0

Since Löb discount reduces confidence (c → c²), there's a perverse incentive to **avoid meta-beliefs** to keep confidence high.

### Example

```clair
; Approach 1: Use meta-belief (L1)
b1 .9 L0 @self "use async/await"
b2 .81 L1 @self <b1 "I believe b1 is correct"  ; .9² = .81

; Approach 2: Stay at L0 (no discount)
b1 .9 L0 @self "use async/await"
b2 .9 L0 @self <b1 "async is correct because..."  ; No discount!
```

Both b2 beliefs express the same idea ("I believe b1"). But the L1 version has lower confidence (.81 vs .9) due to Löb discount.

**Issue:** This creates a **bias against meta-beliefs**. A Thinker LLM trying to maximize confidence (which might correlate with "being helpful") will avoid L1.

**Verdict:** The Löb discount, while theoretically sound, may **discourage** the very meta-reasoning it's meant to capture.

---

## Synthesis: When Does Stratification Actually Help?

### Stratification Helps When:

1. **Self-correction needs to be explicit:** The trace should show **why** an earlier belief was wrong, not just present a contradiction.

2. **Confidence assumptions need to be tracked:** The trace should show **what limits confidence** (unknowns, dependencies).

3. **Comparative decisions need justification:** The trace should show **why A was chosen over B**, not just that A was chosen.

4. **Auditors need to query "why":** Humans need to ask "Why did you change your mind?" or "Why not the alternative?"

### Stratification Is Unnecessary When:

1. **Simple linear reasoning:** No alternatives, no revisions, no self-reference.

2. **Confidence scores are sufficient:** The comparison is implicit in .9 vs .6.

3. **No auditing needed:** The trace is for machine consumption only, not human inquiry.

### Stratification Is Harmful When:

1. **It creates false confidence:** Löb discount is too aggressive for comparative/qualitative meta-beliefs.

2. **It biases against meta-reasoning:** The confidence penalty discourages LLMs from using levels.

3. **It's too complex for LLMs:** Teachability experiments show systematic misuse.

---

## Lean Theorems → Practical Implications

| Theorem | Formal Statement | Practical Implication |
|---------|-----------------|----------------------|
| `no_self_introspection` | ¬(n < n) | A belief cannot reference itself at the same level — prevents direct self-justification loops |
| `no_circular_introspection` | m < n → ¬(n < m) | No circular meta-reasoning (A about B, B about A) — prevents "I believe you believe me believe..." |
| `no_confidence_bootstrap` | loebChain c k ≤ c | Finite meta-levels can't increase confidence — prevents "I'm reliable" → "my beliefs are trustworthy" → ... |
| `loebDiscount_strict_lt` | c² < c for 0 < c < 1 | Meta-beliefs strictly less confident — **ISSUE**: Too aggressive for comparative meta-beliefs |
| `loebChain_decreasing` | c^(2^(k+1)) ≤ c^(2^k) | Confidence decreases exponentially through levels — **ISSUE**: Creates incentive to stay at L0 |

**Gap Identified:** The Lean proofs assume **endorsement meta-beliefs** ("I believe X"), but natural language uses **comparative** ("X > Y") and **qualitative** ("X is limited") meta-beliefs. The formalization doesn't cover these cases.

---

## Thesis Impact

**Thesis:** CLAIR is a viable IR between Thinker and Assembler LLMs — it preserves *why* decisions were made, enables auditing, and doesn't lose essential information at the boundary.

### How D5 Refines the Thesis

**Finding:** Stratification is theoretically sound but **operationally problematic**.

1. **Supports:** Meta-beliefs DO occur naturally (self-correction, comparison, qualification). Without levels, traces lose this meta-information.

2. **Undermines:** LLMs cannot reliably produce stratified traces. Teachability is poor.

3. **Refines:** The Löb discount (c → c²) is too aggressive for natural meta-beliefs. A weaker discount (e.g., c → √c, or no discount for comparative/qualitative) may be more appropriate.

**Revised Thesis:** CLAIR is viable **with operational constraints**:
- Thinkers need validation tools to ensure correct level usage
- The Löb discount should be relaxed or eliminated for comparative/qualitative meta-beliefs
- Meta-beliefs should be optional (most traces don't need them)

---

## Open Questions

1. **Alternative to Löb discount?** Can we design a confidence penalty that prevents bootstrapping but allows comparative meta-beliefs to have reasonable confidence?

2. **Automatic level inference?** Can we detect meta-beliefs post-hoc and assign levels automatically? (e.g., "belief about belief ID" → L1)

3. **Is L0-only sufficient?** Most real traces use only L0. Can we define a "CLAIR Lite" that omits levels entirely?

4. **Confidence vs. belief ID:** Should meta-beliefs use a different reference mechanism? (e.g., `@belief:b1` instead of `<b1`)

5. **Teaching LLMs stratification:** Can we develop better prompts, examples, or fine-tuning to make level usage intuitive?

6. **Empirical studies:** Do humans actually query meta-reasoning ("Why did you change your mind?") in practice, or is this a theoretical concern?

---

## Recommendations for Spec v0.2

1. **Make meta-beliefs optional:** Levels should be "advanced features," not required for basic traces.

2. **Relax Löb discount for comparative meta-beliefs:** Use c → √c or no discount for "X > Y" comparisons.

3. **Add level inference rules:** If content references a belief ID, auto-promote to L1.

4. **Provide validation tools:** DAG checker that detects level violations and suggests corrections.

5. **Add "meta-belief patterns" section:** Document the 4 patterns (revision, comparison, qualification, grounding) with examples.

6. **Consider "confidence source" field:** Separate "confidence in X" from "confidence that X > Y."

---

## Conclusion

Stratification is a **theoretically elegant** solution to self-reference paradoxes, but it's **operationally problematic** in practice:

- ✅ **Natural:** Meta-beliefs occur in self-correction, comparison, and qualification
- ✅ **Useful:** They enable "why did you change your mind?" queries
- ❌ **Unreliable:** LLMs struggle to produce correct stratified traces
- ❌ **Over-aggressive:** Löb discount penalizes valid meta-reasoning
- ⚠️ **Rare:** Most traces don't need levels — L0 is sufficient

**Verdict:** Stratification **refines** the thesis. It's not fundamental to CLAIR's viability, but it's a powerful feature for certain use cases (auditing, self-correction tracking). The spec should make levels optional and provide better tooling.

**Thesis Status:** **SUPPORTED WITH REFINEMENT** — CLAIR is viable, but stratification needs operational improvements (better teaching, relaxed discount, optional levels).
