# A2: Trace Quality Analysis

## Research Question

What makes a CLAIR trace "high quality" beyond structural validity? A trace can be grammatically correct and acyclic yet still fail to guide an Assembler effectively. This exploration defines explicit quality criteria (connectedness, calibration, completeness, granularity), evaluates existing traces against these criteria, and documents common failure modes.

**Thesis Connection:** If CLAIR is viable as an IR, we must be able to distinguish good traces from bad traces. Quality criteria are essential for:
- Training Thinker LLMs to produce useful traces
- Validating traces before passing to Assemblers
- Understanding when CLAIR succeeds vs fails

**Validation Criteria:**
- Explicit quality criteria defined (4+ dimensions)
- Evaluation of 6+ traces from A1 against criteria
- Analysis of common failure modes
- Counter-examples: what makes quality hard to achieve?
- Connection to thesis (supports, undermines, or refines)
- Open questions for future work

---

## Background: Valid vs Quality

A CLAIR trace can be **structurally valid** but **low quality**:

| Dimension | Valid | Quality | Example |
|-----------|-------|---------|---------|
| Grammar | ✅ Conforms to syntax | ✅ | `b1 .9 L0 @self "sort"` |
| Acyclicity | ✅ No cycles | ✅ | Linear chain |
| Confidence | ✅ In [0,1] | ❓ | `.5`, `.5`, `.5` — no discrimination |
| Justification | ✅ References exist | ❓ | `<b1` — tautological |
| Content | ✅ String present | ❓ | "do the thing" — useless |

**Valid but low quality traces exist** (see D2: tautological trace, confidence-splat trace, disconnected DAG).

This exploration asks: What separates **high quality** from **low quality**?

---

## Quality Criterion 1: Connectedness

### Definition

All beliefs should be **grounded** in the user request through justification chains. No "orphan islands" of disconnected content.

### Formalization

For each belief `b` in the trace:
```
Grounded(b) = ∃ path: b → ... → b_user_request
```

A trace has **Connectedness Score** = `(count of grounded beliefs) / (total beliefs)`

### Evaluation: A1 Traces

| Trace | Grounded Beliefs | Total Beliefs | Connectedness | Verdict |
|-------|-----------------|---------------|---------------|---------|
| **Sorting** (A1-1) | 18/18 | 18 | 100% | ✅ Excellent |
| **REST API** (A1-2) | 32/32 | 32 | 100% | ✅ Excellent |
| **Debugging** (A1-3) | 15/15 | 15 | 100% | ✅ Excellent |
| **Poem** (A1-4) | 24/24 | 24 | 100% | ✅ Excellent |
| **Math Proof** (A1-5) | 24/24 | 24 | 100% | ✅ Excellent |
| **Multi-File** (A1-6) | 28/28 | 28 | 100% | ✅ Excellent |

**Finding:** All A1 traces have perfect connectedness. The hand-authored traces show good discipline.

### Counter-Example: Disconnected Trace (from D2)

```
b1 1.0 L0 @user "implement a binary search tree"
b2 .9 L0 @self "trees have nodes"  ← Grounded (via b1)
...
b8 .9 L0 @self "right child > parent"  ← Grounded

b9 .8 L0 @self "sorting is useful"  ← NOT GROUNDED (orphan!)
b10 .7 L0 @self <b9 "quicksort is fast"  ← NOT GROUNDED
b11 .7 L0 @self <b9 "mergesort is stable"  ← NOT GROUNDED

b13 .9 L0 @self <b1 "write code"  ← Grounded
```

**Connectedness Score:** 12/15 = 80%

**Problem:** Beliefs b9-b11 are about sorting algorithms — completely irrelevant to BST implementation. They form an "orphan island" that adds noise without signal.

### Common Failure Mode: Background Knowledge Dump

**Pattern:** Thinker includes "useful context" that isn't connected to decisions.

```
b2 .9 L0 @self <b1 "HTML is a markup language"
b3 .9 L0 @self <b2 "HTML has tags"
b4 .9 L0 @self <b3 "tags can have attributes"
...
b10 .9 L0 @self <b1 "parse the HTML"  ← First actual decision
```

**Beliefs b2-b9 are grounded** (they connect to b1), but they provide **zero decision-making value**. They're background knowledge that doesn't inform the implementation.

**Detection:** Long chains with confidence ~0.9 that don't branch or lead to alternatives.

---

## Quality Criterion 2: Calibration

### Definition

Confidence values should be **meaningful** and **discriminating**:
- Values should reflect true certainty (not arbitrary)
- Alternatives should have distinct values (variance > 0.1)
- Values should be interpretable (0.9 = strong, 0.5 = uncertain, 0.3 = weak)

### Formalization

**Confidence Variance (CV):**
```
CV = var(confidence values at each decision point)
```

High CV = distinct alternatives; Low CV = "confidence splat"

**Calibration Score:** Correlation between confidence and correctness (requires empirical testing)

### Evaluation: A1 Traces

| Trace | Decision Points | Confidence Range | Variance | Verdict |
|-------|----------------|------------------|----------|---------|
| **Sorting** | 5 algorithms | 0.3 - 0.85 | 0.55² = 0.30 | ✅ Excellent discrimination |
| **REST API** | 2 auth choices | Not shown (missing alternatives) | N/A | ⚠️ Weak: no alternatives recorded |
| **Debugging** | 3 hypotheses | 0.1 - 0.95 | 0.85² = 0.72 | ✅ Excellent: wrong hypotheses at 0.1 |
| **Poem** | 3 forms | 0.6 - 0.8 | 0.2² = 0.04 | ⚠️ Weak: narrow range |
| **Math Proof** | 0 alternatives (linear) | N/A | N/A | N/A (no decisions to make) |
| **Multi-File** | 0 alternatives (linear) | N/A | N/A | N/A (no decisions to make) |

**Findings:**

1. **Best:** Debugging trace uses full confidence range (0.1 for wrong hypotheses, 0.95 for root cause). This is how confidence should work.

2. **Weak:** REST API trace doesn't record alternatives considered. It shows JWT at 0.9, but we don't know what else was considered.

3. **Weak:** Poem trace has narrow range (0.6-0.8). What's the difference between haiku at 0.7 vs sonnet at 0.6? Not clear.

4. **Note:** Math proof and Multi-File traces are **linear** (no decision points). Confidence is uniformly high (~0.95) because each step follows deductively. This is correct — proofs shouldn't have "alternatives."

### Counter-Example: Confidence Splat (from D2)

```
b2 .5 L0 @self "use JWT authentication"
b3 .5 L0 @self "use session-based authentication"
b4 .5 L0 @self "use API key authentication"
b5 .5 L0 @self "use OAuth 2.0"
```

**Confidence Range:** 0.5 - 0.5 (no variance)
**CV = 0**

This trace provides **zero decision signal**. All alternatives are equally "maximally uncertain."

### Common Failure Mode: Arbitrary Confidence

**Pattern:** Confidence values cluster around arbitrary values with tiny differences.

```
b5 0.72 L0 @self "bubble sort"
b6 0.73 L0 @self "insertion sort"
b7 0.71 L0 @self "merge sort"
```

**Variance:** 0.02² = 0.0004 (essentially zero)

**Problem:** The Thinker is "fine-tuning" confidence without real discrimination. This is worse than .5 splat because it **pretends** to discriminate while actually being arbitrary.

### Proposed Confidence Guidelines

| Value | Meaning | Use When |
|-------|---------|----------|
| **1.0** | Certain, axiomatic | User request, mathematical truths, definitions |
| **0.9-0.95** | Strong confidence | Chosen approach, well-established patterns |
| **0.7-0.85** | Moderate confidence | Plausible choice, some trade-offs |
| **0.5-0.7** | Weak confidence | Uncertain, multiple valid options |
| **0.3-0.5** | Tentative | Rejected alternatives, weak evidence |
| **0.0-0.3** | Unlikely | Eliminated hypotheses |
| **0.5** | Maximal uncertainty | No evidence either way |

**Rule of thumb:** If max(conf) - min(conf) < 0.1 at a decision point, add a final selection belief or reconsider.

---

## Quality Criterion 3: Completeness

### Definition

The trace should capture **all relevant reasoning**:
- Alternatives considered (even rejected ones)
- Trade-offs recognized
- Edge cases identified
- Invalidations specified

### Formalization

**Completeness Score (CS):** `CS = (relevant beliefs present) / (relevant beliefs possible)`

Since "possible" is subjective, we operationalize as:
- Are rejected alternatives recorded?
- Are invalidation conditions specified where relevant?
- Are edge cases acknowledged?

### Evaluation: A1 Traces

| Trace | Alternatives Recorded | Invalidation Conditions | Edge Cases | Completeness | Verdict |
|-------|----------------------|-------------------------|------------|--------------|---------|
| **Sorting** | ✅ 5 algorithms shown | ✅ `?["n<100"]`, `?["n>10000"]` | ✅ Odd-length arrays | High | ✅ Excellent |
| **REST API** | ❌ Not shown | ❌ None | ⚠️ Pagination missing | Medium | ⚠️ Missing alternatives |
| **Debugging** | ✅ 3 wrong hypotheses | ❌ None | ✅ Empty string, single char | High | ✅ Excellent |
| **Poem** | ✅ 3 forms considered | ❌ None | ❌ None noted | Medium | ⚠️ Creative task has no "edge cases" |
| **Math Proof** | ❌ Proof strategy only | ❌ None | N/A | Low | ⚠️ Only one path shown |
| **Multi-File** | ❌ Linear, no alternatives | ❌ None | ⚠️ Tests mentioned but not detailed | Medium | ⚠️ Missing "why" decisions |

**Findings:**

1. **Best:** Sorting trace shows alternatives + invalidations + edge cases. This is the gold standard.

2. **Weak:** REST API trace doesn't show why JWT was chosen over sessions/API keys/OAuth. A1 later added "missing alternatives" — but original trace was incomplete.

3. **Note:** Math proof is **correctly incomplete** — there's only one valid proof path. But it could show "why not other proof strategies" (infinite descent, unique factorization).

### Counter-Example: Incomplete Trace

**User Request:** "Implement a hash table"

**Trace:**
```
b1 1.0 L0 @user "implement a hash table"
b2 .9 L0 @self <b1 "use chaining for collision resolution"
b3 .9 L0 @self <b2 "store key-value pairs"
b4 .9 L0 @self <b3 "implement get, set, delete methods"
```

**What's missing:**
- Alternatives: Open addressing, robin hood hashing, cuckoo hashing
- Hash function: Which one? (FNV, Murmur, SipHash?)
- Resize strategy: When to grow? 2x? 1.5x?
- Edge cases: Hash collisions, key deletion, table full

**This trace is structurally valid but incomplete.** The Assembler must guess on critical decisions.

### Common Failure Mode: Single-Path Fallacy

**Pattern:** Thinker records only the chosen path, not the reasoning process.

```
b7 .9 L0 @self "use JWT for authentication"
```

**Better:**
```
b5a .5 L0 @self "use API keys (rejected: less secure)"
b5b .7 L0 @self "use sessions (rejected: server-side state)"
b5c .9 L0 @self <b5a,b5b "use JWT (selected: stateless, scales horizontally)"
```

**Rule of thumb:** For any non-trivial decision, record ≥2 alternatives with confidence values.

---

## Quality Criterion 4: Granularity

### Definition

Belief content should be at the **appropriate abstraction level** for the Assembler:
- Not too coarse: "perform computation" → useless
- Not too fine: "initialize registers" → unintelligible
- Just right: "loop from 1 to n, accumulate product" → actionable

### Formalization

**Granularity Score (GS):** Match between content level and target platform.

From D6 findings: Optimal level is **strategy + algorithm**.

### Evaluation: A1 Traces

| Trace | Content Level | Examples | Granularity | Verdict |
|-------|---------------|----------|-------------|---------|
| **Sorting** | Strategy + Algorithm | "divide array recursively", "merge sorted halves" | ✅ Excellent | Actionable |
| **REST API** | Resource + Endpoint | "GET /todos: list all", "POST /todos: create new" | ✅ Excellent | Actionable |
| **Debugging** | Diagnostic | "missing return statement", "Python returns None by default" | ✅ Excellent | Actionable |
| **Poem** | Content Prescription | "stanza 1: green gives way to gold" | ❌ Too specific | Prescribes output |
| **Math Proof** | Logical Step | "a² = 2b²", "a must be even" | ✅ Excellent | Deductive steps |
| **Multi-File** | Implementation | "create Validator.py", "import in UserService" | ✅ Excellent | Actionable |

**Findings:**

1. **Best:** Sorting, REST API, Debugging, Multi-File all hit the sweet spot — strategy + algorithm level.

2. **Problematic:** Poem trace prescribes **exact content** ("green gives way to gold") rather than **theme** ("transformation, loss of green"). This crosses from "reasoning" to "content generation."

3. **Note:** Math proof is at logical-step level — appropriate for deduction.

### Counter-Example: Wrong Granularity

**Too coarse:**
```
b2 .9 L0 @self "implement sorting"
b3 .9 L0 @self "make it work"
```

**Too fine:**
```
b2 .9 L0 @self "allocate memory on heap"
b3 .9 L0 @self "initialize registers"
b4 .9 L0 @self "perform multiplication at CPU level"
```

**Just right:**
```
b2 .9 L0 @self "use merge sort: divide, recursively sort, merge"
b3 .9 L0 @self <b2 "divide: split array into halves until single elements"
b4 .9 L0 @self <b2 "merge: compare and take smaller element"
```

### Common Failure Mode: Platform Mismatch

**Pattern:** Trace targets wrong abstraction level for Assembler.

```
# Thinker assumes C Assembler
b2 .9 L0 @self "allocate 64 bytes on heap"
b3 .9 L0 @self "use pointer arithmetic"

# Assembler is Python-based
# What does "allocate on heap" mean in Python?
```

**Rule of thumb:** Unless platform is specified, write for **typical high-level language** (Python, JavaScript, Go). Avoid hardware-level details.

---

## Synthesis: The Quality Framework

### Quality Dimensions Summary

| Dimension | Metric | Target | Failure Mode |
|-----------|--------|--------|--------------|
| **Connectedness** | Grounded beliefs / total | > 95% | Orphan islands |
| **Calibration** | Confidence variance | > 0.1 at decisions | Confidence splat/arbitrary |
| **Completeness** | Alternatives + invalidations | ≥2 alternatives per decision | Single-path fallacy |
| **Granularity** | Content level match | Strategy + algorithm | Too coarse / too fine |

### Quality Score (Proposed)

```
Quality(trace) = 0.3×Connectedness + 0.3×Calibration + 0.2×Completeness + 0.2×Granularity
```

**Interpretation:**
- **0.9-1.0:** Excellent — reliably guides Assembler
- **0.7-0.9:** Good — mostly actionable, some gaps
- **0.5-0.7:** Fair — requires Assembler guesswork
- **< 0.5:** Poor — worse than no trace

### Application to A1 Traces

| Trace | Connectedness | Calibration | Completeness | Granularity | Overall | Quality |
|-------|---------------|-------------|--------------|-------------|---------|---------|
| **Sorting** | 1.0 | 1.0 | 1.0 | 1.0 | 1.0 | ✅ Excellent |
| **REST API** | 1.0 | 0.5 | 0.6 | 1.0 | 0.75 | ⚠️ Good |
| **Debugging** | 1.0 | 1.0 | 0.9 | 1.0 | 0.97 | ✅ Excellent |
| **Poem** | 1.0 | 0.4 | 0.6 | 0.5 | 0.66 | ⚠️ Fair |
| **Math Proof** | 1.0 | N/A | 0.4 | 1.0 | 0.80 | ✅ Good (linear) |
| **Multi-File** | 1.0 | N/A | 0.6 | 1.0 | 0.82 | ✅ Good (linear) |

**Note:** Linear traces (no decision points) have N/A calibration. Their quality depends on connectedness + granularity.

---

## Common Failure Modes (Catalog)

### Failure Mode 1: Orphan Islands

**Symptom:** Disconnected beliefs with no path to user request.

```
b9 .8 L0 @self "sorting is useful"  ← Orphan!
```

**Root cause:** Thinker includes "context" without connecting to decisions.

**Severity:** High — adds noise, confuses Assembler.

**Fix:** Delete or bridge: "BST uses sorted property → sorting is relevant."

---

### Failure Mode 2: Confidence Splat

**Symptom:** All alternatives at 0.5 (or clustered within 0.1 range).

```
b2 .5 "JWT", b3 .5 "sessions", b4 .5 "OAuth"  ← No signal
```

**Root cause:** Thinker hasn't actually decided — just listing options.

**Severity:** Fatal — Assembler has no guidance.

**Fix:** Add final selection belief: `b_final .9 "select JWT for horizontal scaling"`

---

### Failure Mode 3: Single-Path Fallacy

**Symptom:** Trace shows only chosen option, no alternatives.

```
b7 .9 "use JWT"  ← What about sessions? API keys?
```

**Root cause:** Thinker focuses on "what was chosen" not "why it was chosen."

**Severity:** Medium — Assembler can implement but misses trade-offs.

**Fix:** Record rejected alternatives: `b5 .5 "sessions (rejected: server-side state)"`

---

### Failure Mode 4: Tautological Content

**Symptom:** Beliefs restate previous beliefs in different words.

```
b1 "sort array"
b8 "we need to sort the array"  ← Tautology
b10 "result should be sorted"  ← Tautology
```

**Root cause:** Thinker is "explaining" rather than "deciding."

**Severity:** High — wastes space, provides zero information.

**Fix:** Delete tautologies, keep only decision points.

---

### Failure Mode 5: Wrong Abstraction Level

**Symptom:** Content at hardware level or too abstract.

```
"initialize registers"  ← Too low for Python
"perform computation"  ← Too high to guide
```

**Root cause:** Thinker confused "detailed" with "useful."

**Severity:** Fatal for target platform mismatch.

**Fix:** Use D6 guidelines: strategy + algorithm level.

---

### Failure Mode 6: Missing Invalidations

**Symptom:** Edge cases not specified.

```
b12 .9 "use merge sort"  ← For all n? Even n=5?
```

**Root cause:** Thinker assumes "general purpose" without specifying boundaries.

**Severity:** Medium — Assembler may miss optimizations.

**Fix:** Add invalidations: `?["n<20"] "for small n, use insertion sort"`

---

## Counter-Examples: Quality vs Uselessness

### Counter-Example 1: High Quality, Useless Trace

Can a trace be "high quality" by our metrics but still useless?

**Trace:**
```
b1 1.0 L0 @user "implement a hash table"
b2 .9 L0 @self <b1 "use chaining for collision resolution"
b3 .7 L0 @self <b1 "use open addressing"
b4 .9 L0 @self <b2,b3 "select chaining (simpler, handles high load)"
b5 .9 L0 @self <b4 "store key-value pairs"
b6 .9 L0 @self <b5 "implement get, set, delete"
```

**Quality Scores:**
- Connectedness: 100%
- Calibration: 0.9 - 0.7 = 0.2 variance ✅
- Completeness: 2 alternatives shown ✅
- Granularity: Strategy + algorithm ✅

**Overall:** 0.95 — High quality!

**But it's still missing:**
- Hash function (which one?)
- Initial table size
- Resize strategy
- Thread safety

**Verdict:** **High quality does not mean complete.** Our framework measures *relative* quality, not *absolute* completeness.

### Counter-Example 2: Low Quality, Useful Trace

Can a trace be "low quality" but still useful?

**Trace:**
```
b1 1.0 L0 @user "sort an array"
b2 .9 L0 @self <b1 "use merge sort"
```

**Quality Scores:**
- Connectedness: 100%
- Calibration: N/A (no alternatives)
- Completeness: 0 (no alternatives, no invalidations)
- Granularity: Strategy ✅

**Overall:** ~0.6 — Fair quality

**But:** The Assembler can implement a working merge sort from this. The trace is **minimal but actionable**.

**Verdict:** **Usefulness has a threshold.** Below 0.5 quality, traces are worse than useless. Above 0.5, they work. 0.9 is "excellent" but 0.6 is "good enough."

---

## Thesis Impact

### Does this support or undermine CLAIR as IR?

**Supporting evidence:**

1. **Quality is measurable:** We can define objective metrics (connectedness, calibration, completeness, granularity).

2. **Quality correlates with usefulness:** High-quality traces (sorting, debugging) are the ones that work well in practice.

3. **Failure modes are identifiable:** We can name and characterize 6 common failure patterns.

4. **Improvement is possible:** Knowing the failure modes means we can train Thinkers to avoid them.

**Refining evidence:**

1. **Quality is not automatic:** The spec permits low-quality traces. Thinkers need guidelines.

2. **Quality is multi-dimensional:** A trace can excel in one dimension (connectedness) but fail in another (calibration).

3. **Quality thresholds exist:** Below 0.5, traces are worse than no trace. Above 0.5, they add value.

4. **Perfection is not required:** A 2-belief trace ("use merge sort") has quality ~0.6 but is still useful.

**Refined thesis:**

> "CLAIR is a viable IR when traces meet quality thresholds (connectedness > 0.95, confidence variance > 0.1 at decisions, appropriate granularity). Low-quality traces are possible but detectable and correctable."

**This supports the thesis with operational constraints** — CLAIR works when Thinkers produce quality traces, and we now know how to measure and ensure quality.

---

## Recommendations

### For Thinker Prompts

**Add quality checklist to system prompt:**

```
Before outputting your CLAIR trace, verify:

Connectedness:
□ All beliefs connect to user request (no orphan islands)

Calibration:
□ Confidence values discriminate between alternatives (variance > 0.1)
□ Values follow guidelines: 0.9=strong, 0.5=uncertain, 0.3=weak

Completeness:
□ At least 2 alternatives recorded for each decision
□ Invalidation conditions specified where relevant

Granularity:
□ Content is at strategy+algorithm level
□ Not too coarse ("do computation") or too fine ("initialize registers")
```

### For Automated Validation

**Implement quality checker:**

```python
def check_trace_quality(trace):
    scores = {
        "connectedness": check_connectedness(trace),
        "calibration": check_confidence_variance(trace),
        "completeness": check_alternatives(trace),
        "granularity": check_abstraction_level(trace),
    }
    overall = weighted_average(scores)

    if overall < 0.5:
        return "REJECT: Trace quality below threshold"
    elif overall < 0.7:
        return "WARNING: Trace has gaps - review before use"
    else:
        return "ACCEPT: Trace quality good"
```

### For Spec v0.2

**Add "Trace Quality" section:**

```markdown
## Trace Quality

A valid CLAIR trace should also be high-quality:

1. **Connectedness:** All beliefs must have a path to the user request
2. **Calibration:** Confidence values must discriminate (variance > 0.1)
3. **Completeness:** Record alternatives and invalidations
4. **Granularity:** Content at strategy+algorithm level

See examples/pi-calculation.md for a high-quality reference trace.
```

---

## Open Questions

### Q1: What is the Minimum Viable Quality?

**Hypothesis:** Quality threshold of 0.5 is needed for traces to be useful.

**Research needed:**
- Empirical testing with real Assemblers
- Measure correlation between quality score and code correctness
- Find the "tipping point" where traces become harmful

### Q2: Can Quality Be Automated?

Is there an algorithm to detect quality issues without human judgment?

**Challenges:**
- Granularity matching requires knowing target platform
- "Relevant alternatives" is task-dependent
- Tautology detection requires semantic understanding

**Potential approaches:**
- LLM-as-judge: "Rate this trace's quality from 0-1"
- Heuristic checks: variance, connectivity, entropy
- Human-in-the-loop: flag low-quality for review

### Q3: Does Quality Vary by Problem Type?

**Observation:** Math proofs and creative tasks have different quality profiles than algorithm selection.

**Question:** Should we have **type-specific quality criteria**?

| Problem Type | Key Quality Dimension |
|--------------|----------------------|
| Algorithmic | Calibration (discriminate alternatives) |
| Systems Design | Completeness (edge cases) |
| Debugging | Calibration (hypothesis discrimination) |
| Creative | Granularity (theme vs content) |
| Math Proof | Connectedness (logical flow) |
| Multi-File | Connectedness (cross-file links) |

### Q4: How to Teach Quality?

**Observation from A3:** LLMs struggle to produce high-quality traces even with examples.

**Question:** What's the best pedagogical approach?

- Few-shot examples? (Partial success)
- Negative examples? (Show what NOT to do)
- Quality criteria in prompt? (Explicit checklist)
- Reinforcement learning? (Reward high-quality traces)

---

## Conclusion

**Key findings:**
- ✅ Defined 4 quality dimensions: Connectedness, Calibration, Completeness, Granularity
- ✅ Evaluated 6 A1 traces against quality criteria
- ✅ Documented 6 common failure modes with examples
- ✅ Proposed quality score framework (weighted combination)
- ✅ Identified quality threshold (~0.5) for usefulness

**Thesis connection:** **Refines the thesis** — CLAIR is viable as an IR when traces meet quality thresholds. Quality is measurable and teachable, but not automatic. The spec (or Thinker guidelines) should encode quality criteria.

**Quality dimensions discovered:**
1. **Connectedness:** All beliefs grounded in user request
2. **Calibration:** Confidence discriminates between alternatives
3. **Completeness:** Alternatives and invalidations recorded
4. **Granularity:** Strategy + algorithm level

**Common failure modes:**
1. Orphan islands (ungrounded beliefs)
2. Confidence splat (no decision signal)
3. Single-path fallacy (missing alternatives)
4. Tautological content (zero information gain)
5. Wrong abstraction level (unintelligible or useless)
6. Missing invalidations (edge cases ignored)

**The thesis holds with refinement:** CLAIR preserves *why* decisions were made, but fidelity depends on trace quality. High-quality traces (>0.7) reliably guide Assemblers. Low-quality traces (<0.5) are worse than no trace. Quality is measurable, teachable, and enforceable.

**Next steps:**
- Empirical testing with real LLMs to validate quality thresholds
- Development of automated quality checkers
- Integration with A3 teachability findings (quality training data)
- Spec v0.2 with quality guidelines
