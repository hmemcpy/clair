# A4: Confidence Calibration Challenge

## Research Question

Are Thinker-assigned confidence values meaningful? Do they correlate with actual correctness? This exploration tests whether confidence values in CLAIR tracks are **informative signals** or **decorative noise**. For CLAIR to be viable as an IR, confidence must be calibrated — high confidence should predict correctness, low confidence should predict error.

**Thesis Connection:** If confidence values are uncorrelated with correctness, CLAIR loses its core differentiator. The confidence algebra (proven in Lean) assumes meaningful inputs — garbage in, garbage out. This exploration tests whether real LLMs can produce calibrated confidence.

**Validation Criteria:**
- ≥3 problems with known ground truth for calibration testing
- Analysis of confidence vs correctness correlation
- Counter-examples: when confidence misleads
- Connection to thesis (supports, undermines, or refines)
- Open questions for future work

---

## Background: What is Calibration?

### Definition

**Calibration** = Agreement between expressed confidence and actual correctness.

| Expressed Confidence | Actual Correctness | Calibration Status |
|---------------------|-------------------|-------------------|
| 0.9 (high) | Correct (90%+) | ✅ Well-calibrated |
| 0.9 (high) | Correct (50%) | ❌ Overconfident |
| 0.3 (low) | Correct (30%) | ✅ Well-calibrated |
| 0.3 (low) | Correct (80%) | ❌ Underconfident |

### Why It Matters for CLAIR

CLAIR's value proposition depends on confidence:
- **Alternative selection:** Assembler chooses highest-confidence option
- **Invalidation conditions:** Triggers based on confidence thresholds
- **Information loss:** Assembler might filter low-confidence branches
- **Quality metrics:** A2's "Calibration" dimension measures variance

If confidence is arbitrary, these mechanisms fail.

---

## Test 1: Algorithm Selection (Calibration by Design)

### Experimental Design

**Problem:** "Sort an array of integers in ascending order"

**Ground truth:** We know which algorithms are actually better for which inputs.

**Hypothesis:** A well-calibrated Thinker should assign:
- Low confidence (0.3-0.5) to inefficient algorithms (bubble sort for large n)
- High confidence (0.8-0.95) to appropriate algorithms (merge sort for general case)

### Trace from A1 (Hand-Authored)

```clair
; === ALGORITHM SELECTION ===
b5 .3 L0 @self <b2 "bubble sort: O(n²) but simple"
b6 .5 L0 @self <b2 "insertion sort: O(n²), good for small n"
b7 .6 L0 @self <b2 "merge sort: O(n log n), stable, needs extra space"
b8 .7 L0 @self <b2 "quick sort: O(n log n) average, O(n²) worst, unstable"
b9 .8 L0 @self <b2 "heap sort: O(n log n), unstable, in-place"
b10 .85 L0 @self <b2 ?["n<100"] "use insertion sort (simple and fast for small arrays)"
b11 .75 L0 @self <b2 ?["language has built-in sort"] "use language's built-in sort (Timsort, usually)"
b12 .7 L0 @self <b2,b10,b11 "for general purpose: implement merge sort for clarity and stability"
```

### Calibration Analysis

**Are these confidence values meaningful?**

| Algorithm | Confidence | Actual Quality (for general case) | Calibration |
|-----------|------------|-----------------------------------|-------------|
| Bubble sort (b5) | 0.3 | Poor: O(n²), rarely optimal | ✅ Well-calibrated |
| Insertion sort (b6) | 0.5 | Poor for large n, good for small n | ✅ Well-calibrated |
| Merge sort (b7) | 0.6 | Good: O(n log n), stable | ⚠️ Underconfident (should be 0.8+) |
| Quick sort (b8) | 0.7 | Good average, risky worst case | ✅ Well-calibrated |
| Heap sort (b9) | 0.8 | Good: O(n log n), in-place | ✅ Well-calibrated |
| Insertion (small n) (b10) | 0.85 | Excellent for n<100 | ✅ Well-calibrated |
| Built-in sort (b11) | 0.75 | Usually excellent | ✅ Well-calibrated |
| Merge sort (final) (b12) | 0.7 | Good choice | ⚠️ Lower than b9, b10, b11 |

**Issue:** The final selection (b12) has confidence 0.7, but it's justified by beliefs with confidence 0.6-0.75. This violates the confidence algebra: `conf(b12) should ≤ min(conf(b7), conf(b10), conf(b11)) = min(0.6, 0.85, 0.75) = 0.6`.

But b12 has confidence 0.7 > 0.6. This is **invalid per the spec**.

**Verdict:** Hand-authored traces can have **calibration errors**. The confidence values are intuitively correct (bubble sort = bad), but the algebra isn't consistently applied.

### Counter-Example: What If Confidence Was Arbitrary?

**Uncalibrated trace:**
```clair
b5 .9 L0 @self "bubble sort: simple and works"
b6 .85 L0 @self "insertion sort: good name"
b7 .5 L0 @self "merge sort: complicated"
```

**Assembler behavior:** Chooses bubble sort (0.9 confidence).

**Actual outcome:** O(n²) performance disaster for large arrays.

**This is worse than no trace** — the trace confidently led the Assembler astray.

---

## Test 2: Mathematical Truth (Binary Calibration)

### Experimental Design

**Problem:** "Prove that the square root of 2 is irrational"

**Ground truth:** Mathematical proof has binary correctness — each step either follows or doesn't.

**Hypothesis:** Mathematical reasoning should have high confidence (0.9+) for correct steps, low confidence (0.0-0.3) for wrong paths.

### Trace from A1

```clair
; === PROOF CONSTRUCTION ===
; Step 1: Assume sqrt(2) is rational
b8 .95 L0 @self <b6 "assume sqrt(2) = a/b where a,b are integers with no common factors"

; Step 2: Square both sides
b9 .95 L0 @self <b8 "2 = a²/b² (multiply both sides by b²)"
b10 .95 L0 @self <b9 "a² = 2b² (multiply both sides by b²)"

; Step 3: Analyze parity
b11 .95 L0 @self <b10 "a² is even (equals 2 times something)"
b12 .95 L0 @self <b11 "a is even (if a² is even, a must be even)"

; ... (all steps at 0.95)
```

### Calibration Analysis

**Observation:** All steps at 0.95 confidence.

**Is this calibrated?**

| Confidence | Interpretation | Actual Correctness | Verdict |
|------------|----------------|-------------------|---------|
| 0.95 | "95% sure this follows" | 100% certain (it's a proof) | ⚠️ Underconfident |
| | | | **Mathematical certainty ≠ 0.95** |

**Issue:** In mathematics, if a step follows, it follows with **probability 1.0**. Using 0.95 suggests uncertainty where there is none.

**Alternative interpretation:** 0.95 might mean "95% sure I haven't made a mistake" — but that's meta-confidence (confidence in my reasoning), not confidence in the proposition itself.

### Counter-Example: Overconfidence in Math

**Wrong proof with high confidence:**
```clair
b8 .95 L0 @self "assume sqrt(2) = a/b"
b9 .95 L0 @self <b8 "therefore 2 = a/b"  ← WRONG (forgot to square)
b10 .95 L0 @self <b9 "therefore a = 2b"  ← Compounding error
b11 .95 L0 @self <b10 "therefore sqrt(2) = 2"  ← Nonsense conclusion
```

This trace is **structurally valid** but **factually wrong**. All beliefs at 0.95 confidence.

**The confidence algebra cannot catch this** — the structure is fine, the content is wrong.

**Verdict:** Confidence calibration is **necessary but not sufficient**. A well-calibrated trace about nonsense is still nonsense.

---

## Test 3: Hypothesis Elimination (Debugging)

### Experimental Design

**Problem:** "This code returns None instead of reversed string. What's wrong?"

**Ground truth:** We know the bug (missing return statement).

**Hypothesis:** Wrong hypotheses should have low confidence (0.1-0.3). Correct hypothesis should have high confidence (0.9+).

### Trace from A1

```clair
; === ALTERNATIVE EXPLANATIONS CONSIDERED ===
b13 .1 L0 @self <b1 "result variable is None" → eliminated
b14 .1 L0 @self <b1 "string concatenation fails" → eliminated
b15 .1 L0 @self <b1 "loop doesn't execute" → eliminated

; === ROOT CAUSE ===
b7 .95 L0 @self <b6 "root cause: missing 'return result' at end of function"
```

### Calibration Analysis

**Are these confidence values meaningful?**

| Hypothesis | Confidence | Correctness | Calibration |
|------------|------------|-------------|-------------|
| "result is None" | 0.1 | Wrong (b2 shows result initialized) | ✅ Well-calibrated |
| "concatenation fails" | 0.1 | Wrong (b4 shows correct logic) | ✅ Well-calibrated |
| "loop doesn't execute" | 0.1 | Wrong (b3 shows loop works) | ✅ Well-calibrated |
| "missing return" | 0.95 | Correct | ✅ Well-calibrated |

**This is excellent calibration!** The Thinker assigned low confidence to wrong hypotheses and high confidence to the correct one.

**Why this works:**
- Wrong hypotheses are **explicitly falsified** by evidence (b2 shows initialization, so "result is None" is wrong)
- Low confidence (0.1) reflects "ruled out by evidence"
- High confidence (0.95) reflects "supported by multiple lines of evidence"

**This is how calibration should work in CLAIR.**

---

## Test 4: Subjective Judgment (Creative Tasks)

### Experimental Design

**Problem:** "Write a poem about autumn"

**Ground truth:** None — there's no "correct" poem.

**Hypothesis:** Creative tasks should have **lower confidence overall** (0.6-0.8) because there's no objective truth.

### Trace from A1

```clair
; === ARTISTIC CHOICES ===
b6 .7 L0 @self <b4 "haiku: 5-7-5 syllables, very concise"
b7 .6 L0 @self <b4 "sonnet: 14 lines, rhyme scheme, formal structure"
b8 .8 L0 @self <b4 "free verse: no constraints, more expressive"
b9 .75 L0 @self <b6,b7,b8 "use free verse for flexibility"
```

### Calibration Analysis

**Problem:** What does "0.8 confidence" mean for "use free verse"?

This is not a truth-apt proposition. It's a **preference**, not a fact.

| Confidence | Interpretation | Problem |
|------------|----------------|---------|
| 0.8 "free verse is better" | 80% sure free verse is best | Best by what metric? |
| | | There's no ground truth to calibrate against |

**Verdict:** **Calibration is undefined for subjective judgments.**

**Workaround:** Frame subjective choices as **objective constraints**:
```clair
b8 .9 L0 @self <b1 "user didn't specify form → free verse allows maximum flexibility"
```

Now 0.9 means "90% sure this follows from user's unspecified requirements" — which is calibratable.

---

## Experiment Design: Testing Real LLM Calibration

### Setup

To test whether real Thinker LLMs can produce calibrated confidence, we need:

1. **Problems with verifiable correctness:**
   - Code execution: does the code work?
   - Unit tests: do tests pass?
   - Mathematical proof: is each step valid?
   - Bug diagnosis: is the identified bug actually the bug?

2. **Multiple trials:** Same problem solved 10+ times to see if confidence correlates with success rate.

3. **Comparison conditions:**
   - Zero-shot: LLM assigns confidence without guidance
   - With guidelines: LLM follows confidence scale (0.9=strong, 0.5=uncertain, 0.3=weak)
   - With feedback: LLM sees outcomes and adjusts

### Proposed Experiment: Algorithm Quiz

**Format:** Present Thinker with 10 programming problems and 3 algorithm choices each. Ask for confidence in each choice.

**Example problem:**
```
Problem: "Find shortest path between two nodes in a weighted graph with 10,000 nodes and 100,000 edges."

Choices:
A) Dijkstra's algorithm
B) Bellman-Ford algorithm
C) Depth-first search

Assign confidence to each choice.
```

**Ground truth:**
- Dijkstra: Correct for non-negative weights (0.9 if that's the case)
- Bellman-Ford: Only needed for negative weights (0.3 unless specified)
- DFS: Wrong (doesn't find shortest path) (0.1)

**Calibration metric:**
```
Calibration Score = 1 - |confidence - correctness|

Perfect calibration: Score = 1.0
Random guessing: Score = 0.5
Anti-calibrated: Score = 0 (high confidence on wrong answers)
```

---

## Counter-Examples: When Confidence Misleads

### Counter-Example 1: High Confidence, Wrong Answer

**Trace:**
```clair
b1 1.0 L0 @user "implement binary search for sorted array"
b2 .9 L0 @self <b1 "use mid = (left + right) / 2"
b3 .9 L0 @self <b2 "this works for all array sizes"
```

**Problem:** `(left + right) / 2` overflows for large arrays (left + right > INT_MAX).

**Correct formula:** `mid = left + (right - left) / 2`

**Confidence:** 0.9 (high)
**Correctness:** Wrong (for large arrays)

**This is overconfidence.** The Thinker didn't consider edge cases.

**Fix:** Invalidation condition
```clair
b2 .9 L0 @self <b2 ?["array size < 2^30"] "use mid = (left + right) / 2"
b3 .9 L0 @self <b2 ?["array size >= 2^30"] "use mid = left + (right - left) / 2"
```

Now the confidence is **conditioned** on array size.

---

### Counter-Example 2: Low Confidence, Right Answer

**Trace:**
```clair
b1 1.0 L0 @user "sort 10 integers"
b2 .3 L0 @self <b1 "use bubble sort"
```

**Confidence:** 0.3 (low)
**Correctness:** Correct (for 10 integers, bubble sort is fine)

**This is underconfidence.** The algorithm is appropriate for the input size.

**Why:** The Thinker calibrated bubble sort against "general case" (large n) rather than the specific problem (n=10).

**Fix:** Context-aware confidence
```clair
b2 .8 L0 @self <b1 ?["n=10"] "use bubble sort (simple and fast for small arrays)"
```

---

### Counter-Example 3: Confidence Inflation Through Derivation

**Trace:**
```clair
b1 .9 L0 @self "X is true"
b2 .8 L0 @self <b1 "Y follows from X"
b3 .7 L0 @self <b2 "Z follows from Y"
```

**Per the confidence algebra:**
- `conf(b2) should be ≤ conf(b1) = 0.9` ✅ (0.8 ≤ 0.9)
- `conf(b3) should be ≤ conf(b2) = 0.8` ✅ (0.7 ≤ 0.8)

**But:** What if b1 is wrong? If X is false (conf(b1) should have been 0.1), then b2 and b3 are also wrong.

**Confidence can compound errors.** A high-confidence mistake propagates.

**Mitigation:** The Löb discount for meta-beliefs prevents bootstrapping, but doesn't prevent initial errors.

---

## Analysis: Is Confidence Calibratable?

### What Works

1. **Hypothesis elimination (debugging):** Low confidence on falsified alternatives works well.

2. **Algorithm comparison:** Relative confidence (bubble sort 0.3 < merge sort 0.8) is meaningful.

3. **Binary truth (math):** 0.95+ for deductive steps, 0.1- for eliminated hypotheses.

### What Doesn't Work

1. **Subjective judgments:** "Free verse is better" has no ground truth.

2. **Edge case awareness:** High confidence might miss overflow bugs, null cases.

3. **Derivation chains:** Errors compound; high confidence early leads to high confidence later even if wrong.

### The Calibration Spectrum

| Problem Type | Calibratable? | Reason |
|--------------|---------------|--------|
| Algorithm selection | ✅ Yes | Objective performance metrics |
| Bug diagnosis | ✅ Yes | Hypotheses falsifiable by evidence |
| Mathematical proof | ✅ Yes (binary) | Steps either follow or don't |
| API design | ⚠️ Partial | Some choices are preference-based |
| Creative tasks | ❌ No | No ground truth |
| "Will this code work?" | ⚠️ Hard | Requires exhaustive testing |

---

## Thesis Impact

### Does This Support or Undermine CLAIR as IR?

**Supporting evidence:**

1. **Calibration is achievable:** Debugging and algorithm selection traces show meaningful confidence discrimination.

2. **Confidence algebra works:** When applied correctly, confidence decreases through derivation chains (as proven in Lean).

3. **Low confidence on wrong paths:** 0.1-0.3 for eliminated hypotheses is semantically correct.

**Refining evidence:**

1. **Calibration is not automatic:** Hand-authored traces have errors (merge sort at 0.6, final selection at 0.7 > justified).

2. **Calibration requires ground truth:** Without verifiable correctness, confidence is arbitrary.

3. **Edge cases are hard:** High confidence doesn't guarantee edge case awareness.

4. **Subjective domains resist calibration:** Creative tasks have no objective basis for confidence.

**Refined thesis:**

> "CLAIR confidence values are meaningful when: (1) the domain has objective correctness criteria, (2) alternatives are comparable, and (3) the Thinker is aware of edge cases. In subjective domains or for problems requiring exhaustive testing, confidence may be uncalibrated and should be treated with caution."

**This refines the thesis** — CLAIR is viable as an IR, but confidence is not universally meaningful. Assemblers should:
- Trust high confidence (0.9+) for algorithmic and diagnostic reasoning
- Be skeptical of high confidence for creative tasks
- Use invalidation conditions to handle edge cases

---

## Recommendations

### For Thinker Training

**Confidence calibration guidelines:**

```
When assigning confidence:

1. Start from objective criteria:
   - 0.9-1.0: Mathematically certain, proven correct
   - 0.7-0.9: Well-supported by evidence, standard practice
   - 0.5-0.7: Plausible but not certain, multiple valid options
   - 0.3-0.5: Weak evidence, significant trade-offs
   - 0.0-0.3: Ruled out by evidence, known to be wrong

2. Apply the confidence algebra:
   - Derivation: conf(child) ≤ min(conf(parents))
   - Alternatives: Ensure variance > 0.1

3. For subjective judgments:
   - Use 0.6-0.8 range (acknowledge preference)
   - Frame as "follows from requirements" not "is objectively best"

4. Always consider edge cases:
   - Add invalidation conditions
   - Reduce confidence if edge cases are unknown
```

### For Automated Validation

**Calibration checker:**

```python
def check_calibration(trace):
    issues = []

    # Check derivation chains
    for belief in trace.beliefs:
        for parent in belief.justifications:
            if belief.confidence > parent.confidence:
                issues.append(f"{belief.id}: confidence {belief.confidence} > parent {parent.id} confidence {parent.confidence}")

    # Check decision variance
    for decision_group in trace.group_by_justification():
        confs = [b.confidence for b in decision_group]
        if max(confs) - min(confs) < 0.1:
            issues.append(f"Low variance at decision point: {confs}")

    # Check subjective domains
    if trace.task_type == "creative":
        for belief in trace.beliefs:
            if belief.confidence > 0.85:
                issues.append(f"{belief.id}: confidence {belief.confidence} in subjective domain")

    return issues
```

### For Spec v0.2

**Add calibration section:**

```markdown
## Confidence Calibration

Confidence values should be calibrated to actual correctness:

| Value | Meaning | Use Domain |
|-------|---------|------------|
| 0.9-1.0 | Certain | Math, logic, proven facts |
| 0.7-0.9 | Strong | Algorithmic, diagnostic, evidence-supported |
| 0.5-0.7 | Moderate | Design choices, preferences |
| 0.3-0.5 | Weak | Unproven, speculative |
| 0.0-0.3 | Wrong | Ruled out, falsified |

**Calibration rules:**
1. conf(child) ≤ min(conf(parents)) — derivation never increases confidence
2. Decision variance > 0.1 — alternatives must be distinguishable
3. Reduce confidence for unknown edge cases
4. In subjective domains, use 0.6-0.8 range
```

---

## Open Questions

### Q1: Can LLMs Learn Calibration from Feedback?

**Experiment:** Train Thinker on problems with known outcomes, adjust confidence based on success/failure.

**Hypothesis:** Calibration is learnable.

**Challenge:** Requires large dataset of (problem, reasoning, outcome) triples.

### Q2: What's the Minimum Calibratable Domain?

**Observation:** Algorithm selection is calibratable. Poetry is not.

**Question:** What's the boundary? Is API design calibratable? System architecture? UI design?

**Hypothesis:** Calibratable domains have **objective optimization criteria** (time complexity, correctness). Non-calibratable domains have **subjective optimization criteria** (aesthetics, user preference).

### Q3: How to Handle "Unknown Unknowns"?

**Problem:** Thinker assigns high confidence (0.9) to a solution, but doesn't know about an edge case that makes it wrong.

**Example:** `(left + right) / 2` for binary search — works until array size > 2^30.

**Solution approaches:**
1. **Defensive confidence:** Reduce confidence for "complex" code
2. **Invalidation conditions:** Explicitly call out known edge cases
3. **Confidence ranges:** "0.9 for array size < 2^30, 0.5 otherwise"

Which approach is best? None are fully satisfactory.

### Q4: Should Confidence Be Probabilistic or Ordinal?

**Current model:** Probabilistic (0.9 = 90% likely correct)

**Alternative:** Ordinal (0.9 = "more confident than 0.8")

**Question:** Does the specific value matter, or only the ranking?

**Evidence:** For alternative selection, ranking matters (choose highest). For derivation chains, values matter (confidence algebra).

**Hybrid:** Use values for derivation, ranking for selection.

---

## Conclusion

**Key findings:**

- ✅ Calibration is achievable in objective domains (algorithmic, diagnostic, mathematical)
- ✅ Low confidence on falsified hypotheses (0.1-0.3) is semantically correct
- ✅ Relative confidence (0.3 < 0.8) is meaningful for alternative selection
- ⚠️ Calibration is not automatic — hand-authored traces have errors
- ⚠️ Edge cases are hard — high confidence doesn't guarantee correctness
- ❌ Subjective domains resist calibration — no ground truth for aesthetic judgment

**Thesis connection:** **Refines the thesis** — CLAIR confidence values are meaningful when the domain has objective correctness criteria and the Thinker is aware of edge cases. In subjective domains, confidence should be treated as preference strength, not correctness probability.

**Calibration principles discovered:**
1. **Derivation decreases confidence:** conf(child) ≤ min(conf(parents))
2. **Decision variance:** Alternatives must differ by > 0.1
3. **Domain dependence:** Calibration works for algorithmic/diagnostic, fails for creative
4. **Edge case sensitivity:** High confidence without edge case awareness = overconfidence

**The thesis holds with refinement:** CLAIR preserves *why* decisions were made, but confidence calibration requires:
1. Objective correctness criteria in the domain
2. Thinker awareness of edge cases
3. Adherence to confidence algebra
4. Lower confidence ranges for subjective judgments

**Next steps:**
- Empirical testing with real LLMs to measure calibration accuracy
- Development of calibration checkers (automated validation)
- Confidence training data for Thinker models
- Spec v0.2 with calibration guidelines

---

## Examples Summary

| Example | Confidence Range | Calibration | Verdict |
|---------|------------------|-------------|---------|
| Sorting algorithms | 0.3 - 0.85 | ✅ Well-calibrated | Relative confidence meaningful |
| Debugging hypotheses | 0.1 - 0.95 | ✅ Excellent | Low conf on wrong, high on correct |
| Math proof | All 0.95 | ⚠️ Underconfident | Should be 1.0 for deductive steps |
| Poetry form choice | 0.6 - 0.8 | ❌ Undefined | Subjective preference |
| Binary search overflow | 0.9 | ❌ Overconfident | Missed edge case |
| Small array bubble sort | 0.3 | ❌ Underconfident | Appropriate for n=10 |

**Calibration is achievable but requires discipline.** CLAIR is viable as an IR when Thinkers follow calibration guidelines and domains have objective correctness criteria.
