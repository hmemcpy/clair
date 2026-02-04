# S2: Refined Spec Recommendations

**Date:** 2026-02-04

**Status:** COMPLETED

**Purpose:** Synthesize spec refinements from 23 explorations into actionable recommendations for CLAIR v0.2.

---

## Executive Summary

Based on the viability assessment in S1, the CLAIR spec requires refinements in 4 areas:
1. **Multi-justification semantics** — clarify how `<b1,b2>` combines confidence
2. **Trace quality guidelines** — add usefulness criteria beyond structural validity
3. **Content clarity guidelines** — mitigate opacity and ambiguity
4. **Operational constraints** — stratification, evaluation order, confidence operations

---

## Part 1: Multi-Justification Semantics

### 1.1 Problem (from D4, R1)

The current syntax `<b1,b2>` doesn't specify how confidences combine:
- Conjunction (both required) → multiplication bound: `conf ≤ conf(b1) × conf(b2)`
- Disjunction (either sufficient) → oplus aggregation: `conf = conf(b1) ⊕ conf(b2)`
- Weakest link → min bound: `conf ≤ min(conf(b1), conf(b2))`

### 1.2 Recommendation

Add explicit justification semantics to the grammar:

```markdown
## Justification Semantics

A belief can have multiple justifications with different combination semantics:

### Conjunction (AND)
```
b_id confidence L0 @source <(b1 ∧ b2) "content"
```
**Confidence bound:** `conf(b_id) ≤ conf(b1) × conf(b2) × inference_conf`

**Use when:** The belief requires ALL justifications to be true.
**Example:** "Use merge sort AND it's stable AND it's O(n log n)"

### Disjunction (OR)
```
b_id confidence L0 @source <(b1 ∨ b2) "content"
```
**Confidence aggregation:** `conf(b_id) = conf(b1) ⊕ conf(b2)`

**Use when:** The belief is supported by ANY justification (independent evidence).
**Example:** "Bug suggested by test failure OR code review"

### Weakest Link
```
b_id confidence L0 @source <min(b1, b2) "content"
```
**Confidence bound:** `conf(b_id) ≤ min(conf(b1), conf(b2))`

**Use when:** The belief is no stronger than its weakest justification.
**Example:** "Result is bounded by least-confident input"

### Default (backward compatible)
```
b_id confidence L0 @source <b1,b2 "content"
```
**Semantics:** Treat as conjunction if not specified.

**Note:** In v0.1 traces without explicit semantics, default to conjunction.
```

### 1.3 Rationale

- **Backward compatible:** Old traces (`<b1,b2>`) still parse, default to conjunction
- **Explicit:** New syntax makes semantics clear
- **Flexible:** Supports all three combination modes identified in D4

---

## Part 2: Trace Quality Guidelines

### 2.1 Problem (from D2)

Structural validity (grammar, acyclicity, confidence bounds) is necessary but not sufficient. Traces can be valid yet useless (tautologies, confidence splat, disconnected DAGs).

### 2.2 Recommendation

Add new section to spec:

```markdown
## Trace Quality

A valid CLAIR trace should also be **useful** to an Assembler.

### Quality Criteria

#### 1. Information Gain (IG)
Each belief should provide **non-derivable information** relative to its justifications.

**Bad (tautology):**
```
b1 1.0 L0 @user "sort an array"
b2 1.0 L0 @self <b1 "we need to sort the array"  # No new information
```

**Good:**
```
b1 1.0 L0 @user "sort an array"
b2 .9 L0 @self <b1 "use merge sort for O(n log n) complexity"  # Adds information
```

**Test:** Can a reader predict belief content given only its justifications? If yes, IG ≈ 0.

#### 2. Decision Discriminance (DD)
Use confidence to **rank alternatives**, not list them neutrally.

**Bad (confidence splat):**
```
b2 .5 L0 @self "use JWT authentication"
b3 .5 L0 @self "use session-based authentication"  # No signal
b4 .5 L0 @self "use OAuth 2.0"  # No signal
```

**Good:**
```
b2 .85 L0 @self "use JWT authentication"  # Preferred
b3 .4 L0 @self "use session-based authentication"  # Rejected
b4 .6 L0 @self "use OAuth 2.0"  # Backup option
```

**Test:** For any decision point, are confidence values distinct? Variance > 0.

#### 3. Grounding Connectivity (GC)
All beliefs should **connect to the user request** through justification chains.

**Bad (disconnected islands):**
```
b1 1.0 L0 @user "implement a BST"
b2 .9 L0 @self "trees have nodes"  # No path to implementation
b13 .9 L0 @self <b1 "write code"  # No connection to theory
```

**Good:**
```
b1 1.0 L0 @user "implement a BST"
b2 .9 L0 @self <b1 "BST property: left < node < right"
b3 .9 L0 @self <b2 "insert: compare and recurse left or right"
```

**Test:** Does a path exist from each belief to the user request?

#### 4. Actionability (AC)
Content should be at **appropriate abstraction level** for the Assembler.

**Bad (too high):**
```
b2 .9 L0 @self "perform computation"  # Too vague to implement
```

**Bad (too low):**
```
b2 .9 L0 @self "initialize registers, set up stack frame"  # Irrelevant for Python
```

**Good:**
```
b2 .9 L0 @self "iterate k from 0 until precision reached, accumulate terms"
```

**Test:** Can an LLM Assembler convert this to code without guessing?

### Minimal Useful Trace Example

```clair
b1 1.0 L0 @user "add two numbers"
b2 1.0 L0 @self <b1 "input: two numbers (a, b)"
b3 1.0 L0 @self <b1 "output: their sum (a + b)"
b4 1.0 L0 @self <b2,b3 "implement: return a + b"
```

This trace is minimal (4 beliefs) but useful:
- IG: High (b4 adds "return a + b" not derivable from b2, b3)
- DD: N/A (only one approach)
- GC: All beliefs connect to b1
- AC: "return a + b" is actionable for any Assembler
```

### 2.3 Validation Tooling

Recommend adding a `--quality` flag to validation:
```bash
clair-validator trace.clair --quality
```
Outputs:
- Information gain score (per belief and average)
- Confidence variance (for decision points)
- Connectivity check (orphan beliefs)
- Actionability check (too vague/too specific warnings)

---

## Part 3: Content Clarity Guidelines

### 3.1 Problem (from D3, D6)

Content opacity causes ambiguity: "sort" can mean numeric, alphabetical, or custom key sorting. Identical content means different things in different contexts.

### 3.2 Recommendation

Add new section to spec:

```markdown
## Content Guidelines

Belief content should be **specific, explicit, and committed**.

### 1. Be Specific About Types

**Bad:**
```
b2 .9 L0 @self <b1 "sort the items"
```

**Good:**
```
b2 .9 L0 @self <b1 "sort integers ascending (smallest to largest)"
```
OR
```
b2 .9 L0 @self <b1 "sort strings alphabetically"
```

### 2. Be Explicit About Algorithms

**Bad:**
```
b5 .8 L0 @self <b2 "delete: find replacement (successor or predecessor)"
```

**Good (explain-then-name):**
```
b5 .8 L0 @self <b2 "delete: find smallest in right subtree (called 'successor')"
b6 .8 L0 @self <b5 "find smallest: go right once, then go left until leaf"
```

### 3. Avoid Vague Terms

**Bad:**
```
b2 .9 L0 @self <b1 "use caching"
```

**Good:**
```
b2 .9 L0 @self <b1 "use memoization: cache results keyed by input parameters"
b3 .9 L0 @self <b2 "use functools.lru_cache decorator"
```

### 4. Commit to Decisions (Avoid "Or")

**Bad:**
```
b17 .85 L0 @self <b16 "modify in-place or return new array"
```

**Good:**
```
b17 .85 L0 @self <b16 ?["memory-constrained"] "modify in-place to save memory"
```
OR
```
b17b .9 L0 @self <b16 ?["functional-preferred"] "return new array (functional style, avoids mutation)"
```

### 5. Use Explicit Error Strategies

**Bad:**
```
b7 .5 L0 @self "need error handling"
```

**Good:**
```
b7 .9 L0 @self <b6 "network calls may fail due to timeout or connection refused"
b8 .85 L0 @self <b7 "on network failure: retry up to 3 times with exponential backoff"
b9 .9 L0 @self <b8 "after 3 failures: return error to caller"
```

### 6. Target "Strategy + Algorithm" Abstraction Level

**Too vague (intent):**
```
b5 .6 L0 @self "need iteration over k"
```

**Too specific (pseudocode):**
```
b5 .9 L0 @self "for k in range(n): sum += (-1)**k * factorial(6*k) / denominator"
```

**Just right (natural algorithm):**
```
b5 .9 L0 @self <b4 "iterate k from 0 until precision reached"
b6 .9 L0 @self <b5 "for each k, compute term and add to running sum"
```

### Acceptable Prescriptiveness

**Mathematical formulas** are inherently prescriptive and acceptable:
```
b14 .9 L0 @self <b12 "π = 426880 × √10005 / sum"
```

**Low-level operations** with no abstraction are acceptable:
```
b5 .9 L0 @self "set bit 3 to 1, clear bit 5, preserve others"
```
```

---

## Part 4: Operational Constraints

### 4.1 Evaluation Order (from D4)

**Problem:** Non-distributivity means `a × (b ⊕ c) ≠ (a × b) ⊕ (a × c)`. Need canonical order.

**Recommendation:**
```markdown
## Confidence Evaluation Order

When computing confidence bounds for a belief:

1. **First:** Compute all ⊕ aggregations (combine independent evidence)
2. **Then:** Apply × derivation bounds (multiplicative decrease through chains)
3. **Finally:** Apply ⊖ undercut operations (defeaters)

This order is canonical. Different orderings may produce different bounds
due to non-distributivity of × over ⊕ (proven in Lean).

**Example:**
```
b1 .5 L0 @self "evidence A"
b2 .5 L0 @self "evidence B"
b3 .5 ⊕ L0 @self <b1,b2 "aggregated evidence"  # Step 1: 0.5 ⊕ 0.5 = 0.75
b4 .8 L0 @self <b3 "derived belief"  # Step 2: bound = 0.75 × 0.8 = 0.6
```
```

### 4.2 Confidence Operation Warnings (from D4)

**Recommendation:**
```markdown
## Confidence Operation Constraints

### ⊕ Assumes Independence

The oplus operation (`⊕`) assumes evidence is **independent**.
Correlated evidence will inflate confidence.

**Bad (correlated):**
```
b5 .8 L0 @self "merge sort: O(n log n), stable"
b5b .75 L0 @self "merge sort: efficient, stable"  # Same as b5
b5c .7 L0 @self "merge sort: divide and conquer, stable"  # Same as b5
# Combining with ⊕ inflates: 0.8 ⊕ 0.75 ⊕ 0.7 = 0.985
```

**Good (independent):**
```
b13b .7 L0 @self <b1 "missing return statement (test failure suggests this)"
b13c .6 L0 @self <b1 "missing return statement (code review confirms)"
# Combining with ⊕ is valid: 0.7 ⊕ 0.6 = 0.88
```

**Rule:** Only use ⊕ for truly independent evidence (different sources, different arguments).

### Defeater Calibration

Defeater strength matters. Multiple moderate defeaters compound severely.

**Calibration rubric:**
- **0.9-1.0:** Fatal flaw (completely invalidates belief)
- **0.7-0.9:** Major concern (significantly reduces confidence)
- **0.5-0.7:** Moderate issue (notable but not fatal)
- **0.3-0.5:** Minor concern (slight reduction)
- **0.0-0.3:** Weak consideration (minimal impact)

**Example:**
```
b7 .85 L0 @self "use JWT for authentication"
d1 .8 L0 @self "JWT can't be revoked (fatal for sessions requiring revocation)"
d2 .4 L0 @self "JWT size limits (minor concern for small payloads)"
```

Combined defeat: `0.8 ⊕ 0.4 = 0.88`
Undercut: `0.85 × (1 - 0.88) = 0.102` (belief nearly eliminated)

**Warning:** Three moderate defeaters (0.4 each) can annihilate a belief:
`0.9 × (1 - (0.4 ⊕ 0.4 ⊕ 0.4)) = 0.9 × (1 - 0.784) = 0.194`

### Chain-Length Penalty

Derivation chains decrease confidence multiplicatively. Long chains produce very low confidence.

**Example:** 10-step chain with 0.9 per-step inference confidence:
```
conf(final) ≤ 0.9^10 ≈ 0.35
```

**Guideline:**
- **1-3 steps:** Good (minimal penalty)
- **4-6 steps:** Acceptable (moderate penalty)
- **7+ steps:** Consider restructuring (separate sub-arguments, add axioms)

**Mitigation:** For long deductive chains in mathematics, use 1.0 for deductive steps (A4 finding).
```

### 4.3 Stratification Guidelines (from D5)

**Recommendation:**
```markdown
## Stratification (Optional Feature)

Stratification levels (L0, L1, L2...) are **optional**. Most traces use only L0.

### When to Use Levels

**Use L1+ when:**
- Capturing self-correction ("I was wrong about b2")
- Comparing alternatives ("async is better than thread pool")
- Qualifying confidence ("b2's confidence is limited by unknown scale")

**Don't use L1+ when:**
- Simple linear reasoning (no alternatives, no revisions)
- Confidence scores alone capture the comparison

### Löb Discount

For meta-beliefs at higher levels: `conf(b_meta) ≤ conf(b_base)²`

**Exception:** For comparative/qualitative meta-beliefs, a weaker discount may apply:
- "I believe X" → strict Löb discount (c → c²)
- "X is better than Y" → relaxed discount (c → √c or no discount)
- "X is limited by Y" → relaxed discount

**Recommendation:** Start with strict discount. Relax after empirical testing.

### Meta-Belief Patterns

**Pattern 1: Revision ("I was wrong")**
```
L0: original claim
L1: assessment that L0 claim was wrong
L0: new claim (informed by L1)
```

**Pattern 2: Comparison ("X vs Y")**
```
L0: claim X
L0: claim Y
L1: X > Y (comparative meta-belief)
L0: choose X (informed by L1)
```

**Pattern 3: Qualification ("X is limited by Y")**
```
L0: claim X
L1: X is limited (qualitative meta-belief)
L0: modified X (informed by L1)
```
```

---

## Part 5: Invalidation Syntax Clarification

### 5.1 Problem (from B1, D1)

Current syntax `?["condition"]` is concise but the semantics of conditional invalidation need clarification.

### 5.2 Recommendation

```markdown
## Invalidation Semantics

### Syntax
```
belief_id confidence level source justifications ?["condition"] "content"
```

### Semantics
- The belief is **active** when the condition is FALSE
- The belief is **invalidated** when the condition is TRUE
- Invalidation is **not** retroactive — it prevents future use, doesn't erase history

### Example
```
b7 .9 L0 @self <b6 ?["n < 10"] "use merge sort for large arrays"
b8 .8 L0 @self <b6 ?["n >= 10"] "use insertion sort for small arrays"
```

When `n < 10`:
- b7 is INVALIDATED (condition TRUE)
- b8 is ACTIVE (condition FALSE)

When `n >= 10`:
- b7 is ACTIVE (condition FALSE)
- b8 is INVALIDATED (condition TRUE)

### Multiple Conditions
```
b7 .9 L0 @self <b6 ?["n < 10", "memory_constrained"] "use merge sort"
```
Invalidated when **ANY** condition is TRUE (OR semantics).

### Complex Conditions
For complex logic, use a separate belief:
```
b7 .9 L0 @self <b6 "use merge sort for large arrays"
b7a .8 L0 @self "condition: n < 10 AND NOT memory_constrained"
b7 INVALIDATED_BY b7a
```

(Note: INVALIDATED_BY syntax is proposed for v0.2)
```

---

## Part 6: Source Tag Extensions

### 6.1 Problem (from A1, C1)

Current source tags (`@user`, `@ctx`, `@self`, `@file:path`, `@model:name`) are insufficient for some use cases.

### 6.2 Recommendation

```markdown
## Source Tags

### Standard Tags
- `@user`: Direct user input
- `@ctx`: Context provided to the Thinker
- `@self`: Thinker's own reasoning
- `@file:path`: Information from a file
- `@model:name`: Information from another model

### Proposed Extensions (v0.2)
- `@tool:name`: Information from a tool (e.g., `@tool:grep`, `@tool:filesystem`)
- `@doc:url`: Documentation from a URL
- `@test:name`: Test result or assertion
- `@reviewer:id`: Code review feedback
- `@metric:name`: Performance metric or measurement

### Examples
```
b1 1.0 L0 @user "implement binary search"
b2 .9 L0 @file:README.md "input array is sorted"
b3 .8 L0 @tool:grep "no existing binary search implementation found"
b4 .9 L0 @self <b2,b3 "implement from scratch"
```
```

---

## Part 7: Validation Tool Specification

### 7.1 Current State

Validation checks structural validity (grammar, acyclicity, confidence bounds).

### 7.2 Recommendation

```markdown
## Validation

### Structural Validation (Required)
- **Grammar:** All beliefs conform to syntax
- **Acyclicity:** No belief transitively justifies itself (DAG check)
- **Confidence bounds:** All values ∈ [0,1]
- **Level constraints:** Meta-beliefs at higher levels
- **Reference integrity:** All referenced IDs exist

### Quality Validation (Optional, --quality flag)
- **Information gain:** Warn if content is derivable from justifications
- **Decision discriminance:** Warn if confidence variance < 0.1 at decision points
- **Connectivity:** Warn if orphan islands exist
- **Actionability:** Warn if content is too vague or too specific

### Confidence Validation (Optional, --confidence flag)
- **Derivation bounds:** Warn if `conf(child) > conf(parent)` (violates algebra)
- **Independence:** Flag potential correlated evidence used with ⊕
- **Chain length:** Warn if derivation chains > 5 steps
- **Defeater calibration:** Flag if multiple moderate defeaters compound

### Output Format
```
$ clair-validator trace.clair --quality

✓ Structural validation: PASSED
✓ Grammar: OK (23 beliefs)
✓ Acyclicity: OK (no cycles)
✓ Confidence: OK (all in [0,1])
✓ Levels: OK (all at L0)
✓ References: OK (all IDs valid)

⚠ Quality validation: WARNINGS
  ⚠ b5: Low information gain (content derivable from justifications)
  ⚠ b2,b3,b4: Low decision discriminance (all at 0.5)
  ⚠ b13-b15: Disconnected from main DAG (orphan island)
  ℹ b7: Potentially too vague ("perform computation")

⚠ Confidence validation: WARNINGS
  ⚠ b12: Confidence increased through derivation (0.6 → 0.7)
  ⚠ b5,b5b,b5c: Potential correlated evidence used with ⊕
  ℹ b1→...→b10: Long derivation chain (10 steps)

Status: VALID with warnings
```
```

---

## Part 8: Spec v0.2 Structure

### 8.1 Proposed Table of Contents

```markdown
# CLAIR Specification v0.2

## 1. Introduction
- 1.1 What is CLAIR?
- 1.2 Thinker → Assembler Architecture
- 1.3 Design Goals

## 2. Syntax
- 2.1 Belief Format
- 2.2 Confidence Values
- 2.3 Stratification Levels
- 2.4 Source Tags
- 2.5 Justification Lists
- 2.6 Invalidation Conditions

## 3. Semantics
- 3.1 DAG Structure
- 3.2 Confidence Algebra (×, ⊕, undercut, rebut, min)
- 3.3 Multi-Justification Semantics (∧, ∨, min)
- 3.4 Evaluation Order
- 3.5 Groundedness
- 3.6 Invalidation Semantics

## 4. Stratification (Optional)
- 4.1 Level Constraints
- 4.2 Löb Discount
- 4.3 Meta-Belief Patterns

## 5. Content Guidelines
- 5.1 Specificity (Types, Algorithms)
- 5.2 Explicitness (No Vague Terms)
- 5.3 Commitment (No "Or")
- 5.4 Abstraction Level (Strategy + Algorithm)
- 5.5 Error Handling Strategies

## 6. Trace Quality
- 6.1 Information Gain
- 6.2 Decision Discriminance
- 6.3 Grounding Connectivity
- 6.4 Actionability

## 7. Confidence Operations
- 7.1 Independence Assumption (⊕)
- 7.2 Defeater Calibration
- 7.3 Chain-Length Penalty
- 7.4 Mathematical Deduction (use 1.0)

## 8. Validation
- 8.1 Structural Validation
- 8.2 Quality Validation
- 8.3 Confidence Validation

## 9. Examples
- 9.1 Minimal Useful Trace
- 9.2 Algorithm Selection
- 9.3 Bug Diagnosis
- 9.4 API Design
- 9.5 Self-Correction (with L1)

## Appendix A: Confidence Algebra (Lean Theorems)
## Appendix B: Stratification Theory
## Appendix C: Migration Guide (v0.1 → v0.2)
```

---

## Summary of Changes

| Area | Change | Priority |
|------|--------|----------|
| **Multi-justification** | Add ∧, ∨, min semantics | HIGH |
| **Quality guidelines** | Add IG, DD, GC, AC criteria | HIGH |
| **Content clarity** | Add specificity, explicitness rules | HIGH |
| **Evaluation order** | Specify ×-then-⊕ or ⊕-then-× | MEDIUM |
| **Confidence warnings** | Document ⊕ independence, defeater calibration | MEDIUM |
| **Stratification** | Document as optional, add patterns | MEDIUM |
| **Invalidation** | Clarify semantics, add INVALIDATED_BY | LOW |
| **Source tags** | Add @tool, @doc, @test, @reviewer, @metric | LOW |
| **Validation** | Specify --quality and --confidence flags | MEDIUM |

---

## Next Steps

1. **Implement spec v0.2** with above changes
2. **Update validation tool** with --quality and --confidence flags
3. **Create migration guide** from v0.1 to v0.2
4. **Develop Thinker training prompts** based on content guidelines
5. **Empirical testing** with real LLMs producing v0.2 traces
