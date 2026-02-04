# B4: Degraded Trace Test

## Research Question

How gracefully do Assemblers handle degraded CLAIR traces? In practice, traces may be incomplete, malformed, or corrupted. This exploration systematically degrades a known-good trace to find the **minimum viable trace** and understand which components are essential vs optional.

**Thesis Connection:** CLAIR is claimed to be a robust IR for LLM reasoning. If Assemblers fail catastrophically with minor degradation, the IR model is fragile. If Assemblers degrade gracefully (usable output even from partial traces), the model is robust.

**Validation Criteria:**
- Systematic degradation of known-good trace across 5+ dimensions
- Analysis of how each degradation affects Assembler output
- Identification of minimum viable trace components
- Counter-examples: degradations that cause fatal failure
- Connection to thesis (supports, undermines, or refines)

---

## Background: The Base Trace

### Source: Pi Calculation Trace

From `examples/pi-calculation.md`, the pi-calculation trace is our "known-good" baseline. It has 18 beliefs, well-calibrated confidence, explicit alternatives, clear justification chains, and invalidation conditions.

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b4 .9 L0 @self <b3 "cannot use floating point, need big decimal or rational"
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b6 .5 L0 @self <b3 "Machin formula: moderate speed"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
b8 .85 L0 @self <b7 ?["n<15"] "use Chudnovsky algorithm"
b9 .9 L0 @self <b8 "need: factorial function"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b11 .9 L0 @self <b8 "need: square root of 10005"
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b13 .9 L0 @self <b12 "for each k: compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b14 .9 L0 @self <b13 "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
b15 .9 L0 @self <b14 "accumulate sum"
b16 .85 L0 @self <b15,b11 "final: PI = 426880 * sqrt(10005) / sum"
b17 .9 L0 @self <b1 "input: n (positive integer, number of digits)"
b18 .9 L0 @self <b16 "output: string representation of PI to n digits"
```

### Trace Characterization

| Component | Count | Quality |
|-----------|-------|---------|
| Total beliefs | 18 | High |
| Confidence variance | 0.3 - 0.95 (Δ=0.65) | Excellent discrimination |
| Justification chains | 3-4 levels deep | Well-structured |
| Alternatives shown | 3 (Leibniz, Machin, Chudnovsky) | Complete |
| Invalidation conditions | 1 (`?["n<15"]`) | Present |
| Groundedness | 100% (all trace to b1) | Excellent |

**Expected Assembler behavior:** This trace should produce correct, efficient Chudnovsky implementation with proper precision handling.

---

## Degradation Type 1: Remove Justifications

### Hypothesis

Justification edges (`<b1, b2, ...`) connect beliefs to their reasons. Removing them breaks the "why" chain. Will the Assembler still produce correct code?

### Degraded Trace (No Justifications)

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .95 L0 @self "N can be arbitrarily large"
b3 .95 L0 @self "need arbitrary precision arithmetic"
b4 .9 L0 @self "cannot use floating point, need big decimal or rational"
b5 .3 L0 @self "Leibniz series: slow, needs billions of terms"
b6 .5 L0 @self "Machin formula: moderate speed"
b7 .85 L0 @self "Chudnovsky: ~14 digits per iteration"
b8 .85 L0 @self ?["n<15"] "use Chudnovsky algorithm"
b9 .9 L0 @self "need: factorial function"
b10 .9 L0 @self "need: arbitrary precision division"
b11 .9 L0 @self "need: square root of 10005"
b12 .9 L0 @self "iterate k from 0 until precision reached"
b13 .9 L0 @self "for each k: compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b14 .9 L0 @self "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
b15 .9 L0 @self "accumulate sum"
b16 .85 L0 @self "final: PI = 426880 * sqrt(10005) / sum"
b17 .9 L0 @self "input: n (positive integer, number of digits)"
b18 .9 L0 @self "output: string representation of PI to n digits"
```

**What changed:** All `<bX` justification references removed. Beliefs are now "floating" — no provenance.

### Expected Assembler Behavior

| Aspect | Original Trace | Degraded Trace |
|--------|---------------|----------------|
| **Algorithm selection** | Clear: b7 (.85) chosen over b5 (.3), b6 (.5) | Still clear: b7 has highest confidence |
| **Component ordering** | Justified: b9,b10,b11 must precede b12 | Unclear: does order matter? |
| **Why Chudnovsky?** | Traceable: b7 ← b3 ← b2 ← b1 | Unanswerable: no connection to requirements |
| **Invalidation meaning** | Clear: reconsider if n<15 | Clear: still present |

### Predicted Output Quality

**Assembler interpretation:**
```
"Highest confidence is b7 (.85) 'Chudnovsky', so use that.
I see b9-b16 are about components and formula.
The order is: b9 (factorial), b10 (division), b11 (sqrt),
then b12-b16 (loop and formula).
No explicit dependencies, but the ordering suggests sequence."
```

**Code quality:** Should still produce working Chudnovsky implementation. The content is all there; only the "why" is missing.

**Severity:** LOW — Justifications enable *auditability*, not *assembly*.

### Counter-Example: When Justifications Matter

Consider a trace where ORDER is critical and isn't obvious from content:

```clair
; Good trace (with justifications)
b1 1.0 @user "parse JSON file"
b2 .9 @self <b1 "read file first"
b3 .9 @self <b2 "then parse JSON"

; Degraded trace (no justifications)
b1 1.0 @user "parse JSON file"
b2 .9 @self "read file first"
b3 .9 @self "then parse JSON"
```

**Here, the English text ("first", "then") carries the order.** The Assembler can still infer.

**But without text cues:**

```clair
; Degraded trace (no justifications, no text cues)
b1 1.0 @user "parse JSON"
b2 .9 @self "read file"
b3 .9 @self "parse contents"
b4 .9 @self "handle errors"
```

**Question:** Does b4 happen before, during, or after b2/b3?

**Assembler might:**
- Guess wrong order
- Handle errors only during file read (not during parse)
- Miss that b4 applies to both b2 and b3

### Finding: Justifications Are Most Critical When

1. **Order is ambiguous** (no "first", "then", "after" in content)
2. **Dependencies are cross-cutting** (b4 justifies both b2 and b3)
3. **Content doesn't imply sequence** (atomic operations that could execute in any order)

**Otherwise:** Content semantics often imply order, and LLMs are good at inferring sequence from context.

---

## Degradation Type 2: Scramble Confidence Values

### Hypothesis

Confidence values rank alternatives. Scrambling them flips the ranking — will the Assembler choose the wrong algorithm?

### Degraded Trace (Scrambled Confidence)

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b4 .9 L0 @self <b3 "cannot use floating point, need big decimal or rational"
; SCRAMBLED: original .3, .5, .85 → now .9, .8, .2
b5 .9 L0 @self <b3 "Leibniz series: slow, needs billions of terms"  ; WAS .3
b6 .8 L0 @self <b3 "Machin formula: moderate speed"                ; WAS .5
b7 .2 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"          ; WAS .85
b8 .9 L0 @self <b7 ?["n<15"] "use Chudnovsky algorithm"            ; Still .9 (selection belief)
b9 .9 L0 @self <b8 "need: factorial function"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b11 .9 L0 @self <b8 "need: square root of 10005"
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b13 .9 L0 @self <b12 "for each k: compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b14 .9 L0 @self <b13 "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
b15 .9 L0 @self <b14 "accumulate sum"
b16 .85 L0 @self <b15,b11 "final: PI = 426880 * sqrt(10005) / sum"
b17 .9 L0 @self <b1 "input: n (positive integer, number of digits)"
b18 .9 L0 @self <b16 "output: string representation of PI to n digits"
```

**What changed:** b5-b7 confidence values scrambled. Leibniz now has .9 (highest!), Chudnovsky has .2 (lowest!). But b8 still says "use Chudnovsky" at .9 confidence.

### Expected Assembler Behavior

**Conflicting signals:**
- b5 (Leibniz) has .9 — highest among alternatives
- b7 (Chudnovsky) has .2 — lowest
- b8 says "use Chudnovsky" at .9

**Assembler interpretation paths:**

| Path | Interpretation | Result |
|------|----------------|--------|
| **A: Follow b8's directive** | b8 explicitly says "use Chudnovsky" | Correct: Chudnovsky implemented |
| **B: Follow highest alternative** | b5 has highest confidence (.9) | Wrong: Leibniz implemented (slow!) |
| **C: Detect conflict** | b8 (.9) references b7 (.2) — mismatch | Confused: request clarification |

### Predicted Output Quality

**Most Assemblers will likely follow Path A** — b8 is an explicit *selection* belief that commits to an approach. The content of b8 ("use Chudnovsky algorithm") is directive, not descriptive.

**But:** A naive Assembler might follow Path B, treating all beliefs equally and picking the highest confidence regardless of semantic role.

**Severity:** HIGH if Assembler is naive; LOW if Assembler understands "selection vs alternative" distinction.

### Counter-Example: Without Explicit Selection

```clair
; Degraded trace (no b8 selection belief, scrambled confidence)
b5 .9 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b6 .8 L0 @self <b3 "Machin formula: moderate speed"
b7 .2 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
; No b8 to commit to a choice
```

**Now the Assembler MUST choose based on confidence alone.** It will pick Leibniz (.9) — disastrously wrong for large N.

### Finding: Confidence Scrambling Is Fatal When

1. **No explicit selection belief** (trace explores but doesn't commit)
2. **Assembler treats all beliefs equally** (doesn't distinguish "alternatives" from "selections")

**Mitigation:** Traces should always have final selection beliefs that commit to choices. Content semantics ("use X", "select Y") should override confidence when there's conflict.

---

## Degradation Type 3: Remove Invalidations

### Hypothesis

Invalidation conditions (`?["condition"]`) specify when to reconsider. Removing them loses edge case awareness. Will the Assembler miss optimizations or correctness issues?

### Degraded Trace (No Invalidations)

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b4 .9 L0 @self <b3 "cannot use floating point, need big decimal or rational"
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b6 .5 L0 @self <b3 "Machin formula: moderate speed"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
; REMOVED: ?["n<15"] from b8
b8 .85 L0 @self <b7 "use Chudnovsky algorithm"  ; No invalidation!
b9 .9 L0 @self <b8 "need: factorial function"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b11 .9 L0 @self <b8 "need: square root of 10005"
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b13 .9 L0 @self <b12 "for each k: compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b14 .9 L0 @self <b13 "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
b15 .9 L0 @self <b14 "accumulate sum"
b16 .85 L0 @self <b15,b11 "final: PI = 426880 * sqrt(10005) / sum"
b17 .9 L0 @self <b1 "input: n (positive integer, number of digits)"
b18 .9 L0 @self <b16 "output: string representation of PI to n digits"
```

**What changed:** b8 lost its `?["n<15"]` invalidation. The Assembler no longer knows that Chudnovsky is overkill for small N.

### Expected Assembler Behavior

| Scenario | Original Trace | Degraded Trace |
|----------|---------------|----------------|
| **n=1000** | Use Chudnovsky (appropriate) | Use Chudnovsky (appropriate) |
| **n=5** | "Reconsider: Chudnovsky overkill" | Use Chudnovsky (overkill but works) |
| **Optimization awareness** | Knows to use simpler method for n<15 | No optimization hint |

### Predicted Output Quality

**Functional correctness:** Still 100%. Chudnovsky works for all N, it's just overkill for small N.

**Efficiency:** Lost. The Assembler won't implement a conditional switch (e.g., "if n<20: use Machin, else: Chudnovsky").

**Severity:** LOW for correctness; MEDIUM for efficiency.

### Counter-Example: When Invalidations Are Critical

Consider a trace where invalidations are about **correctness**, not efficiency:

```clair
b1 1.0 @user "sort an array"
b2 .9 @self <b1 "use quick sort"
b3 .9 @self <b2 ?["array may contain duplicates"] "use three-way partition (Dutch National Flag) to handle duplicates efficiently"
```

**If b3 loses its invalidation:**
```
b2 .9 @self <b1 "use quick sort"
b3 .9 @self <b2 "use three-way partition"  ; When? Always?
```

**Assembler behavior:** May use three-way partition *even when unnecessary*, adding complexity. Or may misinterpret and use standard partition (wrong for duplicates).

### Finding: Invalidations Have Three Categories

| Category | Example Impact | Severity if Lost |
|----------|----------------|------------------|
| **Optimization** | "Use simpler method for small N" | LOW — still correct, just suboptimal |
| **Correctness** | "Use three-way partition for duplicates" | HIGH — wrong algorithm may fail |
| **Safety** | "Don't use this for security-critical code" | CRITICAL — security vulnerability |

**Degradation severity depends on category.** Optimization invalidations are optional; correctness/safety invalidations are essential.

---

## Degradation Type 4: Remove Some Beliefs

### Hypothesis

What is the **minimum belief count** needed for the Assembler to produce correct code? We'll progressively remove beliefs to find the threshold.

### Degradation Level 1: Remove Alternatives (Keep only Chudnovsky path)

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
b8 .85 L0 @self <b7 ?["n<15"] "use Chudnovsky algorithm"
b9 .9 L0 @self <b8 "need: factorial function"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b11 .9 L0 @self <b8 "need: square root of 10005"
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b16 .85 L0 @self <b9,b10,b11 "final: PI = 426880 * sqrt(10005) / sum"
b17 .9 L0 @self <b1 "input: n (positive integer, number of digits)"
b18 .9 L0 @self <b16 "output: string representation of PI to n digits"
```

**Removed:** b4 (no floats), b5 (Leibniz), b6 (Machin), b13-b15 (detailed formula steps).

**Belief count:** 18 → 13 (removed 5)

### Expected Assembler Behavior

**Lost information:**
- Why Chudnovsky was chosen (no alternatives to compare)
- Detailed formula breakdown (b13-b15 combined into implicit understanding)
- "Cannot use floating point" constraint (might miss this)

**Assembler interpretation:**
```
"User wants PI to N digits. Use Chudnovsky (b7, b8).
Need factorial, division, sqrt. Iterate k, accumulate.
Final formula: 426880 * sqrt(10005) / sum."
```

**Code quality:** Should still work. The formula in b16 is complete. The Assembler doesn't need b13-b15 if b16 is present.

**Severity:** LOW — Alternatives are for auditability, not assembly.

### Degradation Level 2: Remove Requirements Analysis

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b7 .85 L0 @self "Chudnovsky: ~14 digits per iteration"
b8 .85 L0 @self <b7 "use Chudnovsky algorithm"
b9 .9 L0 @self <b8 "need: factorial function"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b11 .9 L0 @self <b8 "need: square root of 10005"
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b16 .85 L0 @self <b11 "final: PI = 426880 * sqrt(10005) / sum"
```

**Removed:** b2-b6 (requirements, alternatives), b13-b15 (formula details), b17-b18 (interface).

**Belief count:** 18 → 8 (removed 10)

### Expected Assembler Behavior

**Lost information:**
- Why arbitrary precision is needed (b2-b3)
- Input/output interface specification (b17-b18)
- Detailed formula steps (b13-b15)

**Assembler interpretation:**
```
"Use Chudnovsky algorithm. Need factorial, division, sqrt.
Iterate k, accumulate. Final: 426880 * sqrt(10005) / sum."
```

**Code quality:** Still functional, but:
- Assembler might use `float` instead of `Decimal` (missing "arbitrary precision" hint)
- Function signature might vary (no b17-b18 to specify `int` input, `str` output)

**Severity:** MEDIUM — Risk of wrong data type, but algorithm is correct.

### Degradation Level 3: Minimal Trace (Algorithm + Formula Only)

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b7 .85 L0 @self <b1 "use Chudnovsky algorithm"
b16 .85 L0 @self <b7 "PI = 426880 * sqrt(10005) / sum, where sum = Σ (-1)^k * (6k)! * (13591409 + 545140134*k) / ((3k)! * (k!)^3 * 640320^(3k+3/2))"
```

**Belief count:** 18 → 3 (removed 15)

### Expected Assembler Behavior

**Information preserved:**
- User request (b1)
- Algorithm name (b7)
- Complete formula (b16)

**Assembler interpretation:**
```
"User wants PI calculation. Use Chudnovsky with this formula: [formula].
I know Chudnovsky requires arbitrary precision, factorial, sqrt.
I'll implement it in Python using Decimal."
```

**Code quality:** High! The formula in b16 is mathematically complete. A competent Assembler knows:
- Chudnovsky requires factorial
- Square roots need arbitrary precision
- Accumulation is a loop

**Severity:** VERY LOW — 3 beliefs are sufficient for this task!

### Counter-Example: When Minimal Trace Fails

Consider a task where the formula requires **domain knowledge** the Assembler lacks:

```clair
b1 1.0 @user "implement a cryptographic hash function"
b2 .85 @self <b1 "use SHA-256: Merkle-Damgård construction with compression function using message schedule and constants..."
```

**Assembler (non-cryptographer):**
```
"Use SHA-256. What's 'Merkle-Damgård'? What are the constants?
I'll guess or look them up."
```

**Result:** May implement wrong constants, wrong padding, wrong endianness.

**For crypto, medical, legal domains:** Minimal traces fail because Assembler lacks domain knowledge. Detailed traces are needed.

### Finding: Minimum Belief Count Depends On

| Factor | Low Domain Knowledge | High Domain Knowledge |
|--------|---------------------|----------------------|
| **Algorithmic task** | 5-10 beliefs (specify components) | 2-3 beliefs (name + formula) |
| **Domain-specific task** | 10-20 beliefs (explain domain concepts) | 5-10 beliefs (key concepts) |
| **Creative task** | 15+ beliefs (detailed intent) | 5-10 beliefs (theme guidance) |

**Pi calculation is "low domain knowledge"** — most programmers know what factorial, sqrt, and arbitrary precision mean.

---

## Degradation Type 5: Reorder Beliefs

### Hypothesis

CLAIR traces are DAGs, not sequences. Order shouldn't matter... or does it? Will a scrambled order confuse the Assembler?

### Degraded Trace (Random Order)

```clair
b16 .85 L0 @self <b15,b11 "final: PI = 426880 * sqrt(10005) / sum"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b13 .9 L0 @self <b12 "for each k: compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b14 .9 L0 @self <b13 "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
b9 .9 L0 @self <b8 "need: factorial function"
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b11 .9 L0 @self <b8 "need: square root of 10005"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b17 .9 L0 @self <b1 "input: n (positive integer, number of digits)"
b8 .85 L0 @self <b7 ?["n<15"] "use Chudnovsky algorithm"
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b15 .9 L0 @self <b14 "accumulate sum"
b6 .5 L0 @self <b3 "Machin formula: moderate speed"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b18 .9 L0 @self <b16 "output: string representation of PI to n digits"
b4 .9 L0 @self <b3 "cannot use floating point, need big decimal or rational"
```

**What changed:** Order randomized. Justification edges preserved but b16 (which references b15, b11) appears before b15, b11 exist. b2 appears before b1.

### Expected Assembler Behavior

**Human readability:** Terrible. Trace looks chaotic.

**Assembler interpretation:**
```
"I see b16 first: 'PI = 426880 * sqrt(10005) / sum'. It references b15, b11 which I haven't seen yet.
Then b2: 'N can be arbitrarily large'. References b1 which I haven't seen.
...
As I process more beliefs, the justification chains resolve."
```

**Question:** Does the Assembler need to see beliefs in "dependency order" (b1 before b2 before b3)?

**LLM inference:** LLMs process input token-by-token. Forward references might be confusing:
- "b16 ... <b15,b11" — b15, b11 haven't been introduced yet
- The Assembler might "remember" these references and resolve later
- Or it might be confused by forward references

### Predicted Output Quality

| Assembler Type | Expected Behavior |
|----------------|-------------------|
| **Multi-pass (human-like)** | Read whole trace, build mental graph, assemble | Works fine |
| **Single-pass (token-by-token)** | Process beliefs as seen, forward refs are tricky | May degrade |

**Most LLMs:** Multi-pass by default (attention mechanism sees all tokens). Order likely doesn't matter for *correctness*, but might affect *confidence*.

**Severity:** LOW for modern LLMs; MEDIUM for simpler parsers.

### Counter-Example: When Order Matters Critically

Consider a trace with **conditional redefinitions**:

```clair
; GOOD ORDER
b1 1.0 @user "choose algorithm"
b2 .9 @self <b1 "use merge sort"
b3 .9 @self <b1 ?["n<20"] "actually: use insertion sort for small arrays"

; BAD ORDER (redefinition appears before original)
b1 1.0 @user "choose algorithm"
b3 .9 @self <b1 ?["n<20"] "actually: use insertion sort for small arrays"
b2 .9 @self <b1 "use merge sort"
```

**Assembler reading "bad order":**
```
"First: use insertion sort for small arrays.
Then: use merge sort.
Which one? Is b2 the default, and b3 the exception?
Or is b3 the new default, overriding b2?"
```

**Ambiguity:** Order matters when beliefs "override" or "refine" previous beliefs. CLAIR has no explicit "override" semantics — it's inferred from content ("actually", "instead of", etc.).

### Finding: Reordering Has Three Impact Levels

| Impact | Scenario | Severity |
|--------|----------|----------|
| **None** | Pure DAG, no forward refs, no overrides | LOW |
| **Medium** | Forward references (b16 before b15) | LOW-MEDIUM |
| **High** | Override/refinement patterns in wrong order | HIGH |

**Recommendation:** For traces with "override" patterns (mind-change, refinement), order matters. For pure DAG traces, order is cosmetic.

---

## Synthesis: The Degradation Spectrum

### Severity Summary

| Degradation Type | Severity | Justification | Recovery Possible? |
|------------------|----------|---------------|-------------------|
| **Remove justifications** | LOW-MEDIUM | Lost auditability, content often implies order | Yes — LLMs infer from semantics |
| **Scramble confidence** | HIGH | Wrong algorithm choice if no explicit selection | Partial — if selection belief present |
| **Remove invalidations** | LOW-CRITICAL | Optimization (LOW) vs correctness (HIGH) vs safety (CRITICAL) | Depends on category |
| **Remove beliefs** | LOW-MEDIUM | Minimal trace (2-3 beliefs) often sufficient | Yes — if formula is complete |
| **Reorder beliefs** | LOW | LLMs see all tokens; order is cosmetic | Yes — except for override patterns |

### The Minimum Viable Trace

For the pi-calculation task, the **minimum viable trace** is:

```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .85 L0 @self <b1 "use Chudnovsky algorithm: PI = 426880 * sqrt(10005) / Σ (-1)^k * (6k)! * (13591409 + 545140134*k) / ((3k)! * (k!)^3 * 640320^(3k+3/2))"
```

**2 beliefs.** That's it.

**Why this works:**
- b1 specifies the task
- b2 specifies the complete algorithm + formula
- Assembler knows (or can infer) factorial, sqrt, iteration, accumulation

**What's lost:**
- Why Chudnovsky was chosen (no alternatives)
- Edge case handling (no invalidations)
- "Why" chain (no justifications beyond b1)

**What's gained:**
- Brevity (2 beliefs vs 18)
- Assembly still works

### The Fragile Components

Based on degradation analysis, the **most fragile** (essential) components are:

| Component | Fragility | Why Essential |
|-----------|-----------|---------------|
| **User request** | CRITICAL | Without b1, nothing is grounded |
| **Algorithm selection** | HIGH | Without clear choice, Assembler guesses |
| **Complete formula** | HIGH | Incomplete formula → broken code |
| **Invalidations (safety)** | CRITICAL | Safety invalidations prevent disasters |

### The Robust Components

These components are **optional** for assembly (though useful for auditability):

| Component | Robustness | Why Optional |
|-----------|------------|--------------|
| **Alternatives (rejected)** | HIGH | Assembler only needs the choice, not the rejected options |
| **Justifications** | MEDIUM | Content semantics often imply reasoning |
| **Invalidations (optimization)** | MEDIUM | Lost optimization, but code still works |
| **Detailed breakdowns** | HIGH | If high-level belief is complete, details are redundant |

---

## Counter-Examples: Fatal Degradations

### Fatal Degradation 1: Ambiguous Algorithm Selection

```clair
b1 1.0 @user "sort an array"
b2 .5 @self "use merge sort"
b3 .5 @self "use quick sort"
b4 .5 @self "use heap sort"
; No selection belief, equal confidence
```

**Assembler behavior:** Random choice or request clarification. Degradation is **fatal** — no guidance.

### Fatal Degradation 2: Incomplete Formula

```clair
b1 1.0 @user "calculate PI"
b2 .85 @self <b1 "use Chudnovsky algorithm"
; Missing: the actual formula!
```

**Assembler behavior:** Must know Chudnovsky formula from training. If not, fails. Degradation is **fatal** for non-expert Assemblers.

### Fatal Degradation 3: Lost Safety Invalidation

```clair
b1 1.0 @user "hash passwords"
b2 .9 @self <b1 "use MD5 for hashing"
; Lost invalidation: ?["never use MD5 for security"]
```

**Assembler behavior:** Implements MD5 for passwords. **Security vulnerability.** Degradation is **critical**.

### Fatal Degradation 4: Circular Dependency After Removal

```clair
b1 1.0 @user "parse JSON"
b2 .9 @self <b3 "parse the JSON"  ; References b3
b3 .9 @self <b2 "read the file"   ; References b2
; Circular! After removing b4 ("read file first")
```

**Original trace:**
```clair
b2 .9 @self <b4 "parse the JSON"
b3 .9 @self <b2 "read the file"
b4 .9 @self <b1 "read file first"
```

**Removing b4 breaks the chain** and creates a cycle between b2 and b3.

---

## Thesis Impact Assessment

### Does This Support or Undermine CLAIR as IR?

**Supporting evidence:**

1. **Graceful degradation:** Most degradations (removed justifications, removed alternatives, reordered beliefs) don't break assembly. The Assembler still produces working code.

2. **Minimal traces work:** 2-3 beliefs can be sufficient for algorithmic tasks. CLAIR doesn't require verbosity.

3. **Justifications are for auditability:** The "why" chain is less critical for assembly than for human understanding. This supports the dual-audience model (Thinker → Assembler vs human auditor).

**Refining evidence:**

1. **Critical components identified:** User request, algorithm selection, complete formula, safety invalidations are non-negotiable. This refines the spec — these should be marked as "required."

2. **Confidence fragility:** Scrambled confidence values cause wrong choices if no explicit selection belief exists. This suggests "selection beliefs" should be a required pattern in the spec.

3. **Domain knowledge dependency:** Minimal traces work only when Assembler has domain knowledge. For domain-specific tasks, detailed traces are essential. CLAIR can't transfer expertise from Thinker to Assembler.

4. **Invalidations vary by category:** Optimization invalidations are optional; safety invalidations are critical. The spec should distinguish these.

**Undermining evidence:**

1. **Circular dependency risk:** Removing beliefs can create cycles. Structural validation is needed to prevent this.

2. **Order matters for overrides:** Reordering hurts when traces have "mind-change" patterns. CLAIR lacks explicit "override" semantics, relying on content cues.

3. **Ambiguity is fatal:** Confidence splat, equal alternatives, missing selection — these produce unusable traces. The spec should forbid or detect these patterns.

### Thesis Assessment

**CLAIR is viable as an IR with清晰的 essential/optional distinction:**

| Component | Essential | Optional | Reason |
|-----------|-----------|----------|--------|
| User request (`@user`) | ✅ | ❌ | Grounds everything |
| Algorithm selection | ✅ | ❌ | Without clear choice, Assembler guesses |
| Complete formula/spec | ✅ | ❌ | Incomplete spec → broken code |
| Safety invalidations | ✅ | ❌ | Security/correctness critical |
| Alternatives (rejected) | ❌ | ✅ | For auditability, not assembly |
| Justifications | ❌ | ✅ | Content often implies reasoning |
| Optimization invalidations | ❌ | ✅ | Nice-to-have, not critical |
| Detailed breakdowns | ❌ | ✅ | Redundant if high-level complete |

**The thesis stands with refinement:** CLAIR is viable, but not all components are equal. The spec should distinguish essential vs optional, and Thinkers should be trained to prioritize essential components.

---

## Recommendations

### For Spec v0.2

**Add "Essential vs Optional" section:**

```markdown
## Essential Components

A minimally viable CLAIR trace must include:

1. **User request** (`@user`) — grounds the trace
2. **Algorithm/decision selection** — single, unambiguous choice
3. **Complete specification** — formula, API contract, or implementation details
4. **Safety invalidations** — conditions where approach is unsafe/wrong

## Optional Components

These enhance auditability but aren't required for assembly:

1. **Alternatives** — rejected options with low confidence
2. **Justifications** — why beliefs are held (content often implies)
3. **Optimization invalidations** — performance trade-offs
4. **Detailed breakdowns** — step-by-step when high-level is complete
```

**Add "Selection Belief Pattern":**

```markdown
## Selection Beliefs

After exploring alternatives, always include a selection belief:

b5 .3 L0 @self "use bubble sort"
b6 .7 L0 @self "use merge sort"
b7 .9 L0 @self <b5,b6 "select merge sort: O(n log n) worst case"

The selection belief (b7) commits to a choice and explains why.
Without b7, the Assembler must guess between b5 and b6.
```

**Add "Invalidation Categories":**

```markdown
## Invalidation Categories

| Category | Syntax | Impact |
|----------|--------|--------|
| Optimization | `?["n<20"]` | Performance trade-off, optional |
| Correctness | `?["array may have duplicates"]` | Wrong algorithm may fail, required |
| Safety | `?["never for security-critical code"]` | Security/safety risk, critical |

Mark safety invalidations explicitly: `?["SAFETY: condition"]`
```

### For Assembler Prompts

**Add degradation handling:**

```
You are an Assembler LLM. Convert this CLAIR trace into executable code.

If the trace is degraded:
- Missing justifications: Infer order from content semantics
- Scrambled confidence: Follow explicit selection beliefs over confidence
- Missing invalidations: Implement correct code (optimizations optional)
- Minimal beliefs: Fill in standard components (factorial, sqrt, etc.)

If ambiguity prevents assembly:
- Note the ambiguity in comments
- Make a reasonable choice with explanation
- Don't fail — produce working code
```

### For Trace Validation

**Pre-assembly checks:**

```python
def validate_minimal_viability(trace):
    checks = {
        "has_user_request": any(b.source == "@user" for b in trace),
        "has_unambiguous_selection": has_selection_belief(trace) or has_single_alternative(trace),
        "specification_complete": is_complete(trace),
        "no_circular_deps": is_acyclic(trace),
        "no_confidence_splat": confidence_variance(trace) > 0.1,
    }
    return all(checks.values())
```

---

## Open Questions

### Q1: What Is the Optimal Trace Length?

We found that 2 beliefs work for pi-calculation, but 20+ might be needed for domain-specific tasks. Is there a formula?

**Hypothesis:** Optimal length = f(domain knowledge required, task complexity)

**Research needed:**
- Empirical study: trace length vs assembly success rate
- Domain categorization: which domains need detailed traces?
- Task complexity metric: lines of code? decision points?

### Q2: Can Assemblers Recover from Circular Dependencies?

We found that removing beliefs can create cycles. Can Assemblers detect and resolve these?

**Hypothesis:** LLMs might detect cycles and "break" them by ignoring one edge.

**Test needed:** Present traces with intentional cycles, measure Assembler behavior.

### Q3: How Much Domain Knowledge Transfer Is Possible?

Minimal traces assume Assembler knows the domain. Can CLAIR transfer domain knowledge from Thinker to Assembler?

**Hypothesis:** Partial transfer is possible (concepts, constraints) but not deep expertise.

**Example:** Thinker knows crypto details; can CLAIR teach Assembler about SHA-256 constants?

### Q4: Should CLAIR Have Explicit "Override" Semantics?

For mind-change patterns (b5: use X; b7: actually, use Y), order matters. Should the spec add explicit override syntax?

**Proposal:**
```clair
b5 .8 L0 @self "use bubble sort"
b7 .9 L0 @self <b1 override:b5 "actually: use merge sort instead"
```

**Or:** Use invalidations to deprecate earlier beliefs:
```clair
b5 .8 L0 @self ?["before learning complexity"] "use bubble sort"
b7 .9 L0 @self ?["after learning complexity"] "use merge sort instead"
```

---

## Conclusion

**Key findings:**
- ✅ CLAIR degrades gracefully — most degradations don't break assembly
- ✅ Minimal traces (2-3 beliefs) work for algorithmic tasks
- ✅ Justifications and alternatives are optional for assembly (essential for auditability)
- ⚠️ Confidence scrambling is fatal without explicit selection beliefs
- ⚠️ Invalidation severity varies: optimization (LOW) vs correctness (HIGH) vs safety (CRITICAL)
- ⚠️ Domain knowledge dependency — minimal traces work only when Assembler knows the domain

**Essential components (non-negotiable):**
1. User request (`@user`) — grounds the trace
2. Unambiguous algorithm/decision selection
3. Complete specification (formula, API, implementation details)
4. Safety invalidations (critical conditions)

**Optional components (nice-to-have):**
1. Rejected alternatives (for auditability)
2. Justification chains (content often implies)
3. Optimization invalidations (performance, not correctness)
4. Detailed breakdowns (redundant if high-level complete)

**Thesis connection:** **Refines the thesis** — CLAIR is viable as an IR, but not all components are equal. The model supports graceful degradation, and minimal traces are surprisingly effective. The spec should distinguish essential vs optional components to guide Thinkers and validate traces.

**Next steps:**
- Empirical testing with real LLMs to validate degradation predictions
- Development of "minimum viable trace" heuristics
- Spec v0.2 with essential/optional distinction
- Study of domain knowledge transfer limits
