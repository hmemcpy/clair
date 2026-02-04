# S3: Open Questions for Future Work

**Date:** 2026-02-04

**Status:** COMPLETED

**Purpose:** Catalog open questions identified across 23 explorations, organized by priority and researchability.

---

## Executive Summary

The explorations identified **30+ open questions** across 6 categories:
1. **Validation & Quality** (7 questions) — How to ensure traces are useful, not just valid
2. **Stratification** (6 questions) — Whether and how to use meta-beliefs
3. **Confidence Operations** (5 questions) — Algebra refinements and calibration
4. **Content & Language** (5 questions) — Specificity, ambiguity, domain knowledge
5. **Architecture & Protocol** (4 questions) — Thinker-Assembler communication
6. **Empirical Studies** (8 questions) — Real-world testing with LLMs

---

## Part 1: Validation & Quality (7 questions)

### Q1.1: Should Uselessness Be a Spec Violation?

**Context:** D2 identified that structurally valid traces can be completely useless (tautologies, confidence splat, disconnected DAGs).

**Options:**
- **A:** Keep spec as-is, document "usefulness guidelines" for Thinkers
- **B:** Add "actionability" as a validity constraint
- **C:** Develop a formal "usefulness checker" (similar to type checker)

**Trade-offs:**
- A is pragmatic but allows junk traces
- B makes CLAIR more rigorous but harder to produce
- C requires defining "useful," which is task-dependent

**Research needed:** Empirical study of whether Thinkers produce useless traces in practice.

### Q1.2: Can Uselessness Be Detected Automatically?

**Context:** D2 proposed 4 criteria (IG, DD, GC, AC), but can they be operationalized?

**Potential approaches:**
1. **Semantic similarity:** Check if content(b) ≈ content(justifications(b)) using embeddings
2. **Confidence variance:** Flag traces with σ²(confidence) < threshold
3. **Connectivity analysis:** Find disconnected islands in DAG
4. **LLM judgment:** Ask an LLM "Is this trace useful?"

**Problem:** All require defining "useful," which may be task-dependent.

**Research needed:** Develop automatic metric, test against human judgments.

### Q1.3: Is Usefulness Subjective?

**Context:** D2 noted that one Assembler's "useless" is another's "helpful context."

**Example:** BST theory island (D2 Example 3):
- **Novice Assembler:** Might find b2-b8 helpful (explains what BST is)
- **Expert Assembler:** Finds them redundant (knows what BST is)

**Question:** Should CLAIR encode target expertise level?

**Options:**
- Add `@expertise: novice|intermediate|expert` tag
- Assume "competent programmer" baseline
- Let Assemblers filter based on their needs

**Research needed:** Study how different expertise levels perceive trace usefulness.

### Q1.4: What is the Information Gain Threshold?

**Context:** D2 proposed IG(b) = H(content(b) | justifications(b)), but what's the threshold?

**Questions:**
- How much information gain is "enough"?
- Is IG a binary (useful/useless) or continuous (more/less useful)?
- Should threshold vary by belief position in DAG?

**Research needed:** Corpus study of useful vs useless traces to calibrate IG.

### Q1.5: How to Measure Actionability?

**Context:** D2 and D6 identified actionability (AC) as key criterion, but how to measure?

**Options:**
- **LLM judgment:** "Can you implement this belief?"
- **Template matching:** Does content match known actionable patterns?
- **Assembler feedback:** Do real Assemblers succeed?

**Problem:** Actionability depends on target language/platform.

**Research needed:** Develop language-agnostic actionability metric.

### Q1.6: Confidence Variance Threshold for DD?

**Context:** D2 proposed Decision Discriminance (DD) = var(confidence values at decision points).

**Question:** What threshold indicates "no decision signal"?

**Hypothesis:** σ² < 0.1 indicates no meaningful discrimination.

**Research needed:** Study confidence distributions in real traces to calibrate.

### Q1.7: Chain-Length Warning Threshold?

**Context:** D4 noted that 10-step chains collapse confidence to ~0.35.

**Question:** At what chain length should we warn Thinkers?

**Options:**
- 5 steps: 0.9^5 = 0.59 (moderate penalty)
- 7 steps: 0.9^7 = 0.48 (approaching uncertainty)
- 10 steps: 0.9^10 = 0.35 (barely above 0.5)

**Research needed:** Study chain lengths in real traces, identify typical patterns.

---

## Part 2: Stratification (6 questions)

### Q2.1: Is L0-Only Sufficient?

**Context:** D5 found that 90%+ of beliefs in real traces stay at L0.

**Question:** Can we define "CLAIR Lite" that omits levels entirely?

**Implications:**
- Simpler spec, easier to teach
- Loses meta-reasoning tracking (self-correction, comparison)
- May be sufficient for many use cases

**Research needed:** Study whether L0-only traces lose critical auditability.

### Q2.2: Alternative to Löb Discount?

**Context:** D5 found Löb discount (c → c²) is too aggressive for comparative meta-beliefs.

**Examples where it fails:**
- "I'm uncertain about my uncertainty" → ~0.5, but Löb gives 0.6² = 0.36
- "A > B" comparison → can be more confident than A or B individually

**Alternatives:**
- c → √c (weaker discount)
- No discount for comparative/qualitative meta-beliefs
- Discount only for "endorsement" meta-beliefs ("I believe X")

**Research needed:** Empirical study of meta-belief confidence in practice.

### Q2.3: Automatic Level Inference?

**Context:** D5 and A3 found LLMs struggle to assign correct levels.

**Question:** Can we detect meta-beliefs post-hoc and assign levels automatically?

**Approach:**
- If content references a belief ID ("b2 is wrong"), auto-promote to L1
- If content compares beliefs ("async better than thread pool"), auto-promote to L1
- If content qualifies confidence ("b2's confidence is limited"), auto-promote to L1

**Research needed:** Develop heuristics, test accuracy.

### Q2.4: Teaching LLMs Stratification?

**Context:** A3 found LLMs struggle with stratification even with few-shot examples.

**Question:** Can we develop better prompts, examples, or fine-tuning?

**Approaches:**
- Explicit "meta-belief patterns" documentation (D5 identified 4 patterns)
- Schematic examples for each pattern
- Negative examples showing misuse

**Research needed:** Develop training materials, measure improvement.

### Q2.5: Do Humans Query Meta-Reasoning?

**Context:** Stratification enables "why did you change your mind?" queries.

**Question:** Do humans actually ask these in practice, or is this theoretical?

**Research needed:** User study of audit scenarios, catalog query patterns.

### Q2.6: Confidence Source Field?

**Context:** D5 suggested distinguishing "confidence in X" from "confidence that X > Y."

**Proposal:** Add `confidence_source` field:
- `endorsement`: "I believe X" → strict Löb discount
- `comparison`: "X > Y" → relaxed discount
- `qualification`: "X is limited" → relaxed discount

**Research needed:** Test whether this distinction is useful in practice.

---

## Part 3: Confidence Operations (5 questions)

### Q3.1: Canonical Evaluation Order?

**Context:** D4 noted non-distributivity: `a × (b ⊕ c) ≠ (a × b) ⊕ (a × c)`.

**Question:** Should spec canonicalize ×-then-⊕ or ⊕-then-×? Does it matter?

**Example from D4:**
- Path 1: `conf(b4) ≤ 0.75 × 0.8 = 0.6`
- Path 2: `(0.5 × 0.8) ⊕ (0.5 × 0.8) = 0.64`

**Difference:** 0.6 vs 0.64 — small but non-zero.

**Research needed:** Study whether difference matters in practice, pick order.

### Q3.2: Multi-Justification Semantics Default?

**Context:** D4 and S2 identified three semantics (∧, ∨, min), but what's the default?

**Options:**
- Default to conjunction (∧) — most conservative
- Require explicit semantics — no ambiguity
- Infer from content — heuristic

**Research needed:** Study real traces to identify most common semantics.

### Q3.3: Confidence Granularity?

**Context:** D4 asked whether differences of 0.06 (0.375 vs 0.4375) matter.

**Question:** Should we use coarser granularity?

**Options:**
- Continuous: [0, 1] with arbitrary precision
- Coarse: {0.0, 0.25, 0.5, 0.75, 1.0}
- Fine: {0.0, 0.1, 0.2, ..., 1.0}

**Research needed:** Human study on confidence granularity discrimination.

### Q3.4: Defeater Calibration Rubric?

**Context:** D4 proposed rubric (0.9-1.0 fatal, 0.7-0.9 major, etc.) but is it accurate?

**Question:** How should Thinkers decide between 0.4 (concern) vs 0.8 (fatal)?

**Research needed:** Develop defeater taxonomy with examples for each level.

### Q3.5: Independence Testing?

**Context:** D4 noted ⊕ assumes independence, but Thinkers provide correlated evidence.

**Question:** How can Assemblers (or validators) detect correlated evidence?

**Approaches:**
- Semantic similarity: High similarity → correlation
- Justification overlap: Shared parents → correlation
- LLM judgment: "Are these independent?"

**Research needed:** Develop correlation detector, test accuracy.

---

## Part 4: Content & Language (5 questions)

### Q4.1: Should CLAIR Have Type Annotations?

**Context:** D3 noted context-dependency ("sort" means different things for different types).

**Proposal:** Add optional `type` field:
```
b2 .9 L0 @self <b1 "sort the items" :: [T] -> [T]
```

**Trade-offs:**
- **Pro:** Eliminates context-dependency
- **Con:** Breaks "opaque NL" design principle

**Research needed:** A/B test traces with/without type annotations.

### Q4.2: How to Handle Domain Knowledge?

**Context:** D3 noted that Assembler without BST knowledge fails on "successor or predecessor."

**Options:**
- A: Assume Assembler has domain knowledge (current approach)
- B: Include explanations in trace (more verbose but self-contained)
- C: Add `@requires` tag signaling needed domain knowledge

**Research needed:** Study common CS concepts, what can be assumed.

### Q4.3: What is the "Actionability Bar"?

**Context:** D6 identified boundary problem — when is content too vague or too specific?

**Question:** How much domain knowledge should we assume Assemblers have?

- Assume CS degree knowledge (trees, graphs, algorithms)?
- Assume only basic programming (loops, functions)?
- Something in between?

**Research needed:** Define "baseline Assembler" capabilities.

### Q4.4: Framework-Specific Patterns?

**Context:** D6 noted "use React useEffect" is framework-specific but strategy-level.

**Question:** Should CLAIR capture framework-specific intent?

**Example:** "fetch data when component mounts" (generic) vs "use useEffect to fetch on mount" (React-specific)

**Research needed:** Study trade-offs between framework-agnostic and -specific traces.

### Q4.5: When Is "Pseudocode" Better?

**Context:** D6 noted natural language struggles with structural patterns.

**Example:** "for each item: transform(item) → collect(results)" is nearly code but clearer than prose.

**Question:** Should CLAIR allow structured content (e.g., simple templating) for common patterns?

**Research needed:** Study human readability of pseudocode vs prose.

---

## Part 5: Architecture & Protocol (4 questions)

### Q5.1: Pushback Protocol Design?

**Context:** B3 proposed pushback protocol — Assembler signals ambiguity to Thinker.

**Question:** How should this work in practice?

**Options:**
- Synchronous: Thinker waits for Assembler feedback
- Asynchronous: Assembler logs warnings, Thinker reviews later
- Multi-turn: Iterative refinement

**Research needed:** Prototype pushback system, measure effectiveness.

### Q5.2: Invalidation Syntax Extension?

**Context:** S2 proposed `INVALIDATED_BY` for complex invalidation logic.

**Question:** Should invalidation be a separate belief type?

**Current:** `?["condition"]` inline with belief
**Proposed:** Separate invalidation beliefs

**Research needed:** Study complex invalidation scenarios, design syntax.

### Q5.3: Source Tag Extensions?

**Context:** S2 proposed `@tool`, `@doc`, `@test`, `@reviewer`, `@metric` tags.

**Question:** Which are essential vs nice-to-have?

**Research needed:** Study real traces, identify common source types.

### Q5.4: Query Protocol?

**Context:** C1 catalogued 10 query patterns but didn't specify protocol.

**Question:** How should auditors query traces?

**Options:**
- SQL-like: `SELECT * WHERE confidence > 0.8`
- Natural language: "Show all high-confidence beliefs about JWT"
- Programmatic: Python API for traversal

**Research needed:** Design and implement query interface.

---

## Part 6: Empirical Studies (8 questions)

### Q6.1: Can Thinkers Produce High-Quality Traces?

**Context:** All explorations used hand-authored traces.

**Question:** Can real LLMs (e.g., GPT-4, Claude) produce useful traces with just guidelines?

**Research needed:** Prompt Thinker LLMs, measure trace quality (IG, DD, GC, AC).

### Q6.2: Do Assemblers Produce Better Code from CLAIR?

**Context:** B1 claimed 5 fidelity improvements, but these were hypothetical.

**Question:** In controlled experiments, does CLAIR actually improve code quality?

**Research needed:** A/B test: Assembler gets CLAIR vs natural language, measure code quality.

### Q6.3: Scale Test — 30-40 Belief Breakpoint?

**Context:** C2 identified 30-40 beliefs as human readability limit.

**Question:** Is this accurate? Can we improve it?

**Research needed:** User study with traces of varying lengths, measure comprehension.

### Q6.4: Reconstruction Success Rate?

**Context:** C3 claimed 4/5 traces successfully reconstructed.

**Question:** Is this reproducible? What makes traces fail?

**Research needed:** Give auditors traces with missing beliefs, measure reconstruction accuracy.

### Q6.5: Teachability Experiments?

**Context:** A3 found LLMs struggle with stratification.

**Question:** Can improved training materials fix this?

**Research needed:** A/B test prompts with/without stratification guidelines.

### Q6.6: Confidence Calibration by Domain?

**Context:** A4 noted objective vs subjective domains differ.

**Question:** Which domains need 1.0 confidence vs <1.0?

**Domains to study:**
- Mathematical deduction (use 1.0)
- API design (use <1.0)
- Debugging (use <1.0)
- Algorithm selection (use <1.0)

**Research needed:** Corpus study across domains, develop calibration guidelines.

### Q6.7: Real-World Trace Corpus?

**Context:** All explorations used synthetic examples.

**Question:** What do real traces look like in production?

**Research needed:** Collect corpus of real Thinker→Assembler traces, analyze patterns.

### Q6.8: Auditor User Study?

**Context:** C1 catalogued query patterns but didn't test with real auditors.

**Question:** What queries do auditors actually ask?

**Research needed:** User study: give auditors traces, catalog their questions.

---

## Summary by Priority

### HIGH Priority (blocks deployment)
1. **Q1.1:** Should usefulness be a spec violation? (Affects spec v0.2)
2. **Q3.1:** Canonical evaluation order? (Blocks implementation)
3. **Q3.2:** Multi-justification semantics default? (Blocks spec)
4. **Q6.1:** Can Thinkers produce high-quality traces? (Validates whole approach)

### MEDIUM Priority (refines design)
5. **Q1.2:** Can uselessness be detected automatically? (Tooling)
6. **Q2.1:** Is L0-only sufficient? (Simplifies spec)
7. **Q2.2:** Alternative to Löb discount? (Fixes stratification)
8. **Q4.1:** Should CLAIR have type annotations? (Major design decision)
9. **Q5.1:** Pushback protocol design? (Architecture)
10. **Q6.2:** Do Assemblers produce better code? (Validation)

### LOW Priority (future research)
11. **Q1.3:** Is usefulness subjective? (Philosophical)
12. **Q2.6:** Confidence source field? (Nice-to-have)
13. **Q3.4:** Defeater calibration rubric? (Guidelines)
14. **Q4.4:** Framework-specific patterns? (Best practices)
15. **Q6.3-Q6.8:** Various empirical studies (Data collection)

---

## Research Roadmap

### Phase 1: Critical Decisions (Months 1-2)
- Resolve Q1.1, Q3.1, Q3.2 → Finalize spec v0.2
- Run Q6.1 (Thinker production) → Validate feasibility

### Phase 2: Implementation (Months 3-4)
- Implement validator with Q1.2 (uselessness detection)
- Resolve Q2.1, Q2.2 (stratification decisions)
- Run Q6.2 (Assembler consumption) → Measure improvement

### Phase 3: Refinement (Months 5-6)
- Address Q4.1 (type annotations) if needed
- Implement Q5.1 (pushback protocol)
- Run remaining empirical studies (Q6.3-Q6.8)

### Phase 4: Production (Months 7+)
- Deploy to real Thinker→Assembler pipelines
- Collect real traces (Q6.7)
- Iterate based on production data

---

## Conclusion

The explorations identified **30+ open questions**, but most are addressable through:
1. **Empirical studies** with real LLMs (Q6.1-Q6.8)
2. **Spec refinements** based on theoretical analysis (Q1.1, Q3.1, Q3.2)
3. **Tooling development** for validation and query (Q1.2, Q5.1, Q5.4)
4. **Guidelines and training materials** (Q2.4, Q3.4, Q4.2)

The questions are **researchable**, not fundamental blockers. The path to production-ready CLAIR is clear.
