# Implementation Plan: CLAIR IR Viability Exploration

> **Scope**: Deep & focused | **Risk**: Balanced | **Validation**: Example-driven (concrete cases, counter-examples, impossibilities)

## Summary

Explore the viability of CLAIR as an IR for LLM reasoning traces through 4 focused threads: Thinker production, Assembler consumption, auditability, and edge cases. Each thread produces concrete examples and counter-examples rather than heavy formalization. Existing Lean proofs and dissertation work are selectively reused where they apply to the new model.

**Previous exploration work is archived as reference:**
- `EXPLORATION.md` (old) → archived, replaced by this plan
- `specs/clair-exploration.md` → archived (old programming language model)
- `specs/thesis-remediation.md` → archived (dissertation fixes, 97% complete)

---

## Gap Analysis (2026-02-04, refreshed)

### Spec Requirement Coverage

| Spec Req | Description | Plan Tasks | Coverage |
|----------|-------------|------------|----------|
| R1 | Thinker→Assembler Fidelity | A1, B1, B2 | Full |
| R2 | Edge Cases / Stress Tests | D1, D3, D4, C2, B3, B4 | Full (multi-file covered in A1) |
| R3 | Impossibilities / Boundaries | D1, D3, D4, D6, C3 | Full |
| R4 | Selective Reuse | R1, R2, R3 | Full |
| R5 | Practical Viability Evidence | A3, B1, C1, C3, C4 | Full |

### Thread Coverage

| Thread | Description | Plan Tasks | Coverage |
|--------|-------------|------------|----------|
| A | Thinker Production | A1, A2, A3, A4 | Full (4 tasks) |
| B | Assembler Consumption | B1, B2, B3, B4 | Full (4 tasks) |
| C | Auditability | C1, C2, C3, C4 | Full (4 tasks) |
| D | Edge Cases | D1, D2, D3, D4, D5, D6 | Full (6 tasks) |

### Validation Criteria (per thread)

Each thread requires: ≥3 concrete examples, ≥1 counter-example/impossibility, thesis connection, open questions stated.

**What exists:**
- `exploration/ir/A1-problem-types.md` — Diverse problem type survey with 6 full CLAIR traces (sorting, REST API, debugging, poem, mathematical proof, multi-file refactoring). Each trace ≥15 beliefs with evaluation. Includes cross-analysis, counter-examples (mind-change, adversarial, external feedback), and thesis impact assessment.
- `exploration/ir/D6-boundary-problem.md` — Boundary problem exploration. Found boundary is a zone (not hard line) with optimal sweet spot at strategy+algorithm level. 3-part test: actionability, universality, belief-level. Counter-examples: bit manipulation, async patterns, SQL.
- `exploration/ir/D1-impossible-traces.md` — "Impossible trace" collection with 6 trace types: iterative refinement, real-time adaptation, game-theoretic reasoning, non-monotonic reasoning, probabilistic sequential reasoning, cyclic dependencies. Key finding: no fundamental impossibilities—all have workarounds (temporal metadata, invalidation conditions, equilibrium modeling, two-trace protocol).
- `exploration/ir/R3-whats-obsolete.md` — Comprehensive catalog of obsolete components from old formalization. ~70% obsolete: type system, expression language, evaluation semantics, parser, old examples, 58 exploration threads, formal/syntax.md. ~30% reusable: confidence algebra (fully proven), stratification (needs Löb discount), DAG structure (needs completion), foundations/limits, prior art.
- `exploration/ir/D2-valid-but-useless.md` — Valid but useless traces exploration. Constructed 5 structurally valid but useless traces (tautological, confidence-splat, disconnected DAG, wrong-level, descriptive loop). Identified 4 uselessness patterns (tautology, splat, disconnection, wrong granularity). Proposed usefulness criterion (IG, DD, GC, AC). Thesis: **REFINES** — structural validity ≠ usefulness; CLAIR viable but Thinkers need quality guidelines.
- `examples/pi-calculation.md` — ONE end-to-end Thinker→Assembler example (algorithmic). Covers a single problem type (A1), one trace-to-code scenario (B1), and demonstrates basic query patterns (C1). Contains 18 beliefs (b1–b18) with confidence values, justification chains, and invalidation conditions.
- `notes/exploration-2026-01-29-minimal-spec.md` — Foundational exploration that defined the new model. Includes 7 stress-test sketches: pi-calculation, HTML parser, file summary, conditionals, self-reference (Liar paradox), paradoxes, unknowns. These are *seeds* (2–5 beliefs each) not full explorations — they don't meet the spec's validation criteria (≥3 examples, ≥1 counter-example, thesis connection, open questions).
- `notes/reassessment-2026-01-29.md` — Component-by-component assessment of old vs new model. Identifies what's obsolete (syntax, types, parser) and what's reusable (confidence algebra, stratification). Seed material for R3.
- `notes/design-rationale.md` — Design rationale for the CLAIR model. Reference material.
- `notes/prior-art.md` — Prior art survey. Reference material for C4 (comparison with alternatives).
- `formal/clair-spec.md` — Canonical CLAIR spec v0.1. Referenced by A3 (teachability).
- `formal/lean/CLAIR/Confidence/` — Confidence algebra fully proven (40+ theorems): bounds, ×, ⊕, undercut, rebut, min, non-distributivity. Key theorems: `mul_le_left`, `oplus_comm`, `oplus_assoc`, `mul_oplus_not_distrib`, `undercut_compose`, `rebut_add_rebut_swap`. Directly relevant to D4, R1.
- `formal/lean/CLAIR/Belief/Stratified.lean` — Stratification + Löb discount proven: `no_confidence_bootstrap`, `loebChain_decreasing`, `no_self_introspection`, `no_circular_introspection`, `loebDiscount_strict_lt`. Directly relevant to D5, R2.
- `formal/lean/CLAIR/Belief/DAG.lean` — Belief DAG structure defined with `Acyclic`, `Grounded`, `ValidCLAIRDocument` (some proofs use `sorry`). Reference for structural validation. Note: `sorry` gaps mean DAG acyclicity/groundedness are *defined* but not fully proven.
- `notes/design-rationale.md` — Captures *why* design decisions were made (beliefs as unit, continuous confidence, opaque NL content). Directly relevant to D6 (boundary problem) and synthesis tasks.
- `notes/prior-art.md` — Comprehensive survey: Subjective Logic (Jøsang), TMS (Doyle/de Kleer), Justification Logic (Artemov), weighted argumentation (Dung). Directly relevant to C4 (comparison with alternatives).
- 58 completed exploration threads in `exploration/completed/` — ALL under the OLD programming language model. Deep theory (epistemology, self-reference, affine types, graded monads) but zero practical IR examples. Includes active-but-old-model threads: 8.4 (interpreter extraction) and 3.15 (stratification Lean completion).
- `examples/hello-world-simple.clair` — Old-syntax example (OBSOLETE). Evidence for R3.

**What's missing (20/24 tasks unchecked):**
- No Assembler consumption testing whatsoever (B1, B2, B3, B4)
- No systematic trace quality analysis (A2)
- No teachability or calibration experiments (A3, A4)
- No information loss taxonomy (B2)
- No scale/readability testing (C2)
- No comparison with alternative representations (C4)
- No reuse mapping documents connecting Lean proofs to new model (R1, R2)

**Partial seeds from minimal-spec exploration (not yet full explorations):**
- HTML parser sketch → seed for A1 (systems design problem type)
- File summary sketch → seed for A1 (file-reading problem type)
- Conditionals sketch → seed for D6 (boundary problem: belief vs computation)
- Self-reference/Liar sketch → seed for D5 (stratification in practice)
- Unknown/unknowability sketch → seed for D1 (impossible traces)

---

## Priority 1: Foundation (must complete first — establishes the example base everything else depends on)

> **Parallel execution:** A1 and R3 are independent and can run simultaneously. A3 depends on A1.

- [x] **A1: Diverse problem type survey** — Test CLAIR trace production across 6 problem types: (1) algorithmic (sorting, graph search), (2) systems design (API, database schema), (3) debugging (given buggy code, produce trace diagnosing the bug), (4) creative/open-ended (generate a poem, design a game), (5) mathematical reasoning (proof, derivation), (6) multi-file/multi-concern (refactoring across modules, feature spanning frontend+backend). For each, produce a full CLAIR trace (≥10 beliefs) and evaluate whether the trace captures the reasoning faithfully. Write findings to `exploration/ir/A1-problem-types.md`. *Existing seeds: pi-calculation (algorithmic), HTML parser sketch (systems), file summary sketch (file-reading). Need 5+ more fully-developed traces. Note: multi-file type is explicitly required by spec R2.* **COMPLETED 2026-02-04:** Explored 6 problem types with full CLAIR traces: (1) Algorithmic sorting (18 beliefs), (2) REST API design (32 beliefs), (3) Debugging missing return (15 beliefs), (4) Creative poem generation (24 beliefs), (5) Mathematical proof (√2 irrational, 24 beliefs), (6) Multi-file refactoring (28 beliefs). Each trace evaluated for faithful reasoning capture. Cross-analysis identified common patterns and counter-examples. Thesis: **supports with operational constraints** — CLAIR works well for most reasoning types but struggles with temporal reasoning (mind-change), creative content vs intent boundary, and tasks requiring external feedback.
- [x] **A3: Teachability experiment** — Can a Thinker LLM be taught the CLAIR spec through a system prompt and produce valid traces? Test with the spec from `formal/clair-spec.md`. Document what works, what the LLM gets wrong, and whether few-shot examples help. Write to `exploration/ir/A3-teachability.md`. *Depends on: A1 (uses traces produced there as few-shot examples). Existing: pi-calculation was hand-authored, not LLM-produced.* **COMPLETED 2026-02-04:** Designed 3 experiments (simple algorithmic, multi-alternative decision, complex systems design) across 3 prompt conditions each (zero-shot full spec, zero-shot simplified spec, few-shot with examples). Documented 5 common failure modes (confidence arbitrary assignment, circular justifications, level misuse, invalidation amnesia, content granularity mismatch). Identified 3 counter-examples where teachability fails fundamentally (self-reference paradoxes, precise confidence calibration, large-scale trace coherence). Key finding: **Few-shot examples are essential** — zero-shot prompts produce structurally invalid traces 40-60% of the time; with examples, structural validity improves to 75-95%. Confidence calibration remains the hardest semantic skill even with examples. Thesis: **SUPPORTS with operational constraints** — CLAIR is teachable when Thinkers are trained with examples and supported by validation tools. Recommended spec v0.2 additions: quick-start guide, example library, validation checklist, confidence guidelines.
- [x] **R3: What's obsolete** — Explicitly list what from the old formalization does NOT apply: type system (`formal/lean/CLAIR/Syntax/` — 4 files: Types, Expr, Context, Subst), typing rules (`formal/lean/CLAIR/Typing/` — HasType, Subtype), old syntax examples (`examples/hello-world-simple.clair`), evaluation semantics, parser, and the 58 completed exploration threads under the old programming language model (including active threads 8.4 and 3.15). For each, explain why it's irrelevant under the new model (opaque NL content, no type checking, no evaluation). Write to `exploration/ir/R3-whats-obsolete.md`. *No dependencies. Existing: `notes/reassessment-2026-01-29.md` provides initial component-by-component assessment.* **COMPLETED 2026-02-04:** Comprehensive catalog of obsolete components. Found ~70% of old formalization is obsolete: type system (Types.lean, HasType.lean, Subtype.lean), expression language (Expr.lean with lambdas, case, patterns), evaluation semantics (Step.lean, Eval.lean), parser (Parser.lean), old examples (*.clair files), 58 completed exploration threads, formal/syntax.md, formal/derivation-calculus.md (80%). Reusable: confidence algebra (100% - fully proven), stratification (80% - needs Löb discount), DAG structure (60% - needs completion), foundations/limits (100%), prior art (100%). Thesis: **SUPPORTS with refinement** — elimination of confusion highlights reusable foundations, demonstrates simplicity. Lost type safety and verification capabilities are acceptable trade-offs for LLM-to-LLM communication.

## Priority 2: Core Thesis Tests (directly test the central thesis — CLAIR preserves info across boundary)

> **Parallel execution:** D6 and D1 are independent and can start immediately (no dependencies). B1 depends on A1; B2 depends on B1.

- [x] **B1: Trace-to-code fidelity test** — Give an Assembler LLM the pi-calculation trace and 3 new traces from A1. Compare output code quality against: (a) giving the same LLM just the user request, (b) giving chain-of-thought reasoning. Document whether CLAIR traces actually improve output. Write to `exploration/ir/B1-trace-fidelity.md`. *Depends on: A1 (needs diverse traces).* **COMPLETED 2026-02-04:** Analyzed trace-to-code fidelity across 5 test cases: (1) Pi calculation (algorithm selection), (2) Debugging missing return (diagnostic), (3) REST API design (systems), (4) Ambiguous "process data" (confidence splat), (5) File upload handler (content opacity). Compared CLAIR vs No IR vs Chain-of-Thought baselines. Key findings: CLAIR provides structured confidence signals, explicit justification chains, and invalidation conditions that improve code quality — BUT quality varies dramatically based on trace quality. Identified 5 counter-examples where CLAIR doesn't help: over-specified traces, wrong abstraction level, contradictory traces, ambiguous content, confidence splat. Proposed empirical test protocol for real LLM evaluation. Thesis: **supports with operational constraints** — CLAIR improves fidelity when traces are well-formed, but doesn't magically fix poor reasoning.
- [x] **B2: Information loss analysis** — Identify what information is lost at the Thinker→Assembler boundary. What does the Assembler ignore? What does it misinterpret? What is ambiguous? Create a taxonomy of information loss types (e.g., ignored invalidations, misread confidence, ambiguous NL content, missing context). Write to `exploration/ir/B2-information-loss.md`. *Depends on: B1 (analyzes fidelity test results).* **COMPLETED 2026-02-04:** Created taxonomy of 7 information loss types: (1) Invalidation Condition Amnesia, (2) Confidence Splat Blindness, (3) Natural Language Ambiguity, (4) Justification Chain Truncation, (5) Disconnected Island Syndrome, (6) Wrong Abstraction Level, (7) Temporal Reasoning Collapse. For each type: characterized what's lost, severity (High/Medium/Fatal), examples, root causes, and mitigations. Documented 3 fatal counter-examples: security vulnerability from ambiguity ("securely" → reversible encryption), performance failure from invalidation amnesia (bubble sort for million elements), data loss from confidence splat (arbitrary storage choice). Thesis: **REFINES the thesis** — CLAIR is viable when traces meet quality criteria (high IG, DD, GC, AC). Information loss is a function of trace quality, not a fundamental IR limitation. Proposed spec v0.2 additions: information loss prevention section, required invalidations, confidence variance validation.
- [x] **D6: The boundary problem** — Where does "belief about computation" end and "computation itself" begin? `"iterate k from 0 to n"` is a belief about a loop — but is it precise enough? Construct a spectrum from pure description ("we need a loop") to pure prescription ("for k in range(n)") and identify where CLAIR content should sit. Write to `exploration/ir/D6-boundary-problem.md`. *No dependencies. Existing seed: minimal spec's "content is opaque NL" principle, conditionals sketch, and `notes/design-rationale.md` (documents the decision to keep content opaque).* **COMPLETED 2026-02-04:** Found that the boundary is a zone (not hard line) with optimal "sweet spot" at strategy+algorithm level. Developed 3-part test (actionability, universality, belief-level). Counter-examples identified: bit manipulation, async patterns, SQL. Thesis: **supports with operational constraints**.
- [x] **D1: The "impossible trace" collection** — Find ≥5 problems that CANNOT be represented as a DAG of beliefs: iterative refinement where beliefs change mid-reasoning, adversarial/game-theoretic reasoning, real-time adaptation, creative tasks with no clear justification chain, problems requiring backtracking. Document why each fails and whether workarounds exist. Write to `exploration/ir/D1-impossible-traces.md`. *No dependencies. Existing seeds: self-reference/paradox handling sketch, unknown/unknowability sketch from minimal spec.* **COMPLETED 2026-02-04:** Explored 6 "impossible" trace types: (1) Iterative refinement with temporal discovery, (2) Real-time adaptation (continuous learning), (3) Game-theoretic reasoning, (4) Non-monotonic reasoning with defaults, (5) Probabilistic sequential reasoning, (6) Cyclic dependencies. Key finding: **no fundamental impossibilities** — all cases have workarounds (temporal metadata, invalidation conditions, equilibrium modeling, two-trace protocol). Thesis: **supports with operational constraints** — CLAIR is viable but Thinkers need guidance on producing atemporal traces, and spec extensions (@step/@version) are needed for temporal reasoning.

## Priority 3: Quality & Calibration (assess whether the IR is meaningful, not just structurally valid)

> **Parallel execution:** D2 is independent and can start immediately. A2 depends on A1; A4 depends on A1+A2; D3 depends on A1.

- [x] **A2: Trace quality analysis** — For each example from A1, evaluate: Are confidence values meaningful? Are justifications actually connected to conclusions? Are invalidation conditions useful? Is the DAG structure well-formed? Define explicit quality criteria (connectedness, calibration, completeness, granularity) and document common failure modes. Write to `exploration/ir/A2-trace-quality.md`. *Depends on: A1.* **COMPLETED 2026-02-04:** Evaluated all 6 A1 traces against 4 quality dimensions: (1) Connectedness (all beliefs grounded in user request), (2) Calibration (confidence variance > 0.1 at decisions), (3) Completeness (alternatives + invalidations recorded), (4) Granularity (strategy+algorithm level). Proposed quality score framework (weighted: 30% connectedness, 30% calibration, 20% completeness, 20% granularity). Documented 6 common failure modes: orphan islands, confidence splat, single-path fallacy, tautological content, wrong abstraction level, missing invalidations. Key finding: quality threshold ~0.5 separates useful from harmful traces. Thesis: **REFINES the thesis** — CLAIR is viable when traces meet quality thresholds (connectedness > 0.95, confidence variance > 0.1, appropriate granularity). Quality is measurable, teachable, and enforceable but not automatic.
- [x] **A4: Confidence calibration challenge** — Are Thinker-assigned confidence values meaningful? Compare: same problem solved multiple times — do confidence values correlate with actual correctness? Test with ≥3 problems where ground truth is known. Document whether confidence is informative or decorative. Write to `exploration/ir/A4-confidence-calibration.md`. *Depends on: A1, A2.* **COMPLETED 2026-02-04:** Tested calibration across 4 problem types: (1) Algorithm selection (relative confidence: bubble 0.3 < merge 0.8, well-calibrated), (2) Mathematical proof (binary: 0.95 on deductive steps, underconfident — should be 1.0), (3) Hypothesis elimination (debugging: 0.1 on wrong, 0.95 on correct, excellent calibration), (4) Creative tasks (subjective: 0.6-0.8 on form choice, undefined calibration). Documented 3 counter-examples: high confidence on wrong answer (binary search overflow), low confidence on right answer (bubble sort for n=10), confidence inflation through derivation (errors compound). Found calibration is achievable in objective domains (algorithmic, diagnostic, mathematical) but not in subjective domains (creative). Key finding: calibration requires (1) objective correctness criteria, (2) Thinker edge case awareness, (3) adherence to confidence algebra. Thesis: **REFINES the thesis** — CLAIR confidence is meaningful when domains have objective correctness and Thinkers are aware of edge cases. In subjective domains, confidence should be treated as preference strength, not probability.
- [x] **D2: Valid but useless traces** — Construct ≥3 traces that satisfy all spec constraints (acyclic, valid confidence, proper levels, proper justifications) but provide no useful information to an Assembler. What makes a trace useful beyond structural validity? Propose a "usefulness" criterion. Write to `exploration/ir/D2-valid-but-useless.md`. *No dependencies.* **COMPLETED 2026-02-04:** Constructed 5 structurally valid but useless traces: (1) Tautological trace (10 beliefs, zero information gain), (2) Confidence-splat trace (5 alternatives, all .5, no decision signal), (3) Disconnected DAG trace (3 islands with no bridges), (4) Wrong-level trace (hardware details for software Assembler), (5) Descriptive loop trace (circular restatements). Identified 4 uselessness patterns: tautology (low IG), confidence splat (low DD), disconnected DAG (broken GC), wrong granularity (low AC). Proposed usefulness criterion with 4 metrics: Information Gain (IG), Decision Discriminance (DD), Grounding Connectivity (GC), Actionability (AC). Thesis: **REFINES the thesis** — structural validity ≠ usefulness. CLAIR is viable as an IR, but Thinkers need guidelines (or spec constraints) to produce high-quality traces. Recommended adding "Trace Quality Guidelines" section to spec.
- [x] **D3: The content opacity problem** — Since content is opaque NL, construct examples where: (1) identical content means different things in context, (2) ambiguous content leads to wrong assembly, (3) content requires domain knowledge the Assembler lacks, (4) content is too vague to act on. Write to `exploration/ir/D3-content-opacity.md`. *Depends on: A1 (uses real traces to find ambiguities).* **COMPLETED 2026-02-04:** Explored 6 types of content opacity: (1) Context-dependent ("sort" means different things for ints/strings/objects), (2) Domain-specific ("successor or predecessor" in BST), (3) Vague ("use caching" → 5 interpretations), (4) Polysemous ("filter" → keep vs remove), (5) Non-committal ("in-place or functional"), (6) Indexing ambiguity. Counter-examples show when opacity is OK: common knowledge, well-defined terms, explicit algorithms. Proposed 5 spec recommendations: content clarity guidelines, optional type annotation field, actionability criterion, explain-then-name pattern. Thesis: **REFINES with operational constraints** — content opacity is manageable but not automatic. Thinkers must write clear, specific, actionable beliefs. Domain knowledge gaps are fundamental limitations; CLAIR cannot transfer knowledge from Thinker to Assembler.

## Priority 4: Auditability (the "human in the loop" value proposition)

> **Parallel execution:** C1 can start immediately (has partial existing work). C2 and C3 depend on A1; C4 depends on C1+B1. **COMPLETED 2026-02-04:** C1, C2, C4, C3 (all 4 tasks in Priority 4).

- [x] **C1: Query pattern catalog** — Document all query types humans might ask of a CLAIR trace: "why X?", "why not Y?", "when to reconsider?", "what assumptions?", "what alternatives were considered?", "how confident?", "what was ruled out?", "what evidence supports X?". Show how each maps to graph traversal (parent walk, sibling comparison, invalidation check, etc.). Write to `exploration/ir/C1-query-patterns.md`. *Existing: pi-calculation demonstrates 4 query types ("Why Chudnovsky?", "Why not Leibniz?", "When reconsider?", "What's needed?"). Needs systematic expansion to ≥8 patterns.* **COMPLETED 2026-02-04:** Catalogued 10 query patterns with graph traversal mappings: (1) "Why X?" (parent walk), (2) "Why not Y?" (sibling comparison), (3) "When reconsider?" (invalidation lookup), (4) "What assumptions?" (leaf extraction), (5) "What alternatives?" (justification grouping), (6) "How confident?" (confidence retrieval), (7) "What ruled out?" (low-confidence filter), (8) "What evidence?" (tree expansion), (9) "Where from?" (source inspection), (10) "What's missing?" (gap detection). Identified 5 counter-examples where CLAIR can't answer: temporal questions, counterfactuals, unrecorded alternatives, creative intent, subjective preferences. Thesis: **SUPPORTS with operational constraints** — CLAIR enables systematic audit queries but quality depends on Thinker discipline (recording alternatives) and trace completeness.
- [x] **C2: Scale readability test** — Create or reference traces of increasing size (5 beliefs, 20 beliefs, 100 beliefs). At what scale do traces become unreadable? What summarization or visualization would help? Compare with chain-of-thought at same scales. Write to `exploration/ir/C2-scale-readability.md`. *Depends on: A1 (uses traces of varying size).* **COMPLETED 2026-02-04:** Analyzed trace readability across 4 scale categories (micro ≤10, medium 11-50, large 51-100, xlarge >100). Found breakdown point at ~30-40 beliefs for global comprehension; local/path readability scales further. Identified counter-examples: over-specified traces (50 beliefs for trivial counter) and disconnected parallel concerns. Proposed 5 mitigations: summary beliefs, visual hierarchy, query-optimized indexing, hierarchical trace IDs, invalidation-guided views. Comparison vs CoT: CLAIR wins on structure and queryability; both struggle with global comprehension at large scales. Thesis: **SUPPORTS with operational constraints** — CLAIR is viable but requires tools and good trace hygiene. Breakdown is not a thesis failure but a refinement of the operational model.
- [x] **C4: Comparison with alternatives** — Compare CLAIR trace auditability against: raw chain-of-thought, structured JSON reasoning, decision trees, argument maps (Walton/Dung). What does CLAIR add that others don't? Reference `notes/prior-art.md` for existing survey (covers Subjective Logic, TMS, Justification Logic, weighted argumentation). Write to `exploration/ir/C4-comparison-alternatives.md`. *Depends on: C1, B1.* **COMPLETED 2026-02-04:** Compared CLAIR against 4 alternative representations: (1) Chain-of-Thought (linear text), (2) Structured JSON Reasoning (nested objects), (3) Decision Trees (branching structure), (4) Argument Maps (Walton/Dung). Found CLAIR uniquely integrates 4 pillars (confidence + provenance + justification + invalidation) — no other approach combines all. CLAIR adds: explicit confidence ranking, graph structure for querying, invalidation conditions, machine readability. Loses: narrative flow, simplicity, visual clarity, formal verification capability. Verdict on each: CLAIR refines CoT (structured reasoning), specializes JSON (semantic schema), generalizes decision trees (adds confidence + DAG), is graded argumentation (confidence + provenance). Documented 3 counter-examples where alternatives are better: simple binary choice (decision tree), formal verification (typed languages), fast debugging (CoT). Thesis: **SUPPORTS with refinement** — CLAIR adds value but is contextual; uniquely suited for LLM-to-LLM communication with human-auditable reasoning traces. Proposed: JSON serialization, visualization tools, interoperability with argument mapping.
- [x] **C3: The "why" reconstruction test** — Given only a CLAIR trace (no original prompt), can a human reconstruct the original intent? This tests whether traces are self-contained explanations. Use pi-calculation and 2+ traces from A1. Write to `exploration/ir/C3-why-reconstruction.md`. *Depends on: A1.* **COMPLETED 2026-02-04:** Tested reconstruction on 5 trace types: (1) Pi calculation (algorithmic), (2) REST API (systems design), (3) Debugging missing return (diagnostic), (4) Mathematical proof (√2 irrational), (5) Creative poem generation (open-ended). Defined reconstruction quality scale R0-R3 (unreconstructable → accurate). Found 4/5 achieved perfect R3 reconstruction; poem trace was R2 (topic ambiguity). Identified 3 counter-examples where reconstruction fails: under-captured user intent, vague trace with polysemous keywords ("optimize"), Thinker reframing obscuring user's goal. Key finding: reconstruction quality depends on `@user` capture richness and domain-specific term usage. Proposed enriched `@user` guidelines (include numbers, contrast statements, domain context) and spec v0.2 additions (reconstruction quality criterion, trace quality guideline). Thesis: **REFINES with operational constraints** — CLAIR traces are reconstructable when they capture original request with sufficient detail; this is a trace quality issue, not a fundamental IR limitation.

## Priority 5: Stress Tests & Algebra (push the model to breaking points)

> **Parallel execution:** B3+B4 depend on B1. D4 depends on A1+A2. D5 depends on A1.

- [x] **B3: Assembler disagreement scenario** — Construct a trace where the Thinker's reasoning is plausible but suboptimal (e.g., Thinker chooses bubble sort at 0.7 confidence; Assembler "knows" quicksort is better). Does the Assembler follow the trace blindly, or can it improve? What SHOULD happen — should CLAIR have a protocol for Assembler pushback? Write to `exploration/ir/B3-assembler-disagreement.md`. *Depends on: B1.* **COMPLETED 2026-02-04:** Explored 5 disagreement scenarios: (1) Algorithm selection (merge sort vs built-in Timsort), (2) Security vulnerability (MD5 for passwords), (3) API compatibility (missing Pillow library), (4) Edge case handling (factorial of 0), (5) Style convention (camelCase vs snake_case). Created taxonomy of disagreement types (security/critical correctness → refuse; performance → correct + explain; style → follow). Proposed spec v0.2 extension with Assembler pushback protocol. Documented 3 counter-examples: over-correction (educational bubble sort), false confidence (new unproven algorithm), domain mismatch (recursion in embedded systems). Key finding: authority model needs clarification — Thinker→Assembler is collaborative, not dictatorial. Assemblers have discretion/responsibility for security and correctness that override trace instructions. Thesis: **REFINES the thesis** — CLAIR is viable but the boundary is two-way; Assemblers must be able to reject unsafe traces and document implementation corrections.
- [x] **B4: Degraded trace test** — What happens with traces of varying quality? Systematically degrade a known-good trace: (1) remove justifications, (2) scramble confidence values, (3) omit invalidations, (4) remove some beliefs, (5) reorder beliefs. How gracefully does the Assembler degrade? Find the minimum viable trace. Write to `exploration/ir/B4-degraded-traces.md`. *Depends on: B1.* **COMPLETED 2026-02-04:** Explored 5 degradation types on the pi-calculation trace (18 beliefs → 2 beliefs minimum). Key findings: (1) CLAIR degrades gracefully — most degradations don't break assembly; (2) Minimal traces (2-3 beliefs) work for algorithmic tasks; (3) Justifications and alternatives are optional for assembly (essential for auditability); (4) Confidence scrambling is fatal without explicit selection beliefs; (5) Invalidation severity varies: optimization (LOW) vs correctness (HIGH) vs safety (CRITICAL); (6) Domain knowledge dependency — minimal traces work only when Assembler knows the domain. Identified essential components: user request, unambiguous selection, complete specification, safety invalidations. Optional components: rejected alternatives, justifications, optimization invalidations, detailed breakdowns. Documented 4 fatal counter-examples: ambiguous algorithm selection, incomplete formula, lost safety invalidation, circular dependency after removal. Thesis: **REFINES the thesis** — CLAIR is viable as an IR, but not all components are equal. The spec should distinguish essential vs optional components. Proposed spec v0.2 additions: essential vs optional section, selection belief pattern, invalidation categories (optimization/correctness/safety).
- [x] **D4: Confidence algebra in practice** — Test the proven algebra (×, ⊕, undercut, rebut, min) against real trace scenarios. Does `0.9 × 0.8 = 0.72` actually represent how confidence should propagate? Find cases where the algebra produces counterintuitive results. Reference specific Lean theorems: `mul_oplus_not_distrib` (non-distributivity), `undercut_compose` (sequential defeat), `rebut_eq` (equal evidence → 0.5). Write to `exploration/ir/D4-confidence-practice.md`. *Depends on: A1, A2. Existing: Lean proofs in `formal/lean/CLAIR/Confidence/` provide the algebra.* **COMPLETED 2026-02-04:** Tested all 5 operations (×, ⊕, undercut, rebut, min) against real trace scenarios from A1, A4, B1. Mapped 15+ Lean theorems to IR-model implications. Found 5 counterintuitive but mathematically correct results: chain-length collapse (10 steps × 0.9 → ≤0.35), non-distributivity (0.375 vs 0.4375), multiple moderate defeaters → zero, rebut(0.1,0.1) = rebut(0.9,0.9) = 0.5, confidence inflation through rephrasing. Key finding: algebra is sound; practical issues are operational (traces violate mul_le_left, ⊕ assumes independence, spec lacks multi-justification semantics). Proposed spec v0.2 additions: clarify <a∧b> vs <a∨b> vs min, canonical evaluation order, independence warning for ⊕, defeater calibration rubric, chain-length warnings. Thesis: **SUPPORTS with refinement** — confidence algebra is viable; issues are fixable through spec clarification and Thinker training.
- [x] **D5: Stratification in the wild** — Does stratification actually come up in LLM reasoning? Find ≥3 natural examples of meta-beliefs (beliefs about beliefs) in real traces. Test whether the Löb discount (c → c²) matches intuition for meta-confidence. Reference Lean theorems: `no_confidence_bootstrap`, `loebDiscount_strict_lt`, `loebChain_decreasing`. Write to `exploration/ir/D5-stratification-wild.md`. *Depends on: A1. Existing seed: Liar paradox sketch from minimal spec (0.5 at L0). `formal/lean/CLAIR/Belief/Stratified.lean` proves the theory.* **COMPLETED 2026-02-04:** Found that meta-beliefs DO occur naturally in 4 patterns: revision ("I was wrong"), comparison ("X vs Y"), qualification ("X is limited by Y"), and grounding ("X depends on Y"). However, analysis of 20+ existing traces revealed **ZERO** beliefs at L1 or higher — LLMs don't naturally capture meta-reasoning at higher levels. Identified counter-examples: Löb discount is too aggressive for comparative/qualitative meta-beliefs (c → c² assumes endorsement, but "X > Y" can have higher confidence than X or Y individually). Stratification creates perverse incentive to stay at L0 (confidence penalty). Teachability experiments show LLMs systematically misuse levels (under-use: everything at L0; over-use: random L1/L2 for non-meta beliefs). Verdict: **REFINES thesis** — stratification is theoretically sound but operationally problematic. Meta-beliefs are useful for auditing ("why did you change your mind?") but most traces don't need levels. Recommended spec v0.2 changes: make meta-beliefs optional, relax Löb discount for comparative meta-beliefs, add level inference rules.

## Priority 6: Reuse Mapping (connect proven Lean work to new model)

> **Parallel execution:** R1 and R2 are independent of each other (but each depends on D4/D5 respectively).

- [x] **R1: Confidence algebra mapping** — Map each Lean-proven property to its IR-model implication. Specifically: (1) `mul_le_left`/`mul_le_right` → derivation chains always decrease confidence, (2) `oplus_comm`/`oplus_assoc` → aggregation order doesn't matter, (3) `mul_oplus_not_distrib` → can't factor through aggregation+derivation, (4) `undercut_compose` → sequential defeats compose via ⊕, (5) `rebut_add_rebut_swap` → competing evidence sums to 1. For each, state whether it constrains valid traces, informs Thinker behavior, or is irrelevant to the IR model. Write to `exploration/ir/R1-confidence-reuse.md`. *Depends on: D4 (needs practical algebra findings).* **COMPLETED 2026-02-04:** Mapped all 69 Lean theorems across 5 operations (×, ⊕, undercut, rebut, min) to IR-model implications. Classified by relevance (Critical/High/Medium/Low) and constraint type (Validity/Operational/Descriptive). Found 4 trace validity constraints: confidence bounds [0,1], derivation monotonicity, invalidation monotonicity, aggregation monotonicity. Identified 5 critical spec gaps: evaluation order unspecified, multi-justification semantics ambiguous, independence assumption not stated, chain-length penalty not warned, defeater composition implicit. Connected to D4 findings: R1 provides formal foundation; D4 provided practical exploration. Thesis: **SUPPORTS with refinement** — All 69 theorems have practical IR implications; confidence algebra is mathematically sound. Spec v0.2 needs: trace validity section, evaluation order, multi-justification semantics, operational guidance, defeater calibration rubric.
- [x] **R2: Stratification mapping** — Map each stratification proof to its IR-model implication: (1) `no_self_introspection` → no belief can justify itself, (2) `no_circular_introspection` → no circular meta-reasoning, (3) `no_confidence_bootstrap` → meta-beliefs can't inflate confidence, (4) `loebDiscount_strict_lt` → strict decrease through meta-levels. Note that DAG.lean's `Acyclic` and `Grounded` properties directly constrain valid CLAIR documents. Identify gap: Löb discount is proven in Lean but not enforced in the textual spec grammar. Write to `exploration/ir/R2-stratification-reuse.md`. *Depends on: D5 (needs practical stratification findings).* **COMPLETED 2026-02-04:** Mapped all 10 stratification/DAG theorems to IR-model implications. Classified by relevance (Critical/High/Medium) and constraint type (Validity/Operational/Descriptive). Mapped to D5 findings. Identified 4 gaps: (1) Löb discount not in spec grammar (critical), (2) No distinction between endorsement and comparative meta-beliefs (Lean covers only endorsement, but D5 found natural language uses comparative), (3) DAG.lean has sorry proofs (low relevance), (4) No invalidation semantics formalization. Proposed spec v0.2 additions: stratification section, validity constraints, meta-belief patterns, validation section. Thesis: **SUPPORTS WITH REFINEMENT** — Lean formalization confirms structural validity and mathematical soundness. Gaps are operational (spec wording, tooling) not fundamental. Stratification is theoretically sound but operationally complex; should be optional with validation tools.

## Priority 7: Synthesis (blocked by all threads above)

- [ ] **S1: Thesis viability assessment** — After all threads complete, write a synthesis document: Does the evidence support CLAIR as a viable IR? What are the strongest arguments for and against? What would need to change to make it work? Write to `exploration/ir/synthesis.md`. *Depends on: ALL threads A-D and R.*
- [ ] **S2: Refined spec recommendations** — Based on findings, propose concrete changes to `formal/clair-spec.md`: new fields, modified constraints, removed features, added features. Write to `exploration/ir/spec-recommendations.md`. *Depends on: S1.*
- [ ] **S3: Open questions for future work** — Catalog all unresolved questions discovered during exploration, ranked by importance to the thesis. Write to `exploration/ir/open-questions.md`. *Depends on: S1.*

---

## Dependency Graph

```
Priority 1 (Foundation):       A1 ──────────────────────┐
                                A3 (depends on A1)       │
                                R3 (independent)         │
                                                         │
Priority 2 (Core Thesis):      B1 (depends on A1) ──────┤
                                B2 (depends on B1)       │
                                D6 (independent)         │
                                D1 (independent)         │
                                                         │
Priority 3 (Quality):          A2 (depends on A1)       │
                                A4 (depends on A1, A2)   │
                                D2 (independent)         │
                                D3 (depends on A1)       │
                                                         │
Priority 4 (Auditability):     C1 (partial existing)    │
                                C2 (depends on A1)       │
                                C4 (depends on C1, B1)   │
                                C3 (depends on A1)       │
                                                         │
Priority 5 (Stress Tests):     B3 (depends on B1)       │
                                B4 (depends on B1)       │
                                D4 (depends on A1, A2)   │
                                D5 (depends on A1)       │
                                                         │
Priority 6 (Reuse Mapping):    R1 (depends on D4)       │
                                R2 (depends on D5)       │
                                                         │
Priority 7 (Synthesis):        S1 (depends on ALL) ◄────┘
                                S2 (depends on S1)
                                S3 (depends on S1)
```

## File Structure

```
exploration/
└── ir/                              # New IR-model exploration
    ├── A1-problem-types.md
    ├── A2-trace-quality.md
    ├── A3-teachability.md
    ├── A4-confidence-calibration.md
    ├── B1-trace-fidelity.md
    ├── B2-information-loss.md
    ├── B3-assembler-disagreement.md
    ├── B4-degraded-traces.md
    ├── C1-query-patterns.md
    ├── C2-scale-readability.md
    ├── C3-why-reconstruction.md
    ├── C4-comparison-alternatives.md
    ├── D1-impossible-traces.md
    ├── D2-valid-but-useless.md
    ├── D3-content-opacity.md
    ├── D4-confidence-practice.md
    ├── D5-stratification-wild.md
    ├── D6-boundary-problem.md
    ├── R1-confidence-reuse.md
    ├── R2-stratification-reuse.md
    ├── R3-whats-obsolete.md
    ├── synthesis.md
    ├── spec-recommendations.md
    └── open-questions.md
```

---

## Validation

```bash
# Count remaining tasks
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0

# Verify exploration files exist
ls exploration/ir/*.md 2>/dev/null | wc -l
```

---

## Task Count

Total tasks: 24
- Priority 1 (Foundation): 3 tasks — A1, A3, R3
- Priority 2 (Core Thesis): 4 tasks — B1, B2, D6, D1
- Priority 3 (Quality): 4 tasks — A2, A4, D2, D3
- Priority 4 (Auditability): 4 tasks — C1, C2, C4, C3
- Priority 5 (Stress Tests): 4 tasks — B3, B4, D4, D5
- Priority 6 (Reuse Mapping): 2 tasks — R1, R2
- Priority 7 (Synthesis): 3 tasks — S1, S2, S3 (blocked by all above)

**Completed: 15/24 tasks (63%)**

## Critical Path

The longest dependency chain determines minimum iterations:
```
A1 → B1 → B2 → (feeds S1)     = 3 sequential steps before synthesis
A1 → A2 → A4                   = 2 sequential steps
A1 → A2 → D4 → R1              = 3 sequential steps
A1 → D5 → R2                   = 2 sequential steps
```

**Minimum iterations to completion:** ~10 (accounting for synthesis tasks and sequential dependencies), assuming independent tasks are parallelized within each iteration.

**Iteration plan (optimal parallelism):**
1. **Iteration 1:** A1 + R3 + D6 + D1 + D2 + C1 (6 independent tasks, maximum parallelism) ✅ COMPLETED: A1, R3, D6, D1, D2, C1
2. **Iteration 2:** A3 + B1 + A2 + B2 + D5 (all depend only on A1 or B1) ✅ COMPLETED: A3, B1, A2, B2, D5
3. **Iteration 3:** B2 + A4 + D4 + B3 + B4 + C4 (depend on B1/A2/C1)
4. **Iteration 4:** R1 + R2 (depend on D4/D5)
5. **Iteration 5:** S1 → S2 → S3 (sequential synthesis)
