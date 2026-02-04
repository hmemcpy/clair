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

**What's missing (21/24 tasks unchecked):**
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
- [ ] **A3: Teachability experiment** — Can a Thinker LLM be taught the CLAIR spec through a system prompt and produce valid traces? Test with the spec from `formal/clair-spec.md`. Document what works, what the LLM gets wrong, and whether few-shot examples help. Write to `exploration/ir/A3-teachability.md`. *Depends on: A1 (uses traces produced there as few-shot examples). Existing: pi-calculation was hand-authored, not LLM-produced.*
- [x] **R3: What's obsolete** — Explicitly list what from the old formalization does NOT apply: type system (`formal/lean/CLAIR/Syntax/` — 4 files: Types, Expr, Context, Subst), typing rules (`formal/lean/CLAIR/Typing/` — HasType, Subtype), old syntax examples (`examples/hello-world-simple.clair`), evaluation semantics, parser, and the 58 completed exploration threads under the old programming language model (including active threads 8.4 and 3.15). For each, explain why it's irrelevant under the new model (opaque NL content, no type checking, no evaluation). Write to `exploration/ir/R3-whats-obsolete.md`. *No dependencies. Existing: `notes/reassessment-2026-01-29.md` provides initial component-by-component assessment.* **COMPLETED 2026-02-04:** Comprehensive catalog of obsolete components. Found ~70% of old formalization is obsolete: type system (Types.lean, HasType.lean, Subtype.lean), expression language (Expr.lean with lambdas, case, patterns), evaluation semantics (Step.lean, Eval.lean), parser (Parser.lean), old examples (*.clair files), 58 completed exploration threads, formal/syntax.md, formal/derivation-calculus.md (80%). Reusable: confidence algebra (100% - fully proven), stratification (80% - needs Löb discount), DAG structure (60% - needs completion), foundations/limits (100%), prior art (100%). Thesis: **SUPPORTS with refinement** — elimination of confusion highlights reusable foundations, demonstrates simplicity. Lost type safety and verification capabilities are acceptable trade-offs for LLM-to-LLM communication.

## Priority 2: Core Thesis Tests (directly test the central thesis — CLAIR preserves info across boundary)

> **Parallel execution:** D6 and D1 are independent and can start immediately (no dependencies). B1 depends on A1; B2 depends on B1.

- [ ] **B1: Trace-to-code fidelity test** — Give an Assembler LLM the pi-calculation trace and 3 new traces from A1. Compare output code quality against: (a) giving the same LLM just the user request, (b) giving chain-of-thought reasoning. Document whether CLAIR traces actually improve output. Write to `exploration/ir/B1-trace-fidelity.md`. *Depends on: A1 (needs diverse traces).*
- [ ] **B2: Information loss analysis** — Identify what information is lost at the Thinker→Assembler boundary. What does the Assembler ignore? What does it misinterpret? What is ambiguous? Create a taxonomy of information loss types (e.g., ignored invalidations, misread confidence, ambiguous NL content, missing context). Write to `exploration/ir/B2-information-loss.md`. *Depends on: B1 (analyzes fidelity test results).*
- [x] **D6: The boundary problem** — Where does "belief about computation" end and "computation itself" begin? `"iterate k from 0 to n"` is a belief about a loop — but is it precise enough? Construct a spectrum from pure description ("we need a loop") to pure prescription ("for k in range(n)") and identify where CLAIR content should sit. Write to `exploration/ir/D6-boundary-problem.md`. *No dependencies. Existing seed: minimal spec's "content is opaque NL" principle, conditionals sketch, and `notes/design-rationale.md` (documents the decision to keep content opaque).* **COMPLETED 2026-02-04:** Found that the boundary is a zone (not hard line) with optimal "sweet spot" at strategy+algorithm level. Developed 3-part test (actionability, universality, belief-level). Counter-examples identified: bit manipulation, async patterns, SQL. Thesis: **supports with operational constraints**.
- [x] **D1: The "impossible trace" collection** — Find ≥5 problems that CANNOT be represented as a DAG of beliefs: iterative refinement where beliefs change mid-reasoning, adversarial/game-theoretic reasoning, real-time adaptation, creative tasks with no clear justification chain, problems requiring backtracking. Document why each fails and whether workarounds exist. Write to `exploration/ir/D1-impossible-traces.md`. *No dependencies. Existing seeds: self-reference/paradox handling sketch, unknown/unknowability sketch from minimal spec.* **COMPLETED 2026-02-04:** Explored 6 "impossible" trace types: (1) Iterative refinement with temporal discovery, (2) Real-time adaptation (continuous learning), (3) Game-theoretic reasoning, (4) Non-monotonic reasoning with defaults, (5) Probabilistic sequential reasoning, (6) Cyclic dependencies. Key finding: **no fundamental impossibilities** — all cases have workarounds (temporal metadata, invalidation conditions, equilibrium modeling, two-trace protocol). Thesis: **supports with operational constraints** — CLAIR is viable but Thinkers need guidance on producing atemporal traces, and spec extensions (@step/@version) are needed for temporal reasoning.

## Priority 3: Quality & Calibration (assess whether the IR is meaningful, not just structurally valid)

> **Parallel execution:** D2 is independent and can start immediately. A2 depends on A1; A4 depends on A1+A2; D3 depends on A1.

- [ ] **A2: Trace quality analysis** — For each example from A1, evaluate: Are confidence values meaningful? Are justifications actually connected to conclusions? Are invalidation conditions useful? Is the DAG structure well-formed? Define explicit quality criteria (connectedness, calibration, completeness, granularity) and document common failure modes. Write to `exploration/ir/A2-trace-quality.md`. *Depends on: A1.*
- [ ] **A4: Confidence calibration challenge** — Are Thinker-assigned confidence values meaningful? Compare: same problem solved multiple times — do confidence values correlate with actual correctness? Test with ≥3 problems where ground truth is known. Document whether confidence is informative or decorative. Write to `exploration/ir/A4-confidence-calibration.md`. *Depends on: A1, A2.*
- [ ] **D2: Valid but useless traces** — Construct ≥3 traces that satisfy all spec constraints (acyclic, valid confidence, proper levels, proper justifications) but provide no useful information to an Assembler. What makes a trace useful beyond structural validity? Propose a "usefulness" criterion. Write to `exploration/ir/D2-valid-but-useless.md`. *No dependencies.*
- [ ] **D3: The content opacity problem** — Since content is opaque NL, construct examples where: (1) identical content means different things in context, (2) ambiguous content leads to wrong assembly, (3) content requires domain knowledge the Assembler lacks, (4) content is too vague to act on. Write to `exploration/ir/D3-content-opacity.md`. *Depends on: A1 (uses real traces to find ambiguities).*

## Priority 4: Auditability (the "human in the loop" value proposition)

> **Parallel execution:** C1 can start immediately (has partial existing work). C2 and C3 depend on A1; C4 depends on C1+B1.

- [ ] **C1: Query pattern catalog** — Document all query types humans might ask of a CLAIR trace: "why X?", "why not Y?", "when to reconsider?", "what assumptions?", "what alternatives were considered?", "how confident?", "what was ruled out?", "what evidence supports X?". Show how each maps to graph traversal (parent walk, sibling comparison, invalidation check, etc.). Write to `exploration/ir/C1-query-patterns.md`. *Existing: pi-calculation demonstrates 4 query types ("Why Chudnovsky?", "Why not Leibniz?", "When reconsider?", "What's needed?"). Needs systematic expansion to ≥8 patterns.*
- [ ] **C2: Scale readability test** — Create or reference traces of increasing size (5 beliefs, 20 beliefs, 100 beliefs). At what scale do traces become unreadable? What summarization or visualization would help? Compare with chain-of-thought at same scales. Write to `exploration/ir/C2-scale-readability.md`. *Depends on: A1 (uses traces of varying size).*
- [ ] **C4: Comparison with alternatives** — Compare CLAIR trace auditability against: raw chain-of-thought, structured JSON reasoning, decision trees, argument maps (Walton/Dung). What does CLAIR add that others don't? Reference `notes/prior-art.md` for existing survey (covers Subjective Logic, TMS, Justification Logic, weighted argumentation). Write to `exploration/ir/C4-comparison-alternatives.md`. *Depends on: C1, B1.*
- [ ] **C3: The "why" reconstruction test** — Given only a CLAIR trace (no original prompt), can a human reconstruct the original intent? This tests whether traces are self-contained explanations. Use pi-calculation and 2+ traces from A1. Write to `exploration/ir/C3-why-reconstruction.md`. *Depends on: A1.*

## Priority 5: Stress Tests & Algebra (push the model to breaking points)

> **Parallel execution:** B3+B4 depend on B1. D4 depends on A1+A2. D5 depends on A1.

- [ ] **B3: Assembler disagreement scenario** — Construct a trace where the Thinker's reasoning is plausible but suboptimal (e.g., Thinker chooses bubble sort at 0.7 confidence; Assembler "knows" quicksort is better). Does the Assembler follow the trace blindly, or can it improve? What SHOULD happen — should CLAIR have a protocol for Assembler pushback? Write to `exploration/ir/B3-assembler-disagreement.md`. *Depends on: B1.*
- [ ] **B4: Degraded trace test** — What happens with traces of varying quality? Systematically degrade a known-good trace: (1) remove justifications, (2) scramble confidence values, (3) omit invalidations, (4) remove some beliefs, (5) reorder beliefs. How gracefully does the Assembler degrade? Find the minimum viable trace. Write to `exploration/ir/B4-degraded-traces.md`. *Depends on: B1.*
- [ ] **D4: Confidence algebra in practice** — Test the proven algebra (×, ⊕, undercut, rebut, min) against real trace scenarios. Does `0.9 × 0.8 = 0.72` actually represent how confidence should propagate? Find cases where the algebra produces counterintuitive results. Reference specific Lean theorems: `mul_oplus_not_distrib` (non-distributivity), `undercut_compose` (sequential defeat), `rebut_eq` (equal evidence → 0.5). Write to `exploration/ir/D4-confidence-practice.md`. *Depends on: A1, A2. Existing: Lean proofs in `formal/lean/CLAIR/Confidence/` provide the algebra.*
- [ ] **D5: Stratification in the wild** — Does stratification actually come up in LLM reasoning? Find ≥3 natural examples of meta-beliefs (beliefs about beliefs) in real traces. Test whether the Löb discount (c → c²) matches intuition for meta-confidence. Reference Lean theorems: `no_confidence_bootstrap`, `loebDiscount_strict_lt`, `loebChain_decreasing`. Write to `exploration/ir/D5-stratification-wild.md`. *Depends on: A1. Existing seed: Liar paradox sketch from minimal spec (0.5 at L0). `formal/lean/CLAIR/Belief/Stratified.lean` proves the theory.*

## Priority 6: Reuse Mapping (connect proven Lean work to new model)

> **Parallel execution:** R1 and R2 are independent of each other (but each depends on D4/D5 respectively).

- [ ] **R1: Confidence algebra mapping** — Map each Lean-proven property to its IR-model implication. Specifically: (1) `mul_le_left`/`mul_le_right` → derivation chains always decrease confidence, (2) `oplus_comm`/`oplus_assoc` → aggregation order doesn't matter, (3) `mul_oplus_not_distrib` → can't factor through aggregation+derivation, (4) `undercut_compose` → sequential defeats compose via ⊕, (5) `rebut_add_rebut_swap` → competing evidence sums to 1. For each, state whether it constrains valid traces, informs Thinker behavior, or is irrelevant to the IR model. Write to `exploration/ir/R1-confidence-reuse.md`. *Depends on: D4 (needs practical algebra findings).*
- [ ] **R2: Stratification mapping** — Map each stratification proof to its IR-model implication: (1) `no_self_introspection` → no belief can justify itself, (2) `no_circular_introspection` → no circular meta-reasoning, (3) `no_confidence_bootstrap` → meta-beliefs can't inflate confidence, (4) `loebDiscount_strict_lt` → strict decrease through meta-levels. Note that DAG.lean's `Acyclic` and `Grounded` properties directly constrain valid CLAIR documents. Identify gap: Löb discount is proven in Lean but not enforced in the textual spec grammar. Write to `exploration/ir/R2-stratification-reuse.md`. *Depends on: D5 (needs practical stratification findings).*

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

**Completed: 3/24 tasks (13%)**

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
1. **Iteration 1:** A1 + R3 + D6 + D1 + D2 + C1 (6 independent tasks, maximum parallelism)
2. **Iteration 2:** A3 + B1 + A2 + D3 + C2 + C3 + D5 (all depend only on A1)
3. **Iteration 3:** B2 + A4 + D4 + B3 + B4 + C4 (depend on B1/A2/C1)
4. **Iteration 4:** R1 + R2 (depend on D4/D5)
5. **Iteration 5:** S1 → S2 → S3 (sequential synthesis)
