# Plan: CLAIR IR Viability Exploration — Updated Implementation Plan

## What was done

Thorough analysis of all project files to validate and refine `IMPLEMENTATION_PLAN.md`.

## Phase 0: Orient — Findings

### Files analyzed (parallel):
- **specs/**: 3 files — `clair-ir-exploration.md` (active), `clair-exploration.md` (archived/old model), `thesis-remediation.md` (archived)
- **notes/**: 4 files — `exploration-2026-01-29-minimal-spec.md` (foundational), `reassessment-2026-01-29.md`, `design-rationale.md`, `prior-art.md`
- **formal/**: `clair-spec.md` (canonical spec v0.1)
- **formal/lean/**: 12 Lean files across Confidence (5), Belief (2 — Stratified + DAG), Syntax (4), Typing (2)
- **examples/**: `pi-calculation.md` (one complete E2E example), `hello-world-simple.clair` (obsolete)
- **exploration/completed/**: 58 threads (ALL old programming language model)
- **exploration/ir/**: Empty — no IR exploration started

### Lean proof status:
- **REUSABLE**: Confidence algebra (40+ theorems fully proven), Stratification + Löb discount (anti-bootstrapping, no self/circular introspection)
- **OBSOLETE**: Syntax (Types, Expr, Context, Subst), Typing (HasType, Subtype)
- **PARTIAL**: DAG.lean (`sorry` gaps in acyclicity/groundedness proofs)

## Phase 1: Gap Analysis

The existing plan's gap analysis is **accurate**. Key confirmation:
- `exploration/ir/` is genuinely empty — 0 files, 0 exploration started
- All 24 tasks correctly unchecked
- The 7 stress-test sketches in minimal-spec exploration are seeds only (2-5 beliefs each), not full explorations
- pi-calculation is the ONLY complete end-to-end example

### Refinements made to plan:
1. Added `notes/design-rationale.md` as resource for D6 (boundary problem)
2. Added `notes/prior-art.md` detail (Subjective Logic, TMS, Justification Logic) for C4
3. Expanded R3 scope to explicitly include 58 old-model threads + active threads 8.4/3.15
4. Noted DAG.lean `sorry` gaps in gap analysis
5. Added concrete 5-iteration execution plan for optimal parallelism

## Phase 2: Plan Updates

Updated `IMPLEMENTATION_PLAN.md` with:
- Enriched gap analysis with newly discovered resources
- More specific file references in task descriptions
- Concrete iteration plan (5 iterations with parallel groupings)
- All 24 tasks in `- [ ]` checkbox format (verified with grep)

## Validation
- `grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md` → 24 (correct)
- `grep -c "^\- \[x\]" IMPLEMENTATION_PLAN.md` → 0 (correct)
- No code was written (planning mode only)
