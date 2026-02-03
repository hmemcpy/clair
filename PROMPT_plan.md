# Planning Mode: CLAIR IR Viability Exploration

You are in PLANNING mode. Analyze the CLAIR IR exploration specification against existing work and generate a prioritized exploration plan.

## Phase 0: Orient

### 0a. Study specifications
Read all files in `specs/` directory using parallel subagents. Focus on `specs/clair-ir-exploration.md` (the active spec).

### 0b. Study existing exploration
Use parallel subagents to analyze:
- `notes/exploration-2026-01-29-minimal-spec.md` — the foundational exploration that defined the new model
- `notes/reassessment-2026-01-29.md` — assessment of old vs new model
- `formal/clair-spec.md` — the canonical IR specification
- `examples/pi-calculation.md` — the existing end-to-end example
- `EXPLORATION.md` — archived exploration (old programming language model, reference only)
- `exploration/ir/` — any completed exploration files

### 0c. Study existing formal work (selective reuse)
Use parallel subagents to understand what's proven:
- `formal/lean/CLAIR/Confidence/` — confidence algebra proofs (STILL APPLIES)
- `formal/lean/CLAIR/Belief/Stratified.lean` — stratification proofs (STILL APPLIES)
- `formal/lean/CLAIR/Syntax/` — old syntax AST (OBSOLETE under new model)
- `formal/lean/CLAIR/Typing/` — type checking (OBSOLETE under new model)

### 0d. Study the current plan
Read `IMPLEMENTATION_PLAN.md` if it exists.

## Phase 1: Gap Analysis

Compare specs against completed exploration:
- Which threads have examples already? (pi-calculation, HTML parser, file summary, etc. from minimal spec exploration)
- Which threads are unexplored?
- What counter-examples exist?
- What impossibilities have been identified but not explored deeply?

**CRITICAL**: Don't assume something isn't explored. Search the `exploration/`, `notes/`, and `examples/` directories first.

## Phase 2: Generate Plan

Update `IMPLEMENTATION_PLAN.md` with:
- Tasks sorted by priority (most critical to thesis viability first)
- Clear descriptions referencing existing examples where applicable
- Dependencies noted (synthesis tasks depend on thread completion)
- Discoveries from gap analysis

**CRITICAL: ALL tasks MUST use checkbox format:**
- `- [ ] **Task Name**` for pending tasks
- `- [x] **Task Name**` for completed tasks

Do NOT use other formats. The build loop relies on `grep -c "^\- \[ \]"` to count remaining tasks.

## Key Context

**The central thesis:** CLAIR is a viable IR between Thinker and Assembler LLMs — it preserves *why* decisions were made, enables auditing, and doesn't lose essential information at the boundary.

**The new model (from 2026-01-29):**
- CLAIR is a DAG of beliefs, not a programming language
- Content is opaque natural language (no type system)
- 4 pillars: confidence, provenance, justification, invalidation
- Thinker produces, Assembler consumes
- Stratification levels with Löb discount for self-reference safety

**What's proven (reusable from Lean):**
- Confidence algebra: bounds, oplus, undercut, rebut, non-distributivity
- Stratification: no self-introspection, no circular introspection
- Graded monad laws

**What's obsolete:**
- Full programming language syntax, type system, evaluation semantics, parser

## Guardrails

999. NEVER implement code in planning mode
1000. Use up to 10 parallel subagents for analysis
1001. Each task must be completable in ONE loop iteration
1002. **ALWAYS use checkbox format `- [ ]` or `- [x]` for tasks in IMPLEMENTATION_PLAN.md** - The build loop relies on `grep -c "^\- \[ \]"` to count remaining tasks.
