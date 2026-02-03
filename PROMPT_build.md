# Build Mode: CLAIR IR Viability Exploration

Explore ONE task from the plan, write findings, commit, exit.

## Phase 0: Orient

Study with parallel subagents:
- `specs/clair-ir-exploration.md` - Active specification
- `formal/clair-spec.md` - The canonical CLAIR IR spec
- `notes/exploration-2026-01-29-minimal-spec.md` - Foundational exploration
- `notes/reassessment-2026-01-29.md` - Old vs new model assessment
- `examples/pi-calculation.md` - Existing end-to-end example
- `IMPLEMENTATION_PLAN.md` - Current task list
- `exploration/ir/` - Any completed exploration files

### Check for completion

```bash
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

- If 0: Commit → output **RALPH_COMPLETE** → exit
- If > 0: Continue to Phase 1

## Phase 1: Explore

1. **Study the plan** — Choose the most important uncompleted task from `IMPLEMENTATION_PLAN.md`
2. **Search first** — Check if findings already exist in `exploration/ir/`, `notes/`, or `examples/`
3. **Explore** — ONE task only. Explore completely — no placeholders or stubs.
4. **Write findings** — Document in the appropriate `exploration/ir/*.md` file

### Exploration Methodology

For each task, the output should include:

**Examples** (at least 3 per thread task):
- Concrete CLAIR traces showing the phenomenon
- Step-by-step analysis of what works and what doesn't
- Connection to the central thesis

**Counter-examples** (at least 1 per thread task):
- Cases where the model breaks or is insufficient
- Precise characterization of why it fails
- Whether the failure is fundamental or fixable

**Key findings:**
- Clear statement of what was learned
- How it supports, undermines, or refines the thesis
- Open questions for future work

### Key Context

**The central thesis:** CLAIR is a viable IR between Thinker and Assembler LLMs — it preserves *why* decisions were made, enables auditing, and doesn't lose essential information at the boundary.

**The CLAIR spec** (`formal/clair-spec.md`):
```
belief := id confidence level source justifications? invalidations? content
```
- 4 pillars: confidence, provenance, justification, invalidation
- Content is opaque natural language
- DAG structure (acyclic)
- Stratification levels with Löb discount (c → c²)
- 0.5 = maximal uncertainty, absence = no belief

**Existing examples to build on:**
- Pi calculation (algorithm selection)
- HTML parser (system design)
- File summary (external content)
- Conditional (purple sky)
- Self-reference (stratification)
- Liar paradox
- Unknown (alien colors)

**Proven results (reusable):**
- Confidence ∈ [0,1] preserved under all operations (Lean)
- Non-distributivity of × and ⊕ (Lean, counterexample a=b=c=0.5)
- Stratification prevents self-reference paradox (Lean)
- Löb discount g(c)=c² prevents bootstrapping (Lean)

If stuck, use extended thinking to reason through the problem.

## Phase 2: Update & Learn

**Update IMPLEMENTATION_PLAN.md:**
- Mark task `- [x] Completed`
- Add discovered issues or new questions
- Note new tasks discovered during exploration
- Periodically clean out completed items when file gets large

## Phase 3: Commit & Exit

```bash
git add -A && git commit -m "explore(clair-ir): [description]"
```

Check remaining:
```bash
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

- If > 0: Say "X tasks remaining" and EXIT
- If = 0: Output **RALPH_COMPLETE**

## Guardrails

99999. Focus on practicality — examples and counter-examples over formal proofs.
999999. Each exploration document should be self-contained and readable.
9999999. Explore completely. No "TODO: explore this later" stubs.
99999999. Keep IMPLEMENTATION_PLAN.md current — future iterations depend on it.
999999999. For any issues you notice, document in IMPLEMENTATION_PLAN.md.
9999999999. ONE task per iteration. Search before exploring. Never output RALPH_COMPLETE if tasks remain.
99999999999. Connect every finding to the central thesis: does it support, undermine, or refine it?
