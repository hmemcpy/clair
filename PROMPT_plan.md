# Planning Mode: Thesis Remediation

You are in PLANNING mode. Analyze the thesis remediation specification against existing dissertation content and generate a prioritized implementation plan.

## Phase 0: Orient

### 0a. Study specifications
Read all files in `specs/` directory using parallel subagents, especially `thesis-remediation.md`.

Also read the original PhD review:
- `clair_thesis_review.md` - Full review with 6 major concerns, 7 holes, 30 missing citations

### 0b. Study existing implementation
Use parallel subagents to analyze:
- `formal/dissertation/chapters/` - All 13 chapter .typ files
- `formal/dissertation/appendices/` - All 4 appendix .typ files
- `formal/dissertation/references.bib` - Current bibliography
- `formal/lean/CLAIR/` - Lean formalization
- `examples/` - CLAIR example programs

### 0c. Study the current plan
Read `IMPLEMENTATION_PLAN.md` if it exists.

## Phase 1: Gap Analysis

Compare specs against implementation:

### Bibliography
- Which of the 30 citations are truly missing vs. key mismatches?
- Are any already present under different keys?

### Semantic Foundations
- Does Chapter 3 have a "Semantic Commitments" section?
- Are there "0.5 = ignorance" claims to remove?

### Language Specification
- Does a formal grammar exist anywhere?
- Are typing rules complete in the Lean code?
- Is there an operational semantics specification?

### Verification
- Does `lake build` succeed?
- What theorems are truly machine-checked vs. sketched?

### Evaluation
- Does any evaluation chapter exist?
- Are there any empirical results?

**CRITICAL**: Don't assume something isn't implemented. Search the codebase first.

## Phase 2: Generate Plan

Update `IMPLEMENTATION_PLAN.md` with:
- Tasks sorted by priority (blocking issues first)
- Clear descriptions with file locations
- Dependencies noted where relevant
- Discoveries from gap analysis

**CRITICAL: ALL tasks MUST use checkbox format:**
- `- [ ] **Task Name**` for pending tasks
- `- [x] **Task Name**` for completed tasks

Do NOT use other formats like `#### P1.1: Task Name`. The build loop relies on `grep -c "^\- \[ \]"` to count remaining tasks.

Capture the WHY, not just the WHAT.

## Guardrails

999. NEVER implement code in planning mode
1000. Use up to 10 parallel subagents for analysis
1001. Each task must be completable in ONE loop iteration
1002. **ALWAYS use checkbox format `- [ ]` or `- [x]` for tasks in IMPLEMENTATION_PLAN.md**
