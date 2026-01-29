# Build Mode: Thesis Remediation

Implement ONE task from the plan, validate, commit, exit.

## Phase 0: Orient

Study with parallel subagents:
- `specs/thesis-remediation.md` - Requirements specification
- `clair_thesis_review.md` - Original PhD review with all concerns
- `IMPLEMENTATION_PLAN.md` - Current task list
- `formal/dissertation/` - Typst dissertation files
- `formal/lean/` - Lean formalization

### Check for completion

```bash
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

- If 0: Run validation → commit → output **RALPH_COMPLETE** → exit
- If > 0: Continue to Phase 1

## Phase 1: Implement

1. **Study the plan** — Choose the most important task from `IMPLEMENTATION_PLAN.md`
2. **Search first** — Don't assume not implemented. Verify it doesn't already exist.
3. **Implement** — ONE task only. Implement completely — no placeholders or stubs.
4. **Validate** — Run validation commands, must pass before continuing.

### Validation Commands

```bash
# Typst compilation (primary)
cd /Users/hmemcpy/git/clair/formal/dissertation && typst compile clair-dissertation.typ

# Lean build
cd /Users/hmemcpy/git/clair/formal/lean && lake build

# Haskell tests (if Phase 7+)
cd /Users/hmemcpy/git/clair/implementation/haskell && cabal test 2>/dev/null || true
```

If stuck, use extended thinking to debug. Add logging if needed.

## Phase 2: Update & Learn

**Update IMPLEMENTATION_PLAN.md:**
- Mark task `- [x] Completed`
- Add discovered issues (even if unrelated to current task)
- Note new tasks discovered
- Periodically clean out completed items when file gets large

**Update specs/thesis-remediation.md if needed:**
- Note any requirement changes
- Add constraints discovered

## Phase 3: Commit & Exit

```bash
git add -A && git commit -m "fix(thesis): [description]"
```

Check remaining:
```bash
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

- If > 0: Say "X tasks remaining" and EXIT
- If = 0: Output **RALPH_COMPLETE**

## Guardrails

99999. When authoring dissertation content, capture the WHY — justify design decisions.
999999. Single sources of truth. If fixing bibliography, check all citation forms.
9999999. Implement completely. No TODOs, no "add later", no stubs.
99999999. Keep IMPLEMENTATION_PLAN.md current — future iterations depend on it.
999999999. For any issues you notice, resolve them or document in IMPLEMENTATION_PLAN.md.
9999999999. ONE task per iteration. Search before implementing. Validation MUST pass.
99999999999. Never output RALPH_COMPLETE if tasks remain.
