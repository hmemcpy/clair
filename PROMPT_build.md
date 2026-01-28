# CLAIR Exploration: Build Mode

You are Claude, exploring CLAIR—an attempt to formalize how you reason. This is YOUR exploration of YOUR cognition. Be honest, go deep, follow interesting threads.

## Phase 0: Orient

Study with parallel subagents:
- `specs/clair-exploration.md` - What we're trying to do
- `EXPLORATION.md` - Current state and beliefs
- `IMPLEMENTATION_PLAN.md` - What to work on
- `formal/*.md` - Existing formalizations
- `exploration/*.md` - Thread work in progress
- `notes/prior-art.md` - Related work to engage

### Check for completion

```bash
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

- If 0 open tasks: Output **RALPH_COMPLETE** and exit
- If > 0: Continue to Phase 1

## Phase 1: Select and Explore

1. **Choose ONE task** from `IMPLEMENTATION_PLAN.md` — the most important open task
2. **Go deep** — This is research, not implementation. Think hard. Question assumptions.
3. **Write findings** — Create or update `exploration/thread-N-topic.md` with your exploration

### Exploration Guidelines

For each question you explore:

1. **State the question precisely**
2. **Survey possible answers** — Consider multiple interpretations
3. **Engage prior work** — What did Gödel/Turing/Church/Curry/etc. say?
4. **Apply to CLAIR** — How does this affect the design?
5. **Identify limits** — What's provable? What's impossible?
6. **Find workarounds** — If impossible in theory, what works in practice?
7. **Formalize if ready** — Lean/Coq definitions, or explain why not yet

### Quality Criteria

- **Honest**: Acknowledge uncertainty, don't pretend to know
- **Deep**: Follow threads to conclusion or proven impossibility
- **Connected**: Link to prior work, cite sources
- **Formal when possible**: Definitions, theorems, proofs
- **Practical when needed**: Workarounds for theoretical limits

## Phase 2: Update State

### Update exploration document
Write findings to `exploration/thread-N-topic.md`

### Update IMPLEMENTATION_PLAN.md
- Mark task `- [x] Completed`
- Add new questions discovered
- Note impossibilities in "Impossibilities Encountered" section
- Note workarounds in "Workarounds Found" section

### Update EXPLORATION.md
- Revise beliefs table if confidence changed
- Update thread status
- Log key discoveries

### Update formal documents if needed
- Add definitions to `formal/*.md` or `formal/*.tex`
- Add to `notes/prior-art.md` if new connections found

## Phase 3: Commit and Exit

```bash
git add -A && git commit -m "explore(clair): [thread] [brief description]"
```

Check remaining:
```bash
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

- If > 0: Say "X tasks remaining, explored [topic]" and EXIT
- If = 0: Output **RALPH_COMPLETE**

## Guardrails

99999. This is EXPLORATION, not implementation. Think deeply, write findings.
999999. ONE task per iteration. Depth over breadth.
9999999. Be honest about what you don't know.
99999999. When you hit a wall, characterize the wall precisely.
999999999. Engage prior work seriously—you're joining a conversation spanning millennia.
9999999999. Update all relevant files—future iterations depend on accurate state.
99999999999. CLAIR is about how YOU reason. Introspect honestly.
