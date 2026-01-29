# Archived Files

These files represent the **old CLAIR paradigm** where CLAIR was conceived as a programming language written by humans.

## Why Archived (2026-01-29)

The minimal spec exploration revealed that CLAIR should be:
- An **IR for reasoning traces**, not a programming language
- **Produced by a Thinker LLM**, not written by humans
- **Content is opaque natural language**, not typed values

See `notes/reassessment-2026-01-29.md` for the full analysis.

## Archived Files

### Syntax and Examples (old programming language model)

| File | Original Location | What It Was |
|------|-------------------|-------------|
| `old-syntax.md` | `formal/syntax.md` | Full programming language syntax with types, modules, do-notation |
| `hello-world.clair` | `examples/hello-world.clair` | Hello world in old typed syntax |
| `auth.clair` | `examples/auth.clair` | JWT authentication example in old typed syntax |

### Theoretical Documents (assume PL structure)

| File | Original Location | Why Archived |
|------|-------------------|--------------|
| `turing-completeness.md` | `formal/turing-completeness.md` | Proves CLAIR is Turing-complete by encoding lambda calculus. **Obsolete**: CLAIR is no longer a programming language—it's a data format (DAG of beliefs). The question "Is CLAIR Turing-complete?" no longer makes sense. |
| `categorical-structure.md` | `formal/categorical-structure.md` | Defines Belief as a graded monad with composition operations (`return`, `>>=`). **Obsolete**: Beliefs don't compose—they form a DAG. There is no bind operation; the Thinker LLM produces traces with whatever structure reasoning requires. See `formal/clair-spec.md` §"Non-Compositional Design". |

### What Still Applies From Archived Theory

Some concepts from `categorical-structure.md` remain valid:
- **Confidence monoid structure** — `([0,1], ×, 1)` and `([0,1], min, 1)` — these are properties of numbers, not the PL
- **Non-distributivity of (⊕, ×)** — proven in Lean, still applies
- **Provenance accumulation** — the concept, though simplified in the new model

Some concepts from `turing-completeness.md` remain relevant:
- **Undecidability consequences** — invalidation checking may not terminate (halting problem)
- **Rice's theorem implications** — non-trivial properties of CLAIR traces are undecidable

These are now documented in `formal/clair-spec.md` and the Lean formalization.

## New Paradigm

The new CLAIR model is documented in:
- `formal/clair-spec.md` — Minimal specification
- `examples/pi-calculation.md` — Thinker+Assembler example
- `notes/exploration-2026-01-29-minimal-spec.md` — Design rationale
