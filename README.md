# CLAIR: Comprehensible LLM AI Intermediate Representation

> An intermediate representation for reasoning traces—a DAG of beliefs that captures *what* an LLM concluded, *why*, and *when to reconsider*.

## What Is CLAIR?

CLAIR is a **data format** for reasoning traces, not a programming language.

```clair
b1 1.0 L0 @user "calculate PI to N decimal places"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b4 .85 L0 @self <b3 "Chudnovsky algorithm converges fastest"
b5 .85 L0 @self <b4 ?["n<15"] "use Chudnovsky"
```

Each belief carries:
- **Confidence** — calibrated reliability in [0,1]
- **Level** — stratification for safe self-reference
- **Source** — where it came from (@user, @self, @file, etc.)
- **Justifications** — backward edges to supporting beliefs
- **Invalidations** — conditions that would defeat this belief
- **Content** — the proposition (opaque natural language)

## The Thinker+Assembler Architecture

```
┌─────────────────────┐
│   User Request      │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│   Thinker LLM       │  ← Reasons about the problem
│   (e.g., Opus)      │     Produces CLAIR trace
└──────────┬──────────┘
           │ CLAIR trace (DAG of beliefs)
           ▼
┌─────────────────────┐
│   Assembler LLM     │  ← Interprets CLAIR trace
│   (e.g., Haiku)     │     Produces executable code
└──────────┬──────────┘
           │ Code (Python, JS, etc.)
           ▼
┌─────────────────────┐
│   Runtime           │  ← Executes
└─────────────────────┘
```

**Both LLMs understand CLAIR.** The Thinker produces structured reasoning; the Assembler interprets it. Humans can audit the trace.

## Key Design Decisions

### Beliefs Don't Compose

CLAIR is not a programming language. There's no monadic bind, no function composition. Beliefs are **nodes in a DAG**, not composable computations.

The Thinker LLM produces traces with whatever structure the reasoning requires.

### Confidence Algebra Still Applies

When beliefs justify other beliefs, confidence propagates:

| Operation | Formula | Use Case |
|-----------|---------|----------|
| Sequential | `c₁ × c₂` | Derivation chains |
| Conservative | `min(c₁, c₂)` | Weakest link |
| Independent | `c₁ ⊕ c₂ = 1-(1-c₁)(1-c₂)` | Multiple sources |

These are **constraints on valid traces**, not operations the format provides.

### Stratification Prevents Bootstrapping

Beliefs have levels (L0, L1, L2...). A belief *about* another belief must be at a higher level. The **Löb discount** (`c → c²`) ensures confidence decreases through meta-levels:

```clair
b1 .9 L0 @self "X is true"
b2 .81 L1 @self <b1 "I believe b1"      ; .9² = .81
b3 .65 L2 @self <b2 "I believe b2"      ; .81² ≈ .65
```

No finite chain of self-reference can bootstrap confidence.

### Tracking, Not Proving

CLAIR doesn't prove beliefs are true. It **tracks** what is believed, with what confidence, for what reasons. This is a principled response to Gödel's incompleteness—no system can prove its own soundness.

## Project Structure

```
formal/
  clair-spec.md              # Minimal IR specification
  theoretical-foundations.md # Reading guide to foundational work
  logical-foundations.md     # Connections to epistemic logic, etc.
  dissertation/              # The CLAIR Book (PDF)
    clair-book.pdf           # Full specification book
    chapters/                # Book chapters
    appendices/              # Appendices
  lean/CLAIR/               # Lean 4 formalization
    Confidence/             # Confidence algebra proofs
    Belief/                 # DAG structure, stratification

examples/
  pi-calculation.md         # Thinker+Assembler walkthrough

notes/
  reassessment-2026-01-29.md    # Paradigm shift analysis
  exploration-2026-01-29-*.md   # Design exploration

archive/                    # Old programming language model (obsolete)
```

## Formal Verification (Lean 4)

Core properties are machine-checked:

| Property | Status |
|----------|--------|
| Confidence bounds [0,1] | ✓ Proven |
| ⊕ commutative, associative, identity | ✓ Proven |
| Non-distributivity of (⊕, ×) | ✓ Proven (counterexample) |
| Undercut reduces confidence | ✓ Proven |
| Löb discount ≤ original | ✓ Proven |
| Anti-bootstrapping | ✓ Proven |
| Acyclic → well-founded | Stated (infrastructure needed) |

## Theoretical Foundations

CLAIR synthesizes ideas from:

- **Provability Logic (GL)** — Löb's theorem, safe self-reference
- **Subjective Logic** — Confidence algebra (but not three-component opinions)
- **Defeasible Reasoning** — Undercut and rebut semantics (Pollock)
- **ATMS** — DAG structure, dependency tracking (de Kleer)
- **AGM Belief Revision** — Revision on edges, Recovery correctly fails
- **Epistemic Modal Logic** — Graded belief operators

See `formal/theoretical-foundations.md` for a full reading guide.

## Status

**Theoretical framework: complete.** The [CLAIR Book](formal/dissertation/clair-book.pdf) documents the full specification.

**Implementation: not started.** To make this work in practice:
1. CLAIR parser + validator
2. System prompts for Thinker/Assembler
3. Example traces for few-shot learning
4. (Optional) Fine-tuning for reliable output

## What CLAIR Is Not

- **Not a programming language** — It's a data format for reasoning traces
- **Not executable** — The Assembler produces executable code
- **Not typed** — Content is opaque natural language interpreted by LLMs
- **Not compositional** — Beliefs form a DAG, not composable computations

## Origins

Developed through exploration of: *"What would an AI-native intermediate representation look like that preserves reasoning for audit?"*

Key insight: The fundamental unit isn't the value—it's the **belief**. A belief is content plus epistemic metadata (confidence, provenance, justification, invalidation). Traditional IRs discard reasoning; CLAIR preserves it.
