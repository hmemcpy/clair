# CLAIR Minimal Spec Exploration — 2026-01-29

## Context

We set out to define a practical, minimal CLAIR specification — moving away from the Lean-heavy formal spec toward something that captures LLM reasoning traces in a round-trippable format.

**Key insight:** CLAIR is not a programming language for humans. It's an IR for capturing *why* an LLM concluded what it concluded. The goal is reconstructing the chain of reasoning, not producing readable code.

## What We Arrived At

### The Core Model

A CLAIR document is a **DAG of beliefs**. Each belief has:

```
belief := id confidence level source justifications? invalidations? content
```

The 4 pillars:
1. **Confidence** — calibrated reliability [0,1]
2. **Provenance** — where it came from (@user, @self, @file, etc.)
3. **Justification** — backward edges to supporting beliefs
4. **Invalidation** — conditions that would defeat this belief

### Key Design Decisions

| Decision | Rationale |
|----------|-----------|
| Not JSON | Too verbose for real programs |
| No alternatives explanation | Confidence score IS the judgment |
| Levels for self-reference | Prevents bootstrapping, provable in Lean |
| Löb discount (c → c²) | Confidence decreases through meta-levels |
| 0.5 = maximal uncertainty | Not algebraic neutrality, but "no evidence either way" |
| Absence = no belief | No ⊥ needed; omission is meaningful |
| Natural language answers | Debug scores optional; users get readable explanations |
| No type system | Content is opaque; LLMs interpret natural language |

### The Spec

Written to: `formal/clair-spec.md`

## Examples Explored

### 1. PI Calculation (Algorithm Selection)
```
b1 1.0 L0 @user "calculate PI to N decimal places"
b2 .95 L0 @self <b1 "arbitrary precision needed for large N"
b3 .3 L0 @self <b2 "Leibniz series"
b4 .85 L0 @self <b2 "Chudnovsky algorithm"
b5 .5 L0 @self <b2 "Machin formula"
b6 .8 L0 @self <b4 ?["n<15"] "use Chudnovsky"
```
**Lesson:** Alternatives captured via confidence scores at same parent. Highest wins.

### 2. HTML Parser (System Design)
```
b1 1.0 L0 @user "design HTML parser for head, title, meta tags"
b6 .95 L0 @self <b2 "architecture: tokenizer → parser → AST"
b7 .4 L0 @self <b6 "regex tokenizer"
b8 .8 L0 @self <b6 "state machine tokenizer"
b9 .85 L0 @self <b8 ?["need_streaming"] "use state machine tokenizer"
```
**Lesson:** Design decisions flow naturally; trace answers "why?" questions.

### 3. File Summary (Reading External Content)
```
b1 1.0 L0 @user "open config.yaml and summarize"
b2 1.0 L0 @file:config.yaml "database:\n  host: localhost..."
b3 .95 L0 @self <b1,b2 "3 sections: database, cache, logging"
b7 .85 L0 @self <b3,b4,b5,b6 "summary: production config..."
```
**Lesson:** File content becomes a belief with @file source. Subsequent questions reference it.

### 4. Conditional (Purple Sky)
```
b1 .01 L0 @self "the sky is purple"
b2 1.0 L0 @user "if sky is purple → one sock to pool"
b3 .01 L0 @self <b1,b2 "I will wear one sock to the pool"
```
**Lesson:** Conditionals = beliefs about rules. Low confidence in antecedent → low confidence in conclusion. No special syntax needed.

### 5. Self-Reference (Stratification)
```
b1 .9 L0 @self "X is true"
b2 .81 L1 @self <b1 "I believe b1"      ; .9² = .81
b3 .65 L2 @self <b2 "I believe b2"      ; .81² ≈ .65
```
**Lesson:** Levels prevent bootstrapping. Löb discount ensures confidence decreases through meta-levels.

### 6. Liar Paradox
```
b1 .5 L0 @self "this statement is false"
```
**Lesson:** No cycle (content self-reference ≠ justification cycle). 0.5 is the honest answer to undecidable propositions. CLAIR doesn't explode.

### 7. Unknown (Alien Colors)
```
b1 1.0 L0 @user "what color are aliens?"
b2 .3 L0 @self <b1 "aliens exist"
b3 .1 L0 @self <b2 "cannot determine color without evidence"
; No beliefs about specific colors — absence is meaningful
```
**Lesson:** Don't output beliefs you have no basis for. Absence = "I don't know". No ⊥ needed.

## Stress Tests Passed

| Test | Result |
|------|--------|
| Simple reasoning chains | ✓ Works |
| Alternatives with ranking | ✓ Confidence scores |
| External file content | ✓ @file source |
| Conditionals | ✓ Beliefs about rules |
| Self-reference | ✓ Levels + Löb discount |
| Liar paradox | ✓ 0.5, no explosion |
| Unknown/no evidence | ✓ Absence, no ⊥ |
| Program growth across turns | ✓ Graph extends |
| Type system needed? | ✗ Not needed; content is opaque NL |

## Architecture: Thinker + Assembler

CLAIR is not a standalone programming language. It's the **interface between reasoning and implementation**.

```
┌─────────────────┐
│  Thinking LLM   │  ← Reasons, produces CLAIR
│  (e.g., Opus)   │     "what to compute and why"
└────────┬────────┘
         │ CLAIR trace
         ▼
┌─────────────────┐
│  Assembler LLM  │  ← Reads CLAIR, produces executable
│  (e.g., Haiku)  │     "how to actually implement it"
└────────┬────────┘
         │ Code / IR
         ▼
┌─────────────────┐
│  Runtime/LLVM   │  ← Executes
└─────────────────┘
```

**Both LLMs understand CLAIR.** That's the contract.

| Role | Input | Output | Optimized for |
|------|-------|--------|---------------|
| Thinker | User request | CLAIR trace | Reasoning, planning, justification |
| Assembler | CLAIR trace | Executable | Code generation, syntax, correctness |

### Why This Matters

- **No programming languages needed** — humans wrote code for compilers; LLMs can go direct
- **Separation of concerns** — reasoning vs. implementation
- **Swappable assemblers** — same CLAIR → JS, Python, WASM, LLVM
- **Auditable** — reasoning preserved regardless of target
- **Different models** — optimize thinker for reasoning, assembler for code gen

### Computation as Beliefs

The thinker doesn't output code. It outputs beliefs about computation:

```
b5 .9 L0 @self <b4 "iterate k from 0 to n/14"
b6 .9 L0 @self <b5 "compute factorial(6k)"
b7 .9 L0 @self <b5 "compute (13591409 + 545140134*k)"
b8 .85 L0 @self <b6,b7 "divide and accumulate into sum"
```

The assembler LLM interprets these natural language beliefs and produces actual executable code. No formal pseudocode syntax needed — the assembler understands natural language.

### The Vision

Traditional: `Human → Programming Language → Compiler → Machine Code`

CLAIR: `Human → Thinker LLM → CLAIR → Assembler LLM → Machine Code`

Programming languages existed for humans. CLAIR exists for LLMs.

## Why No Type System?

CLAIR intentionally has no type system for content. This is a feature, not a limitation.

### Types Were for Compilers

Traditional type systems exist because compilers need to:
- Allocate memory (what size?)
- Check compatibility (can I add these?)
- Catch errors before runtime

LLMs don't have these constraints. They understand "iterate k from 0 to n" without needing `k : Int`.

### Content is Opaque

The `content` field is a natural language string. The Assembler LLM interprets it:

```
b9 .9 L0 @self <b8 "need: factorial function"
```

The Assembler knows what a factorial is. It doesn't need `factorial : Nat → Nat`.

### The Structure IS the Type System

CLAIR has structural constraints — just not content types:

| Structural constraint | Enforced by |
|----------------------|-------------|
| Confidence in [0,1] | Grammar |
| Valid ID references | DAG integrity |
| Stratification levels | Level rules |
| Provenance tracking | Source field |

This is sufficient for reasoning traces.

### Adding Types = Designing a Language

The moment you add `Int`, `String`, `Function`, you're designing a programming language. We explicitly moved away from that. CLAIR is a **data format**, not a **programming language**.

### When Types Might Matter

If CLAIR ever needed machine verification (not LLM interpretation), types could help. But that's the dissertation's formal Lean spec territory — not the practical IR.

## Open Questions / Future Work

1. **Storage**: Currently Option 0 (in-context). Need file-based for real programs.
2. **Edge types**: May need AND vs OR (conjunctive vs independent) — not yet required.
3. **Active defeat**: May need "X undermines Y" — not yet required.
4. **Parser**: No parser exists yet for the format.
5. **Lean verification**: Stratification rules should be provable.
6. **Assembler protocol**: How does assembler report back errors/confidence?

## Where We Left Off

- Spec is stable at `formal/clair-spec.md`
- Examples cover algorithm selection, system design, file reading, conditionals, self-reference, paradoxes, unknowns
- Type system question resolved: not needed (content is opaque natural language)
- Ready to: write more examples, build parser, or connect to dissertation

## Files Modified

- `formal/clair-spec.md` — the minimal spec (created)
- `examples/pi-calculation.md` — complete end-to-end example (created)
- `notes/exploration-2026-01-29-minimal-spec.md` — this document
