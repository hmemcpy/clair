# CLAIR Specification v0.1

**CLAIR: Comprehensible LLM AI Intermediate Representation**

A minimal serialization format for reasoning traces.

## Overview

A CLAIR document is a directed acyclic graph of beliefs. Each belief captures:

1. **Confidence** — how certain (calibrated reliability)
2. **Provenance** — where it came from
3. **Justification** — what supports it (backward edges)
4. **Invalidation** — when to reconsider (forward conditions)

## Grammar

```
document := belief*

belief := id confidence level source justifications? invalidations? content

id             := [a-z][a-z0-9_]*
confidence     := number in [0,1]
level          := "L" [0-9]+
source         := "@" source_type (":" reference)?
source_type    := "user" | "ctx" | "self" | "file" | "model"
justifications := "<" id ("," id)*
invalidations  := "?" "[" condition ("," condition)* "]"
condition      := quoted_string
content        := quoted_string
```

## Components

| Component | Meaning |
|-----------|---------|
| `id` | Unique identifier for this belief |
| `confidence` | Calibrated reliability in [0,1] |
| `level` | Stratification level for self-reference safety |
| `source` | Provenance — where this belief originated |
| `justifications` | Why — edges to supporting beliefs |
| `invalidations` | When to reconsider this belief |
| `content` | The proposition (opaque) |

## Source Types

| Type | Meaning |
|------|---------|
| `@user` | From user input |
| `@ctx` | From context (files, environment) |
| `@self` | Derived by the reasoning system |
| `@file:path` | From specific file |
| `@model:name` | From specific model |

## Confidence Semantics

Confidence is **calibrated reliability** in [0,1]:

| Value | Meaning |
|-------|---------|
| 1.0 | Certain (axiomatic, from trusted source) |
| 0.0 | Certainly false (contradicted, defeated) |
| 0.5 | **Maximally uncertain** — no evidence either way |
| >0.5 | Net evidence for |
| <0.5 | Net evidence against |

### The Meaning of 0.5

0.5 represents **maximal uncertainty**, not algebraic neutrality. It is appropriate when:

- No evidence exists either way
- Evidence is perfectly balanced
- The proposition is fundamentally undecidable (e.g., liar paradox)

Note: 0.5 is *not* neutral under confidence operations:
- `0.5 × 0.5 = 0.25` (confidence decreases through derivation)
- `0.5 ⊕ 0.5 = 0.75` (independent evidence aggregates upward)

This is intentional. "I don't know" combined with "I don't know" from an independent source *should* yield more information than either alone. The algebra reflects this.

### When to Use 0.5

```
b1 .5 L0 @self "this statement is false"     ; undecidable — .5 is correct
b2 .5 L0 @self "coin will land heads"        ; no evidence — .5 is correct
b3 .5 L0 @self <b1,b2 "some derived belief"  ; .5 × .5 = .25 — uncertainty compounds
```

### Absence of Belief (No ⊥ Needed)

If I have no basis for a belief, I don't output one. Absence from the trace IS the representation of "I don't know."

| State | Representation |
|-------|----------------|
| Uncertain but tracking | `belief("X", 0.5)` |
| No basis to even track | Omit from trace |
| Explaining why no belief | `belief("insufficient evidence for X", 0.1)` |

This is analogous to `Option<Belief>`:
- `Some(belief)` = I have a belief (any confidence)
- `None` = I chose not to form a belief

Example — "What color are aliens?":
```
b1 1.0 L0 @user "what color are aliens?"
b2 .3 L0 @self <b1 "aliens exist"
b3 .1 L0 @self <b2 "cannot determine color without evidence"
; No beliefs about specific colors — absence is meaningful
```

We don't need a bottom value (⊥). Not outputting a belief is not an error — it's a valid epistemic state.

## Semantics

### Answering "Why?"

To answer "Why X?", trace justification edges backward. The chain of content is the explanation.

The answer should be **natural language**, not raw scores. The LLM:
1. Traces the graph to find the justification chain
2. Synthesizes a readable explanation using the chain + general knowledge
3. The trace ensures the answer is grounded, not hallucinated

**Example query:** "Why state machine for tokenization?"

**Trace:** `b8 ← b7 ← b5 ← b1`

**Answer:** "I used a state machine because HTML tokenization requires tracking context — inside tags, inside quotes, reading attributes. A state machine handles these transitions cleanly."

### Debug Output

Scores can be shown as optional debug information:

```
[debug: b8 .8 <b7 | alternatives: b6 .4 regex]
```

Debug info shows: belief ID, confidence, justification, and alternatives considered. Available on request for auditing, not shown by default.

### Alternatives

Multiple beliefs may share the same justification parent. Confidence ranks them. Highest confidence wins. No explanation of scores required — the score *is* the judgment.

### Validity Constraints

- Graph must be acyclic (no belief can transitively justify itself)
- All referenced IDs must exist
- Confidence must be in [0,1]
- Stratification must be respected (see below)

## Stratification (Self-Reference Safety)

To prevent confidence bootstrapping through self-reference, beliefs have levels.

### Rules

1. **Level constraint**: A belief at level N can only justify beliefs at level ≥ N
2. **Meta-belief constraint**: A belief *about* another belief must be at a higher level
3. **Löb discount**: If belief b2 at level L+1 references belief b1 at level L, then `conf(b2) ≤ conf(b1)²`

### Example (Valid)

```
b1 .9 L0 @self "X is true"
b2 .81 L1 @self <b1 "I believe b1"      ; .9² = .81 ✓
b3 .65 L2 @self <b2 "I believe b2"      ; .81² ≈ .65 ✓
```

### Example (Invalid — Bootstrap Attempt)

```
b1 .9 L0 @self "I am reliable"
b2 .95 L0 @self <b1 "my beliefs are trustworthy"  ; ✗ same level self-reference
```

### Why This Works

The Löb discount (c → c²) ensures confidence strictly decreases through meta-levels. You cannot inflate confidence by reasoning about your own reliability. This property is formally verifiable in Lean.

## Example

```
b1 1.0 L0 @user "calculate PI to N decimal places"
b2 .95 L0 @self <b1 "arbitrary precision needed for large N"
b3 .3 L0 @self <b2 "Leibniz series"
b4 .85 L0 @self <b2 "Chudnovsky algorithm"
b5 .5 L0 @self <b2 "Machin formula"
b6 .8 L0 @self <b4 ?["n<15"] "use Chudnovsky"
b7 .8 L0 @self <b6 "function chudnovsky(n) { ... }"
```

Most reasoning stays at L0. Levels increase only for meta-beliefs (beliefs about beliefs).

### Query: "Why Chudnovsky?"

Trace: `b6 ← b4 ← b2 ← b1`

Answer: "User needed PI to N digits → required arbitrary precision → Chudnovsky satisfied this with highest confidence (.85 vs .5 and .3)"

### Query: "When to reconsider?"

Check invalidations: `b6 ?["n<15"]`

Answer: "Reconsider if n < 15 (Chudnovsky may be overkill for small N)"

## Non-Compositional Design

CLAIR is a **data format**, not a programming language. This has important implications:

### Beliefs Don't Compose

In functional programming, monads compose via bind:
```
b1 >>= f >>= g  -- chain computations
```

CLAIR has no such operation. Beliefs are **nodes in a DAG**, not composable computations. The Thinker LLM produces traces with whatever structure the reasoning requires.

### What This Means

| Concept | CLAIR Status |
|---------|--------------|
| Monadic bind (`>>=`) | ❌ Not applicable |
| Functorial map | ❌ Not applicable |
| Return/pure | ❌ Not applicable |
| Confidence propagation | ✅ Applies (through derivation chains) |
| Confidence algebra | ✅ Applies (×, min, ⊕ operations) |

### Confidence Still Propagates

When a belief is justified by others, confidence flows through the chain:

```
b1 .9 L0 @self "X"
b2 .8 L0 @self "Y"
b3 .72 L0 @self <b1 <b2 "therefore Z"   ; 0.9 × 0.8 = 0.72
```

The confidence algebra (Chapter 3 of the dissertation) specifies how:
- `c₁ × c₂` — sequential derivation (confidence multiplies)
- `min(c₁, c₂)` — conservative combination
- `c₁ ⊕ c₂ = 1 - (1-c₁)(1-c₂)` — independent evidence aggregation

These are **constraints on valid traces**, not operations the format itself provides.

### Traces Don't Compose Either

You can:
- **Extend** a trace by adding new beliefs that reference existing ones
- **Merge** traces if they share belief IDs (union of nodes/edges)
- **Query** a trace for justification paths

But there's no formal `trace₁ ⊗ trace₂ → trace₃` with algebraic laws.

**Analogy**: JSON doesn't have a composition operation. You can merge JSON objects, but there's no algebraic structure. CLAIR traces are similar—structured data, not composable computations.

## Future Extensions

The following may be added as needed:

- **Edge types** — distinguish conjunctive (AND) vs independent (OR) justification
- **Active defeat** — beliefs that undermine other beliefs
- **Structured content** — typed content beyond opaque strings
- **Persistent storage** — file-based storage for growing programs across turns

### Storage (Future)

Currently, CLAIR traces can live in conversation context (Option 0). For larger programs:

**Option 1: File-based**
```
; session.clair - appended each turn
b1 1.0 @user "open config.yaml..."
b2 1.0 @file:config.yaml "..."
b8 1.0 @user "count words..."  ; later turn
b10 .9 @self <b9 "18 tokens"
```

LLM reads file at start of turn, appends new beliefs, writes back. Context stays free for reasoning.

**Option 2: Embedded in response** — trace travels with each message (context grows)

**Option 3: External store** — database holds graph, LLM queries/updates

File-based (Option 1) is simplest for persistence without context bloat.

## Relationship to Formal Specification

This document describes the practical IR format. The formal semantics (confidence algebra, defeat operations, stratified self-reference) are specified in the dissertation appendices and may be verified in Lean.
