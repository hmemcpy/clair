# CLAIR Reassessment — 2026-01-29

## Executive Summary

Our exploration on 2026-01-29 arrived at a fundamentally different conception of CLAIR than what exists in the current codebase. This document assesses all existing work against the new model.

**The New Model:**
- CLAIR is an **IR for reasoning traces**, not a programming language
- Produced by a **Thinker LLM** (e.g., Opus), consumed by an **Assembler LLM** (e.g., Haiku)
- **Content is opaque natural language** — no type system needed
- A **DAG of beliefs** with 4 pillars: confidence, provenance, justification, invalidation
- **Stratification levels** (L0, L1, L2...) with **Löb discount** (c → c²) for self-reference safety
- **0.5 = maximal uncertainty**, absence = no belief (no ⊥)

**The Old Model (in existing codebase):**
- CLAIR is a **full programming language** with rich type system
- Written by **humans** (like Haskell/ML)
- Has `Belief<Int>`, refinement types, effect types, modules
- Complex syntax: lambdas, do-notation, case expressions
- Haskell reference interpreter

---

## Assessment by Component

### 1. formal/syntax.md — ❌ OBSOLETE

**What it defines:**
- Full programming language syntax (modules, types, functions)
- `Belief<a>` as a parametric type wrapping values
- Refinement types `{ x : Int | x > 0 }`
- Effect types, ADTs, type aliases
- Do-notation, pattern matching, lambdas

**Conflict with new model:**
- New model: content is **opaque natural language strings**
- New model: **no type system** for content — LLMs interpret natural language
- New model: CLAIR is a **data format**, not a programming language

**Verdict:** This document describes a different language. Should be archived or completely rewritten.

---

### 2. formal/derivation-calculus.md — ⚠️ PARTIALLY APPLIES

**What still applies:**
- ✓ DAG structure (not trees)
- ✓ Confidence propagation formulas (min, multiply, oplus)
- ✓ Basic justification edges

**What may be over-engineered:**
- Labeled edge types (support, undercut, rebut) — our minimal spec only has support edges (justifications)
- Formal Lean structures for justification nodes
- Non-deductive justification constructors (abduction, analogy, induction) — LLMs do this naturally
- Complex aggregation rules (correlated evidence)

**Verdict:** Core ideas apply, but formalization is too heavy. Simplify to match minimal spec.

---

### 3. formal/foundations-and-limits.md — ✓ EXCELLENT, MINOR UPDATES

**What applies perfectly:**
- ✓ "CLAIR is a tracking system, not a proof system"
- ✓ Church/Turing/Gödel limits
- ✓ Tracking vs proof distinction
- ✓ "The improvement is not truth, but explicitness"

**What needs updating:**
- Self-reference handling: Replace "ill-formed beliefs" with stratification levels
- Update examples to use new minimal syntax

**Verdict:** This document is conceptually aligned with our new model. It validates that CLAIR doesn't try to prove — it tracks. Minor updates needed.

---

### 4. formal/clair-spec.md — ✓ THE NEW CANONICAL SPEC

This is the minimal spec we created. It supersedes syntax.md.

---

### 5. examples/*.clair — ❌ OBSOLETE

**hello-world.clair and auth.clair:**
- Written in the old "programming language" syntax
- Uses `Belief<String>`, `Effect<IO, Unit>`, refinement types
- Complex decision constructs with scores and criteria
- This is what a human programmer would write

**Conflict with new model:**
- New model: CLAIR traces are **produced by LLMs**, not written by humans
- New model: Content is natural language, not typed values
- No modules, no do-notation, no pattern matching

**Verdict:** These examples demonstrate the old paradigm. They should be archived. New examples should look like `examples/pi-calculation.md`.

---

### 6. implementation/haskell/ — ❌ NEEDS MAJOR RETHINKING

**What exists:**
- Full parser for old syntax
- Type checker with bidirectional checking
- Evaluator with small-step semantics
- Confidence algebra implementation

**What's still relevant:**
- ✓ Confidence algebra (`oplus`, `otimes`, `undercut`, `rebut`)
- ✓ Belief structure concept

**What's obsolete:**
- Parser for the old syntax
- Type checking (content is opaque natural language)
- Complex evaluation semantics

**New implementation needs:**
- Parser for the minimal CLAIR format (beliefs in DAG)
- DAG validation (acyclicity, valid references)
- Confidence computation from DAG
- Stratification validation

**Verdict:** Confidence algebra is reusable. Parser/typechecker need complete rewrite for minimal format.

---

### 7. formal/lean/ — ⚠️ PARTIALLY APPLIES (DETAILED ASSESSMENT)

**What EXISTS and is EXCELLENT:**

1. **Confidence algebra** (CLAIR/Confidence/):
   - ✓ `Basic.lean`: Bounds ([0,1]), multiplication closure, derivation decreases confidence
   - ✓ `Oplus.lean`: Commutative, associative, identity (0), absorbing (1), monotonicity
   - ✓ `Oplus.lean`: Non-distributivity PROVEN with counterexample (a=b=c=0.5)
   - ✓ `Undercut.lean`: Undercut semantics
   - ✓ `Rebut.lean`: Rebut semantics

2. **Stratification** (CLAIR/Belief/Stratified.lean):
   - ✓ `StratifiedBelief n α` with level indexing
   - ✓ `introspect` requires proof of `m < n`
   - ✓ `no_self_introspection`: proven `¬(n < n)`
   - ✓ `no_circular_introspection`: proven `m < n → ¬(n < m)`
   - ✓ Level 0 cannot be introspected from

**What's MISSING for new model:**

1. **Löb discount NOT implemented**: Current `introspect` preserves confidence exactly:
   ```lean
   theorem introspect_confidence (h : m < n) (b : StratifiedBelief m α) :
       (introspect h b).confidence = b.confidence := rfl
   ```
   Our new model requires: `conf(b₂) ≤ conf(b₁)²`

2. **DAG well-foundedness**: Not formalized (justification structure in Syntax, not Belief)

**What's OVER-ENGINEERED:**
- `CLAIR/Syntax/` - Complex expression AST for old programming language model
- `CLAIR/Typing/` - Type checking for typed content (content is now opaque NL)
- `CLAIR/Semantics/` - Evaluation semantics (Assembler LLM handles this)
- `CLAIR/Parser.lean` - Parser for old syntax

**Action items for Lean:**
1. ADD Löb discount to `introspect`:
   ```lean
   def introspectWithDiscount (h : m < n) (b : StratifiedBelief m α) : StratifiedBelief n (Meta α) :=
     { value := ⟨b.value, none⟩
       confidence := b.confidence * b.confidence }  -- c → c²
   ```
2. PROVE Löb discount prevents confidence bootstrapping
3. KEEP all Confidence/ proofs
4. KEEP Belief/Stratified.lean (update for Löb)
5. ARCHIVE or REMOVE Syntax/, Typing/, Semantics/, Parser.lean

**Verdict:** Confidence algebra is production-ready. Stratification needs Löb discount. Remove type system formalization.

---

### 8. Dissertation Chapters — ⚠️ MIXED

| Chapter | Status | Notes |
|---------|--------|-------|
| 01-introduction | ⚠️ NEEDS MAJOR UPDATE | Reframe around Thinker+Assembler architecture |
| 02-background | ✓ MOSTLY OK | Prior art still relevant |
| 03-confidence | ✓ APPLIES | Confidence algebra is unchanged |
| 04-justification | ⚠️ SIMPLIFY | DAG structure OK, but over-formalized |
| 05-self-reference | ⚠️ UPDATE | Add stratification levels + Löb discount |
| 06-grounding | ? REVIEW | May need adjustment |
| 07-belief-revision | ⚠️ SIMPLIFY | Core ideas OK, formal model may be too heavy |
| 08-multi-agent | ? REVIEW | May apply to Thinker+Assembler interaction |
| 09-verification | ❌ RETHINK | Type verification is obsolete |
| 10-implementation | ❌ REWRITE | Describes Haskell interpreter for old syntax |
| 11-phenomenology | ? REVIEW | May still apply |
| 12-impossibilities | ✓ APPLIES | Limits are fundamental |
| 13-conclusion | ⚠️ UPDATE | Reflect new vision |
| 14-evaluation | ❌ REDO | Evaluation criteria changed |

---

## Theoretical Foundations to Prove

### 1. Stratification Safety (HIGH PRIORITY) — PARTIALLY EXISTS

**Claim:** Stratification levels + Löb discount prevent confidence bootstrapping.

**What EXISTS in Lean:**
- ✓ `no_self_introspection`: `¬(n < n)` — can't introspect same level
- ✓ `no_circular_introspection`: `m < n → ¬(n < m)` — no circular references
- ✓ Level indexing prevents Liar-like paradoxes

**What's MISSING:**
- ✗ Löb discount: Current `introspect` preserves confidence exactly
- NEEDED: Prove that `conf(b₂) ≤ conf(b₁)²` for meta-beliefs

**Why it matters:** Without Löb discount, an agent could maintain high confidence through meta-levels. With c → c², confidence strictly decreases: 0.9 → 0.81 → 0.65 → ...

---

### 2. DAG Well-Foundedness (HIGH PRIORITY) — NOT FORMALIZED

**Claim:** Justification graphs must be acyclic (DAGs), ensuring all beliefs are grounded.

**Formalization needed:**
```lean
structure JustificationDAG where
  nodes : List Belief
  edges : List (Belief × Belief)  -- (conclusion, premise)
  acyclic : ∀ b, ¬ reachable edges b b
  grounded : ∀ b ∈ nodes, ∃ path to axiom
```

**Why it matters:** Cycles would create infinite regress or circular reasoning.

**Status:** Mentioned in derivation-calculus.md. NOT in Lean. NEEDED for minimal spec.

---

### 3. Confidence Bounds Preservation — ✓ PROVEN

**Claim:** All confidence operations preserve [0,1] bounds.

**Status:** ✓ Fully proven in Lean:
- `Confidence.nonneg`: `0 ≤ c`
- `Confidence.le_one`: `c ≤ 1`
- `mul_mem'`: multiplication closure
- `oplus_bounded`: oplus preserves bounds
- `undercut_le`: undercut reduces confidence

---

### 4. Non-Distributivity — ✓ PROVEN

**Claim:** (⊕, ×) do NOT form a semiring — distributivity fails.

**Status:** ✓ Proven with counterexample in `Oplus.lean`:
```lean
theorem mul_oplus_not_distrib :
    ∃ (a b c : Confidence),
      (a : ℝ) * ((oplus b c) : ℝ) ≠ ((oplus (a * b) (a * c)) : ℝ)
```
Using a = b = c = 0.5: `0.5 × 0.75 = 0.375 ≠ 0.4375`

**Why it matters:** This is fundamental — the operations form a "de Morgan bimonoid", not a semiring.

---

### 5. 0.5 as Maximal Uncertainty (SEMANTIC)

**Claim:** 0.5 represents maximal uncertainty, not algebraic neutrality.

**Note:** This is semantic, not a theorem. Document that:
- 0.5 × 0.5 = 0.25 (confidence decreases through derivation)
- 0.5 ⊕ 0.5 = 0.75 (independent evidence aggregates upward)

The algebra is correct — "I don't know" from two independent sources IS more informative than from one.

---

## Limits and Impossibilities

### What CLAIR Cannot Do (Unchanged)

From foundations-and-limits.md — these still apply:

| Limitation | Source |
|------------|--------|
| Prove beliefs are true | Fundamental (not the goal) |
| Prove its own soundness | Gödel's 2nd theorem |
| Decide all validity | Church's theorem |
| Check all invalidation conditions | Turing's halting problem |
| Justify its axioms internally | Foundational |

### New Insights

**CLAIR cannot type-check content** — because content is natural language. The Assembler LLM interprets it.

**CLAIR cannot prevent LLM hallucination** — but it can *track* justification chains so hallucinations are auditable.

**CLAIR cannot guarantee the Assembler produces correct code** — but it provides the reasoning trace to debug incorrect output.

---

## End-to-End Example Assessment

### Existing: examples/pi-calculation.md — ✓ GOOD

This demonstrates the full pipeline:
1. **Oracle (Thinker)** produces CLAIR trace with algorithm selection reasoning
2. **Assembler (Doer)** interprets trace and produces Python code
3. **Queries** show how trace answers "why?" questions

**Gaps in example:**
- Doesn't show what happens when Assembler encounters ambiguity
- Doesn't show error handling (what if Assembler can't interpret?)
- Doesn't show multi-turn growth (file-based storage)

### Recommended Additional Examples

1. **Error case**: Assembler returns low-confidence code, needs clarification
2. **Multi-turn**: Reading a file, then querying it, showing DAG growth
3. **Self-reference**: Demonstrating stratification in action
4. **Defeat**: Showing how new evidence updates confidence

---

## Action Items

### Immediate (Before Further Development)

1. **Archive old syntax.md** — move to `archive/old-syntax.md`
2. **Archive old examples** — move hello-world.clair and auth.clair to `archive/`
3. **Update README** — reflect new Thinker+Assembler architecture
4. **Create minimal parser** — for new CLAIR format (much simpler than old)

### Short-Term (Solidify Foundations)

5. **Prove stratification safety in Lean** — critical for self-reference claims
6. **Prove DAG well-foundedness** — formal guarantee
7. **Write 3-4 more examples** showing error cases, multi-turn, defeat
8. **Simplify derivation-calculus.md** — remove over-engineering

### Medium-Term (Dissertation Update)

9. **Rewrite Chapter 1** — Thinker+Assembler framing
10. **Rewrite Chapter 10** — New implementation approach
11. **Update Chapter 5** — Stratification levels + Löb discount
12. **Simplify Chapters 4, 7** — Remove excessive formalism

---

## The Vision (Restated)

Traditional: `Human → Programming Language → Compiler → Machine Code`

CLAIR: `Human → Thinker LLM → CLAIR → Assembler LLM → Machine Code`

**Programming languages existed for humans. CLAIR exists for LLMs.**

The Thinker reasons and produces a DAG of beliefs. The Assembler interprets and produces code. The trace preserves *why*. Humans can audit the trace. This is the value proposition.

---

## Files to Archive

```
archive/
├── old-syntax.md           (was formal/syntax.md)
├── hello-world.clair       (was examples/hello-world.clair)
├── auth.clair              (was examples/auth.clair)
└── old-implementation-notes.md
```

## Files to Keep/Update

```
formal/
├── clair-spec.md           ✓ NEW CANONICAL
├── foundations-and-limits.md  ⚠️ minor updates
├── derivation-calculus.md  ⚠️ simplify
└── lean/                   ⚠️ keep confidence, simplify rest

examples/
├── pi-calculation.md       ✓ GOOD
├── (new examples needed)

notes/
├── exploration-2026-01-29-minimal-spec.md  ✓
├── reassessment-2026-01-29.md              ✓ THIS DOCUMENT
```
