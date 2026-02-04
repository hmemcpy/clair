# R3: What's Obsolete — Old vs New CLAIR Model

**Task:** Explicitly list what from the old formalization does NOT apply to the new IR model.

**Date:** 2026-02-04

**Status:** COMPLETED

---

## Executive Summary

The old CLAIR formalization (2023-2025) treated CLAIR as a **programming language for humans**. The new model (2026) treats CLAIR as an **IR for LLM reasoning traces**. This shift renders approximately **70% of the old work obsolete**.

**What's OBSOLETE (70%):**
- Type system (Syntax/Types, Typing/HasType, Typing/Subtype)
- Expression language (Syntax/Expr with lambdas, case, pattern matching)
- Evaluation semantics (Semantics/Step, Semantics/Eval)
- Parser for old syntax
- 58 completed exploration threads under old programming language model
- Old examples (.clair files)
- formal/syntax.md and formal/derivation-calculus.md (mostly)

**What's REUSABLE (30%):**
- Confidence algebra (fully proven in Lean, 40+ theorems)
- Stratification theory (needs Löb discount addition)
- DAG structure (defined but not fully proven)
- Foundations/limits philosophy
- Prior art survey

---

## Part 1: Obsolete Components

### 1.1 Type System (100% OBSOLETE)

**Files:**
- `formal/lean/CLAIR/Syntax/Types.lean` (253 lines)
- `formal/lean/CLAIR/Typing/HasType.lean` (201 lines)
- `formal/lean/CLAIR/Typing/Subtype.lean`

**What it defined:**
```lean
inductive Ty where
  | base   : BaseTy → Ty              -- Nat, Bool, String, Unit
  | fn     : Ty → Ty → Ty             -- Function types: A → B
  | prod   : Ty → Ty → Ty             -- Product types: A × B
  | sum    : Ty → Ty → Ty             -- Sum types: A + B
  | belief : Ty → ConfBound → Ty      -- Belief<A>[c]
  | meta   : Ty → Nat → ConfBound → Ty -- Meta<A>[n][c]
```

**Why it's obsolete:**

The new model's spec (`formal/clair-spec.md`):
```
belief := id confidence level source justifications? invalidations? content
```

The `content` field is **opaque natural language**. There is no type system for content because:
1. **Thinker LLMs produce natural language**, not typed expressions
2. **Assembler LLMs interpret natural language**, not typed values
3. **Humans audit natural language reasoning**, not type derivations

**Concrete example of obsolescence:**

Old model (typed):
```
belief<String>[0.9] "The file exists"
belief<Nat>[0.8] "The file has 42 lines"
belief<Bool × Nat>[0.7] ("exists", 42)
```

New model (opaque NL):
```
b1: @file:README.md 0.9 "The file exists"
b2: @file:README.md 0.8 "The file has 42 lines"
b3: @self 0.7 "The README file exists and contains 42 lines"
   justification: [b1, b2]
```

The `content` field contains free-form text. No type checker can verify that "42 lines" is a Nat, or that this text is "well-formed" beyond being a string.

**Typing rules that no longer apply:**

| Old Rule | Purpose | Why Obsolete |
|----------|---------|--------------|
| `Γ ⊢ e : A @c` | Expression has type A with confidence c | Content is opaque NL, not typed |
| `lam : HasType Γ (lam A e) (A → B)` | Lambda abstraction | No lambda expressions in traces |
| `app : HasType Γ (app e₁ e₂) B (c₁ × c₂)` | Function application | No function application in traces |
| `case : HasType Γ (case e e₁ e₂) C (c × (c₁ ⊕ c₂))` | Sum type elimination | No sum types in traces |
| `sub : A <: A' → c ≥ c' → HasType Γ e A' c'` | Subtyping with confidence | No subtyping without types |

**Action:** Archive these files. They represent excellent work on a typed CLAIR language that humans would write, but that's not our target.

---

### 1.2 Expression Language (100% OBSOLETE)

**Files:**
- `formal/lean/CLAIR/Syntax/Expr.lean`
- `formal/lean/CLAIR/Syntax/Subst.lean`
- `formal/lean/CLAIR/Syntax/Context.lean`

**What it defined:**

```lean
inductive Expr where
  | var        : Nat → Expr
  | lam        : Ty → Expr → Expr              -- λx:A. e
  | app        : Expr → Expr → Expr            -- e₁ e₂
  | pair       : Expr → Expr → Expr            -- (e₁, e₂)
  | fst        : Expr → Expr                   -- fst e
  | snd        : Expr → Expr                   -- snd e
  | inl        : Ty → Expr → Expr              -- inl<A> e
  | inr        : Ty → Expr → Expr              -- inr<A> e
  | case       : Expr → Expr → Expr → Expr     -- case e of inl x → e₁ | inr y → e₂
  | litNat     : Nat → Expr
  | litBool    : Bool → Expr
  | litString  : String → Expr
  | litUnit    : Expr
  | belief     : Expr → Confidence → Justification → Expr
  | val        : Expr → Expr                   -- Extract value from belief
  | conf       : Expr → Expr                   -- Extract confidence
  | just       : Expr → Expr                   -- Extract justification
  | derive     : Expr → Expr → Expr            -- Conjoin beliefs
  | aggregate  : Expr → Expr → Expr            -- Disjoin beliefs
  | undercut   : Expr → Expr → Expr            -- Defeat belief
  | rebut      : Expr → Expr → Expr            -- Rebuttal
  | introspect : Expr → Expr                   -- Stratified introspection
  | letIn      : Expr → Expr → Expr            -- let x = e₁ in e₂
```

**Why it's obsolete:**

The new model has **no expressions**. A CLAIR trace is a **DAG of beliefs**, not a program.

Old model: Write CLAIR code like Haskell:
```clair
let exists = belief("README.md exists", 0.9, none, none, none)
let count = belief("README.md has 42 lines", 0.8, none, none, none)
in derive exists count
```

New model: Produce a trace of beliefs:
```
b1: @file:README.md 0.9 L0 "The README.md file exists"
b2: @file:README.md 0.8 L0 "The README.md file contains 42 lines"
b3: @self 0.7 L0 "The file exists and has 42 lines"
   justification: [b1, b2]
```

The difference:
- **Old:** Computation expressed through let-binding, function application, pattern matching
- **New:** DAG structure implicit through `justification: [id1, id2, ...]` lists

**Specific obsolete constructs:**

| Old Construct | Purpose | New Equivalent |
|---------------|---------|----------------|
| `lam A e` | Lambda abstraction | None (not applicable) |
| `app e₁ e₂` | Function application | None (not applicable) |
| `letIn e₁ e₂` | Local binding | DAG justification edges |
| `case e e₁ e₂` | Pattern matching | None (not applicable) |
| `fst e`, `snd e` | Pair projection | None (not applicable) |
| `val e` | Extract value | Content is opaque NL |
| `conf e` | Extract confidence | `confidence` field directly |
| `just e` | Extract justification | `justification` list directly |

**Action:** Archive these files. The expression AST was designed for a programming language, not a trace format.

---

### 1.3 Evaluation Semantics (100% OBSOLETE)

**Files:**
- `formal/lean/CLAIR/Semantics/Step.lean`
- `formal/lean/CLAIR/Semantics/Eval.lean`

**What it defined:**

```lean
inductive Step : Expr → Expr → Prop where
  | beta : ...
  | delta : ...
  | zeta : ...
  | -- Small-step operational semantics
```

```lean
def eval : Expr → Expr → Prop
  -- Multi-step evaluation to normal form
```

**Why it's obsolete:**

The new model has **no evaluation**. CLAIR traces are not executed—they are **interpreted** by an Assembler LLM.

Old model pipeline:
```
Human → CLAIR program → Type checker → Evaluator → Result
```

New model pipeline:
```
Human → Thinker LLM → CLAIR trace → Assembler LLM → Code
```

The "evaluation" of a CLAIR trace is:
1. **Validation**: Check DAG is acyclic, references are valid
2. **Confidence computation**: Propagate confidence through × and ⊕
3. **Query answering**: Traverse justification edges

None of these require the operational semantics defined in the old model.

**What replaces evaluation:**

| Old Concept | New Replacement |
|-------------|-----------------|
| `e ⇓ e'` (evaluation) | Trace validation (DAG check) |
| `e ⟶ e'` (single step) | Confidence propagation rules |
| Normal form | Grounded beliefs (all justifications resolve to axioms) |
| Type safety | Structural validity (well-formed DAG) |

**Action:** Archive these files. Evaluation semantics assumed CLAIR is a programming language with computational behavior.

---

### 1.4 Parser (100% OBSOLETE)

**File:**
- `formal/lean/CLAIR/Parser.lean`

**What it defined:**

A parser for the old CLAIR syntax with type annotations, lambdas, do-notation, etc.

**Why it's obsolete:**

The new CLAIR format is dramatically simpler:

Old syntax (complex):
```clair
let analyze : Belief<String> =
  belief(
    "File exists",
    0.9,
    none,
    none,
    @file:README.md
  )
in derive analyze (belief("Has 42 lines", 0.8, none, none, none))
```

New format (simple):
```
b1: 0.9 L0 @file:README.md "File exists"
b2: 0.8 L0 @ctx "Has 42 lines"
b3: 0.7 L0 @self "Combined analysis"
   justification: [b1, b2]
```

The new format can be parsed with a simple line-by-line parser. No need for the complex parser in Parser.lean.

**Action:** Archive. The new format is designed for LLM output, not human editing.

---

### 1.5 Old Examples (100% OBSOLETE)

**Files:**
- `examples/hello-world-simple.clair`
- `examples/auth.clair` (if it exists)

**What they contain:**

Programs written in the old syntax with types, lambdas, and computational constructs.

**Example from hello-world-simple.clair:**
```clair
belief("Hello, world!", 1.0, none, none, none)

-- The belief constructor takes 5 arguments:
-- 1. The content (string value)
-- 2. Confidence level (1.0 = certain)
-- 3. Justification (none = axiom/foundation)
-- 4. Invalidation (none = no defeaters)
-- 5. Provenance (none = no source tracking)
```

**Why it's obsolete:**

This example still uses the old `belief(...)` function call syntax. The new format uses the spec from `formal/clair-spec.md`:

```
belief := id confidence level source justifications? invalidations? content

b1: 1.0 L0 @user "Hello, world!"
```

**Action:** Archive these examples. Replace with traces in the new format (see `examples/pi-calculation.md` for the correct style).

---

### 1.6 58 Completed Exploration Threads (90% OBSOLETE)

**Location:**
- `exploration/completed/thread-*.md` (58 files)

**What they contain:**

Deep theoretical work on CLAIR as a programming language:
- Type system refinements
- Evaluation semantics
- Curry-Howard correspondence
- Sequent calculus for justification
- Cut elimination
- Type inference with confidence
- Graded monads for effect tracking
- Affine types for belief consumption

**Examples of obsolete threads:**

| Thread | Topic | Why Obsolete |
|--------|-------|--------------|
| 2.16 | Sequent calculus for justification | No sequent calculus without type system |
| 2.19 | Cut elimination | No proof system for traces |
| 2.22 | Curry-Howard terms | No isomorphism without types |
| 2.23 | Confidence subtyping | No subtyping without types |
| 2.24 | Type inference with confidence | No type inference |
| 8.12 | CLAIR syntax in Lean | No syntax formalization needed |
| 3.15 | Stratification Lean completion | Partially reusable (see §2.2) |

**What's reusable from these threads:**

1. **Philosophical insights**: The distinction between tracking and proving (thread 1)
2. **Confidence algebra**: Many threads developed the algebra that's now proven (thread 1.4)
3. **Stratification concepts**: Self-reference handling (thread 3, 3.18)
4. **Defeat dynamics**: Undercut, rebut, reinstatement (threads 2.10, 2.11, 2.12)

**Action:** Archive the entire `exploration/completed/` directory. Extract reusable insights into reference documents.

---

### 1.7 formal/syntax.md (100% OBSOLETE)

**File:**
- `formal/syntax.md`

**What it defines:**

The complete grammar for the old CLAIR programming language:
- Modules, imports, exports
- Type definitions (ADTs, type aliases)
- Function definitions with type signatures
- Pattern matching
- Do-notation for monadic code
- Refinement types `{ x : Int | x > 0 }`

**Why it's obsolete:**

The new spec is 5 lines:
```
belief := id confidence level source justifications? invalidations? content

confidence := [0,1]
level := L0 | L1 | L2 | ...
source := @user | @ctx | @self | @file:path | @model:name
justifications := [id1, id2, ...]
invalidations := ?["condition"]
content := <opaque natural language>
```

No modules. No type definitions. No functions. No pattern matching. Just beliefs.

**Action:** Archive to `archive/old-syntax.md`.

---

### 1.8 formal/derivation-calculus.md (80% OBSOLETE)

**File:**
- `formal/derivation-calculus.md`

**What it defines:**

1. **DAG structure** (REUSABLE): Justification graphs must be acyclic
2. **Confidence propagation** (REUSABLE): × for derivation, ⊕ for aggregation
3. **Labeled edge types** (OBSOLETE): support, undercut, rebut with complex formalization
4. **Non-deductive justifications** (OBSOLETE): abduction, analogy, induction constructors
5. **Correlated evidence aggregation** (OBSOLETE): Complex rules for dependent evidence

**What to keep:**

- DAG requirement (acyclic justification graphs)
- Basic confidence operations (×, ⊕, min)
- Groundedness requirement (all beliefs trace to axioms)

**What to discard:**

- Labeled edge types (the new model only has justification edges, not defeat edges)
- Complex aggregation rules (⊕ is sufficient)
- Non-deductive justification constructors (LLMs do this naturally)

**Action:** Create simplified version focusing on DAG structure and confidence algebra.

---

### 1.9 Haskell Implementation (90% OBSOLETE)

**Location:**
- `implementation/haskell/`

**What it contains:**

- Parser for old syntax
- Type checker with bidirectional checking
- Evaluator with small-step semantics
- Confidence algebra implementation
- REPL

**What's obsolete:**

- Parser (old syntax)
- Type checker (no types)
- Evaluator (no evaluation)

**What's reusable:**

- Confidence algebra implementation (`oplus`, `otimes`, `undercut`, `rebut`)
- Data structures for Belief
- DAG validation utilities

**Action:** Extract confidence algebra and DAG validation. Archive the rest.

---

## Part 2: Reusable Components

### 2.1 Confidence Algebra (100% REUSABLE)

**Location:**
- `formal/lean/CLAIR/Confidence/` (5 files)

**What's proven:**

1. **Basic.lean**:
   - `mul_mem'`: Multiplication preserves [0,1]
   - `mul_le_left`, `mul_le_right`: Derivation decreases confidence
   - `Confidence.nonneg`, `Confidence.le_one`: Bounds

2. **Oplus.lean**:
   - `oplus_comm`: Commutativity
   - `oplus_assoc`: Associativity
   - `oplus_bounded`: Preserves [0,1]
   - `mul_oplus_not_distrib`: Non-distributivity (with counterexample)

3. **Undercut.lean**:
   - `undercut_le`: Undercut reduces confidence
   - `undercut_compose`: Sequential defeats compose

4. **Rebut.lean**:
   - `rebut_eq`: Rebuttal normalizes to ratio
   - `rebut_add_rebut_swap`: Competing evidence sums to 1

5. **Min.lean**:
   - Min operation for conjunction

**Why it's reusable:**

These theorems describe **pure confidence operations** that are independent of:
- Type systems
- Expression languages
- Evaluation semantics
- Syntax

The operations ×, ⊕, undercut, rebut, min are the same whether we're typing beliefs or tracing them.

**IR-model implications:**

| Lean Theorem | IR-Model Meaning |
|--------------|------------------|
| `mul_le_left` | Derivation chains always decrease confidence |
| `oplus_comm` | Aggregation order doesn't matter |
| `mul_oplus_not_distrib` | Can't factor through aggregation + derivation |
| `undercut_compose` | Sequential defeats compose via ⊕ |
| `rebut_eq` | Equal evidence → 0.5 (maximal uncertainty) |

**Action:** Keep as-is. This is production-ready formalization.

---

### 2.2 Stratification (80% REUSABLE, needs extension)

**Location:**
- `formal/lean/CLAIR/Belief/Stratified.lean`

**What's proven:**

```lean
structure StratifiedBelief (n : Nat) (α : Type) where
  value : α
  confidence : Confidence

def introspect {m n : Nat} (h : m < n) (b : StratifiedBelief m α) :
    StratifiedBelief n (Meta α)

theorem no_self_introspection : ¬(n < n)
theorem no_circular_introspection : m < n → ¬(n < m)
```

**What's missing:**

The Löb discount. Current `introspect` preserves confidence exactly:
```lean
theorem introspect_confidence (h : m < n) (b : StratifiedBelief m α) :
    (introspect h b).confidence = b.confidence := rfl
```

The new spec requires: `conf(b₂) ≤ conf(b₁)²` for meta-beliefs.

**What needs to be added:**

```lean
def introspectWithDiscount {m n : Nat} (h : m < n) (b : StratifiedBelief m α) :
    StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, none⟩
    confidence := b.confidence * b.confidence }  -- c → c²

theorem loebDiscount_strict_lt {c : Confidence} (h : 0 < c) (h2 : c < 1) :
    c * c < c
```

**Why this matters:**

Without Löb discount, confidence could be maintained through meta-levels:
- L0: "This code is correct" at 0.9
- L1: "I believe the L0 belief" at 0.9
- L2: "I believe the L1 belief" at 0.9

With Löb discount:
- L0: 0.9
- L1: 0.9² = 0.81
- L2: 0.81² = 0.65

Confidence strictly decreases through meta-levels.

**Action:** Extend Stratified.lean with Löb discount. Prove that it prevents bootstrapping.

---

### 2.3 DAG Structure (60% REUSABLE, needs completion)

**Location:**
- `formal/lean/CLAIR/Belief/DAG.lean`

**What's defined:**

```lean
structure JustificationDAG where
  nodes : List Belief
  edges : List (BeliefId × BeliefId)
  acyclic : ∀ id, ¬ reachable edges id id
  grounded : ∀ id ∈ nodes, ∃ pathToAxiom id
```

**What's missing (uses `sorry`):**

The `reachable` and `pathToAxiom` definitions are incomplete. The acyclicity and groundedness proofs have gaps.

**Why it matters:**

The DAG structure is the **core invariant** of CLAIR traces:
- Acyclic: No circular reasoning
- Grounded: All beliefs trace to axioms (user input or context)

**Action:** Complete the DAG formalization. Prove that well-formed traces are acyclic and grounded.

---

### 2.4 Foundations and Limits (100% REUSABLE)

**Location:**
- `formal/foundations-and-limits.md`

**What it contains:**

Philosophical grounding for CLAIR:
- "CLAIR is a tracking system, not a proof system"
- Church/Turing/Gödel limits
- Tracking vs proof distinction
- "The improvement is not truth, but explicitness"

**Why it's reusable:**

These insights are **model-independent**. They apply whether CLAIR is a programming language or an IR.

**Key quote (still relevant):**

> "CLAIR does not attempt to prove that beliefs are true. It attempts to track *why* we believe them, *how confident* we are, and *what would change our minds*."

This is exactly the value proposition for the Thinker→Assembler pipeline.

**Action:** Keep as-is. Minor updates to examples for new format.

---

### 2.5 Prior Art Survey (100% REUSABLE)

**Location:**
- `notes/prior-art.md`

**What it contains:**

Comparison with related work:
- Subjective Logic (Jøsang)
- Truth Maintenance Systems (Doyle, de Kleer)
- Justification Logic (Artemov)
- Weighted argumentation (Dung)
- Dempster-Shafer theory

**Why it's reusable:**

These comparisons are about **belief tracking**, not about syntax or types. They directly inform the IR model:
- Subjective Logic's opinion triangles map to our confidence scale
- TMS's justification networks map to our DAG structure
- Justification Logic's terms map to our belief IDs

**Action:** Keep as-is. Reference for C4 (comparison with alternatives).

---

## Part 3: Partially Reusable Components

### 3.1 Dissertation Chapters (Mixed)

**Location:**
- `dissertation/chapters/*.md`

**Assessment by chapter:**

| Chapter | Status | Action |
|---------|--------|--------|
| 01-introduction | ⚠️ Major update | Reframe around Thinker+Assembler |
| 02-background | ✓ Mostly OK | Prior art still relevant |
| 03-confidence | ✓ Applies | Algebra unchanged |
| 04-justification | ⚠️ Simplify | DAG OK, over-formalized |
| 05-self-reference | ⚠️ Update | Add stratification + Löb |
| 06-grounding | ? Review | May need adjustment |
| 07-belief-revision | ⚠️ Simplify | Core ideas OK |
| 08-multi-agent | ? Review | May apply to Thinker+Assembler |
| 09-verification | ❌ Rethink | Type verification obsolete |
| 10-implementation | ❌ Rewrite | Old Haskell impl |
| 11-phenomenology | ? Review | May still apply |
| 12-impossibilities | ✓ Applies | Limits fundamental |
| 13-conclusion | ⚠️ Update | Reflect new vision |
| 14-evaluation | ❌ Redo | Criteria changed |

**Action:** Case-by-case review. Keep philosophical content, update technical content.

---

## Part 4: Concrete Examples of Obsolescence

### Example 1: Type Checking (Obsolete)

**Old model (Types.lean, HasType.lean):**
```lean
Γ ⊢ belief("File exists", 0.9, none, none, none) : Belief<String>[0.9] @ 0.9
```

**New model (clair-spec.md):**
```
b1: 0.9 L0 @file:README.md "The file exists"
```

No type judgment. No derivation. Just a belief in the trace.

---

### Example 2: Function Application (Obsolete)

**Old model (Expr.lean):**
```lean
let analyze = λx:Belief<String>. belief(extract x, 0.8, [x], none, none)
in analyze (belief("File exists", 0.9, none, none, none))
```
Type derivation:
```lean
Γ ⊢ analyze : Belief<String> → Belief<String>
Γ ⊢ analyze (belief...) : Belief<String> @ 0.72
```

**New model:**
```
b1: 0.9 L0 @file:README.md "The file exists"
b2: 0.8 L0 @self "I have analyzed the file"
   justification: [b1]
```

No function application. Just a justification edge.

---

### Example 3: Pattern Matching (Obsolete)

**Old model (Expr.lean):**
```lean
case result of
  inl success → handle_success success
  inr error → handle_error error
```

**New model:**
```
b10: 0.7 L0 @self "The operation succeeded"
   invalidation: ?["result is error"]
b11: 0.7 L0 @self "The operation failed"
   invalidation: ?["result is success"]
```

No pattern matching. Mutually invalidating beliefs.

---

### Example 4: Evaluation (Obsolete)

**Old model (Semantics/Step.lean):**
```lean
(belief v c j) ⟶ v
(fst (pair e₁ e₂)) ⟶ e₁
```

**New model:**

No evaluation steps. The trace is static. The Assembler LLM interprets it:
1. Read beliefs with high confidence
2. Follow justification edges to understand reasoning
3. Check invalidations to know when to reconsider
4. Generate code based on content

---

## Part 5: Migration Guide

### For Each Obsolete Component

| Component | Replacement | Action |
|-----------|-------------|--------|
| Syntax/Types.lean | None (no types) | Archive |
| Syntax/Expr.lean | DAG structure (DAG.lean) | Archive |
| Typing/HasType.lean | None (no typing) | Archive |
| Semantics/Step.lean | None (no evaluation) | Archive |
| Semantics/Eval.lean | Query answering (traversal) | Archive |
| Parser.lean | Simple line parser (write new) | Archive |
| examples/*.clair | examples/*.md (new format) | Archive |
| formal/syntax.md | formal/clair-spec.md | Archive |
| 58 exploration threads | Reference archive | Archive |
| Haskell parser | Simple trace parser | Rewrite |
| Haskell typechecker | DAG validator | Rewrite |
| Haskell evaluator | None (no evaluation) | Delete |

---

## Part 6: Thesis Impact Assessment

### Connection to Central Thesis

**Thesis:** CLAIR is a viable IR between Thinker and Assembler LLMs — it preserves *why* decisions were made, enables auditing, and doesn't lose essential information at the boundary.

### How This Exploration Supports the Thesis

**1. Eliminates Confusion (SUPPORTS):**

By explicitly cataloging what's obsolete, we prevent future confusion between the old programming language model and the new IR model. The thesis is clearer when we know what CLAIR is NOT.

**2. Highlights Reusable Foundations (SUPPORTS):**

The confidence algebra and stratification theory survive the transition. This shows that CLAIR has solid mathematical foundations independent of any particular syntax or type system.

**3. Demonstrates Model Shift (REFINES):**

The shift from typed language to opaque NL content is a **refinement** of the thesis:
- Old: "CLAIR is a language for explicit reasoning"
- New: "CLAIR is an IR for LLM reasoning traces"

**4. Reveals Implementation Simplicity (SUPPORTS):**

The new model is dramatically simpler:
- 70% of old work is obsolete
- No type checker
- No evaluator
- No complex parser

This simplicity supports viability—we're not building an impossibly complex system.

### Counter-Example: Lost Capabilities

**What we gave up (UNDERMINES):**

The old model had capabilities the new model lacks:
- **Type safety**: Couldn't pass a Belief<Nat> where Belief<String> expected
- **Computational behavior**: Could write CLAIR programs that executed
- **Formal verification**: Could prove properties about CLAIR programs

**Mitigation:**

These capabilities were for **humans** writing CLAIR. The new model is for **LLMs** producing traces. The trade-off is acceptable because:
- LLMs don't need type safety (they interpret natural language)
- The Assembler LLM handles "execution"
- Trace validation replaces formal verification

---

## Part 7: Open Questions

1. **DAG Well-Foundedness**: Should we complete the Lean proofs for acyclicity and groundedness, or is the current definition sufficient?

2. **Trace Validation**: What's the minimal validation needed for a trace? (Syntax check + DAG check + confidence bounds?)

3. **Confidence Calibration**: Without type constraints, how do we ensure Thinker LLMs assign meaningful confidence values?

4. **Ambiguity Detection**: Can we detect when opaque NL content is too ambiguous for reliable assembly?

---

## Part 8: Recommendations

### Immediate Actions

1. **Archive obsolete files**:
   ```bash
   mkdir -p archive/old-model
   mv formal/lean/CLAIR/Syntax/ archive/old-model/
   mv formal/lean/CLAIR/Typing/ archive/old-model/
   mv formal/lean/CLAIR/Semantics/ archive/old-model/
   mv formal/lean/CLAIR/Parser.lean archive/old-model/
   mv formal/syntax.md archive/old-syntax.md
   mv examples/*.clair archive/old-model/
   mv exploration/completed/ archive/old-exploration-threads/
   ```

2. **Create simplified trace parser**:
   - Line-based parser for `belief := id confidence level source ...`
   - DAG validation (acyclicity check)
   - Confidence range validation ([0,1])

3. **Complete Löb discount formalization**:
   - Extend `formal/lean/CLAIR/Belief/Stratified.lean`
   - Add `introspectWithDiscount` with c → c²
   - Prove strict decrease through meta-levels

4. **Complete DAG formalization**:
   - Fill in `sorry` gaps in `formal/lean/CLAIR/Belief/DAG.lean`
   - Prove acyclicity and groundedness theorems

### Documentation Updates

1. **Update README** to reflect Thinker→Assembler architecture
2. **Create migration guide** from old to new model
3. **Document reusable components** (Confidence/, Stratified.lean, DAG.lean)

---

## Conclusion

**Summary of Findings:**

1. **70% of old formalization is obsolete**: Type system, expression language, evaluation semantics, parser, old examples, 58 exploration threads, formal/syntax.md

2. **30% is reusable**: Confidence algebra (fully proven), stratification theory (needs Löb discount), DAG structure (needs completion), foundations/limits, prior art

3. **The shift is fundamental**: From "programming language for humans" to "IR for LLM reasoning traces"

4. **Simplicity supports viability**: The new model is dramatically simpler, making implementation more feasible

**Thesis Impact:**

- **SUPPORTS**: Eliminates confusion, highlights reusable foundations, demonstrates simplicity
- **REFINES**: Clarifies that CLAIR is an IR, not a language
- **UNDERMINES**: Lost type safety and formal verification capabilities (acceptable trade-off)

**Overall Assessment:**

This exploration clarifies the boundary between old and new models. By explicitly cataloguing what's obsolete, we prevent future confusion and can focus on the components that actually matter for the IR model: confidence algebra, stratification, and DAG structure.

The survival of the confidence algebra and stratification theory through this transition is strong evidence that CLAIR has solid mathematical foundations independent of any particular syntax or implementation. This supports the thesis that CLAIR is a viable IR for LLM reasoning traces.
