#import "../layout.typ": *

// Chapter 10: Implementation
#heading(level: 1)[Implementation]

This chapter documents CLAIR as implemented: not as a standalone programming language, but as an #emph[intermediate representation] for reasoning traces produced by LLMs and consumed by other LLMs. We describe the Thinker+Assembler architecture, the minimal CLAIR format, and the formal verification in Lean.

#heading(level: 2)[10.1 Architectural Overview]

CLAIR is the interface between two LLMs with complementary roles:

#heading(level: 3)[10.1.1 The Thinker+Assembler Architecture]

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

#emph[Both LLMs understand CLAIR.] This is the contract. The Thinker produces structured reasoning that the Assembler can interpret, and humans can audit.

#heading(level: 3)[10.1.2 Role Separation]

+---+---+
| *Role* | *Input* | *Output* | *Optimized for* |
+---+---+
| Thinker | User request | CLAIR trace | Reasoning, planning, justification |
| Assembler | CLAIR trace | Executable code | Code generation, syntax, correctness |
+---+---+

This separation provides several benefits:

1. #emph[Auditable reasoning]: The CLAIR trace captures #emph[why], not just #emph[what]
2. #emph[Swappable assemblers]: Same CLAIR trace can target Python, JavaScript, LLVM, etc.
3. #emph[Different model strengths]: Thinker optimized for reasoning, Assembler for code gen
4. #emph[Debugging]: When code is wrong, trace shows where reasoning went astray

#heading(level: 3)[10.1.3 Why Not a Traditional Programming Language?]

Programming languages were designed for humans to communicate with compilers. CLAIR is designed for LLMs to communicate with each other.

| Traditional | CLAIR |
|-------------|-------|
| `Human → Language → Compiler` | `Human → Thinker → CLAIR → Assembler` |
| Syntax optimized for human parsing | Format optimized for LLM parsing |
| Types for compiler verification | Content is natural language |
| Code IS the artifact | Reasoning trace IS the artifact |

CLAIR's content is #emph[opaque natural language strings]. The Assembler LLM interprets them using its general knowledge. No type system is needed because LLMs understand natural language.

#heading(level: 2)[10.2 The CLAIR Format]

A CLAIR document is a #emph[directed acyclic graph (DAG) of beliefs].

#heading(level: 3)[10.2.1 Belief Structure]

Each belief captures the four pillars (Chapter 4):

```
belief := id confidence level source justifications? invalidations? content
```

| Component | Meaning |
|-----------|---------|
| `id` | Unique identifier (e.g., `b1`, `b2`) |
| `confidence` | Calibrated reliability in [0,1] |
| `level` | Stratification level for self-reference safety |
| `source` | Provenance (@user, @self, @file, etc.) |
| `justifications` | Backward edges to supporting beliefs |
| `invalidations` | Conditions that would defeat this belief |
| `content` | The proposition (opaque natural language string) |

#heading(level: 3)[10.2.2 Example: Algorithm Selection]

```clair
; User request becomes a belief
b1 1.0 L0 @user "calculate PI to N decimal places"

; Thinker reasons about requirements
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"

; Algorithm alternatives with confidence scores
b4 .3 L0 @self <b3 "Leibniz series"
b5 .5 L0 @self <b3 "Machin formula"
b6 .85 L0 @self <b3 "Chudnovsky algorithm"

; Decision with invalidation condition
b7 .85 L0 @self <b6 ?["n<20"] "use Chudnovsky algorithm"

; Computation steps
b8 .9 L0 @self <b7 "iterate k from 0 until precision reached"
b9 .9 L0 @self <b8 "compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b10 .9 L0 @self <b9 "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
```

The Assembler reads this trace and produces executable Python code. See `examples/pi-calculation.md` for the complete example.

#heading(level: 3)[10.2.3 Source Types]

| Type | Meaning |
|------|---------|
| `@user` | From user input |
| `@self` | Derived by the reasoning system |
| `@file:path` | From specific file |
| `@model:name` | From specific model |
| `@ctx` | From context |

#heading(level: 3)[10.2.4 Confidence Semantics]

Confidence is #emph[calibrated reliability] in [0,1]:

| Value | Meaning |
|-------|---------|
| 1.0 | Certain (axiomatic, from trusted source) |
| 0.0 | Certainly false (contradicted, defeated) |
| 0.5 | Maximally uncertain (no evidence either way) |
| >0.5 | Net evidence for |
| <0.5 | Net evidence against |

0.5 represents maximal uncertainty, not algebraic neutrality. This is intentional:
- `0.5 × 0.5 = 0.25` (confidence decreases through derivation)
- `0.5 ⊕ 0.5 = 0.75` (independent evidence aggregates upward)

#heading(level: 2)[10.3 Stratification and the Löb Discount]

To prevent confidence bootstrapping through self-reference, CLAIR uses stratification levels.

#heading(level: 3)[10.3.1 Level Rules]

1. #emph[Level constraint]: A belief at level N can only justify beliefs at level ≥ N
2. #emph[Meta-belief constraint]: A belief #emph[about] another belief must be at a higher level
3. #emph[Löb discount]: If belief b₂ at level L+1 references belief b₁ at level L, then `conf(b₂) ≤ conf(b₁)²`

#heading(level: 3)[10.3.2 Example: Confidence Decay Through Meta-Levels]

```clair
b1 .9 L0 @self "X is true"
b2 .81 L1 @self <b1 "I believe b1"      ; .9² = .81
b3 .65 L2 @self <b2 "I believe b2"      ; .81² ≈ .65
```

This ensures an agent cannot inflate confidence by reasoning about its own reliability:
- Starting at 0.9 confidence
- Level 1: 0.81 (squared)
- Level 2: 0.65 (squared again)
- Level 3: 0.43 (squared again)

No finite chain of meta-reasoning can bootstrap confidence back up.

#heading(level: 3)[10.3.3 Formal Verification]

The Löb discount and stratification properties are formalized in Lean:

```lean
/-- Löb discount reduces confidence (unless already at 0 or 1) -/
theorem loebDiscount_le (c : Confidence) : (loebDiscount c : ℝ) ≤ (c : ℝ) :=
  mul_le_left c c

/-- Anti-bootstrapping: No finite chain of meta-reasoning can increase confidence -/
theorem no_confidence_bootstrap (c : Confidence) (k : Nat) :
    (loebChain c k : ℝ) ≤ (c : ℝ)
```

See `formal/lean/CLAIR/Belief/Stratified.lean` for the complete formalization.

#heading(level: 2)[10.4 DAG Structure]

#heading(level: 3)[10.4.1 Acyclicity Requirement]

The justification graph must be acyclic:
- No belief can transitively justify itself
- This ensures all beliefs are grounded in axioms

#heading(level: 3)[10.4.2 Formal Definition]

```lean
/-- A CLAIR document is acyclic -/
def Acyclic (doc : CLAIRDocument) : Prop :=
  ∀ b : BeliefId, ¬ Reachable doc b b

/-- A belief is grounded if traceable to axioms -/
inductive Grounded (doc : CLAIRDocument) : BeliefId → Prop where
  | axiom : ... → Grounded doc id
  | derived : ... → (∀ e ∈ b.justifications, Grounded doc e.premise) →
      Grounded doc id
```

See `formal/lean/CLAIR/Belief/DAG.lean` for the complete formalization.

#heading(level: 2)[10.5 Lean Formalization Status]

The formal verification in Lean covers:

#heading(level: 3)[10.5.1 Proven Properties]

+---+---+
| *Property* | *Location* | *Status* |
+---+---+
| Confidence bounds [0,1] | `Confidence/Basic.lean` | ✓ Proven |
| oplus commutative, associative | `Confidence/Oplus.lean` | ✓ Proven |
| oplus identity (0), absorbing (1) | `Confidence/Oplus.lean` | ✓ Proven |
| Non-distributivity (⊕, ×) | `Confidence/Oplus.lean` | ✓ Proven with counterexample |
| Undercut reduces confidence | `Confidence/Undercut.lean` | ✓ Proven |
| No self-introspection | `Belief/Stratified.lean` | ✓ Proven |
| No circular introspection | `Belief/Stratified.lean` | ✓ Proven |
| Löb discount reduces confidence | `Belief/Stratified.lean` | ✓ Proven |
| Anti-bootstrapping | `Belief/Stratified.lean` | ✓ Proven |
+---+---+

#heading(level: 3)[10.5.2 Properties with `sorry`]

| Property | Location | Notes |
|----------|----------|-------|
| Acyclic implies well-founded | `Belief/DAG.lean` | Infrastructure needed |
| Well-founded implies grounded | `Belief/DAG.lean` | Infrastructure needed |

These proofs require additional infrastructure (e.g., working with List membership and graph reachability). The statements are correct; full proofs are future work.

#heading(level: 2)[10.6 The Assembler's Role]

#heading(level: 3)[10.6.1 Interpreting CLAIR Traces]

The Assembler LLM reads a CLAIR trace and produces executable code. It uses:

1. #emph[Natural language understanding]: Content strings are interpreted semantically
2. #emph[Confidence awareness]: Lower confidence may warrant additional checks
3. #emph[Justification tracing]: Comments can reference belief IDs for auditability

#heading(level: 3)[10.6.2 Example: Assembler Output]

Given the PI calculation trace (Section 10.2.2), the Assembler might produce:

```python
"""
PI Calculator using Chudnovsky Algorithm

Generated from CLAIR trace.
Reasoning: b1 -> b3 -> b6 -> b7 -> b8-b10

To audit: "Why Chudnovsky?"
  b7 <- b6 "~14 digits per iteration"
  b6 <- b3 "need arbitrary precision"
  b3 <- b2 "N can be arbitrarily large"
  b2 <- b1 (user request)
"""

from decimal import Decimal, getcontext

def calculate_pi(n: int) -> str:
    # b3: Set arbitrary precision
    getcontext().prec = n + 50

    # b8-b10: Main Chudnovsky loop
    ...
```

The generated code includes comments linking to the reasoning trace for auditability.

#heading(level: 3)[10.6.3 Error Handling]

When the Assembler cannot interpret a trace:

1. It may request clarification from the Thinker
2. It may produce code with explicit uncertainty markers
3. It may report which beliefs were unclear

This feedback loop is part of the architecture but not formalized in this dissertation.

#heading(level: 2)[10.7 Querying CLAIR Traces]

CLAIR traces can answer questions about the generated code.

#heading(level: 3)[10.7.1 "Why?" Queries]

To answer "Why X?", trace justification edges backward:

Query: "Why Chudnovsky algorithm?"

Trace: `b7 ← b6 ← b3 ← b2 ← b1`

Answer: "The user requested PI to N decimal places, where N can be arbitrarily large. This requires arbitrary precision arithmetic. Chudnovsky was selected because it converges at ~14 digits per iteration (confidence .85 vs Leibniz .3 and Machin .5)."

#heading(level: 3)[10.7.2 "When to Reconsider?" Queries]

Check invalidation conditions:

Query: "When should I reconsider this choice?"

Trace: `b7 ?["n<20"]`

Answer: "If n < 20 digits, Chudnovsky may be overkill. Simpler methods would suffice."

#heading(level: 3)[10.7.3 Debug Output]

For technical auditing, scores can be shown:

```
[debug: b7 .85 <b6 | alternatives: b4 .3 Leibniz, b5 .5 Machin]
```

#heading(level: 2)[10.8 Comparison with Traditional Approaches]

| Aspect | Traditional Code | CLAIR Trace |
|--------|------------------|-------------|
| What is preserved | Implementation | Reasoning |
| Auditability | Comments (optional) | Justification DAG (mandatory) |
| Why questions | "Read the code" | Trace backward |
| Confidence | Implicit | Explicit |
| Reconsideration | Manual review | Invalidation conditions |
| Target flexibility | Fixed language | Any assembler |

#heading(level: 2)[10.9 Non-Compositional Design]

A crucial clarification: CLAIR is a #emph[data format], not a programming language. This distinction has important implications.

#heading(level: 3)[10.9.1 Beliefs Do Not Compose]

In functional programming, monads compose via bind:
```
b1 >>= f >>= g  -- chain computations, confidence multiplies
```

CLAIR has #emph[no such operation]. Beliefs are nodes in a DAG, not composable computations. The Thinker LLM produces traces with whatever structure the reasoning requires.

| Concept | CLAIR Status |
|---------|--------------|
| Monadic bind (`>>=`) | Not applicable |
| Functorial map | Not applicable |
| Return/pure | Not applicable |
| Confidence propagation | ✓ Applies (through derivation chains) |
| Confidence algebra | ✓ Applies (×, min, ⊕ operations) |

#heading(level: 3)[10.9.2 Confidence Still Propagates]

When a belief is justified by others, confidence flows through the chain:

```clair
b1 .9 L0 @self "X"
b2 .8 L0 @self "Y"
b3 .72 L0 @self <b1 <b2 "therefore Z"   ; 0.9 × 0.8 = 0.72
```

The confidence algebra (Chapter 3) specifies:
- $c_1 times c_2$ — sequential derivation (confidence multiplies)
- $min(c_1, c_2)$ — conservative combination
- $c_1 oplus c_2 = 1 - (1-c_1)(1-c_2)$ — independent evidence aggregation

These are #emph[constraints on valid traces], not operations the format provides.

#heading(level: 3)[10.9.3 Traces Do Not Compose Either]

You can:
- #emph[Extend] a trace by adding new beliefs that reference existing ones
- #emph[Merge] traces if they share belief IDs (union of nodes/edges)
- #emph[Query] a trace for justification paths

But there is no formal $"trace"_1 times.circle "trace"_2 -> "trace"_3$ with algebraic laws.

#strong[Analogy]: JSON has no composition operation. You can merge JSON objects, but there's no algebraic structure. CLAIR traces are similar—structured data, not composable computations.

#heading(level: 2)[10.10 Limitations]

#heading(level: 3)[10.10.1 Current Limitations]

1. #emph[No parser]: The CLAIR format is described but not parsed programmatically
2. #emph[No Assembler implementation]: LLMs serve as assemblers; no formal assembler exists
3. #emph[No persistent storage]: Traces are currently in-context or file-based
4. #emph[Incomplete Lean proofs]: 2 theorems use `sorry`

#heading(level: 3)[10.10.2 Fundamental Limitations]

As established in Chapter 12 (Impossibilities):

1. CLAIR cannot prove beliefs are true (tracking system, not proof system)
2. CLAIR cannot prove its own soundness (Gödel's 2nd theorem)
3. CLAIR cannot decide all invalidation conditions (Turing's halting problem)

These are not implementation gaps but fundamental limits that CLAIR acknowledges.

#heading(level: 2)[10.11 Future Work]

1. #emph[CLAIR parser]: Implement parser for the minimal format
2. #emph[Formal assembler protocol]: Define how Assembler reports errors/confidence
3. #emph[Multi-turn storage]: File-based storage for DAG growth across conversation turns
4. #emph[Complete Lean proofs]: Fill in remaining `sorry` placeholders
5. #emph[Visualization tools]: DAG visualization for debugging

#heading(level: 2)[10.12 Summary]

CLAIR is implemented as:

1. A #emph[minimal format] for reasoning traces (DAG of beliefs)
2. An #emph[interface] between Thinker and Assembler LLMs
3. A #emph[formal theory] verified in Lean (confidence algebra, stratification, DAG properties)

The key insight is that CLAIR is not a programming language for humans. It is an IR for LLMs. Programming languages existed for humans to communicate with compilers. CLAIR exists for LLMs to communicate with each other—and for humans to audit that communication.

#v(1em)
