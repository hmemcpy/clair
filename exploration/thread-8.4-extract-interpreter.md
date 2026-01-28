# Thread 8.4: Extract Working Interpreter from Lean 4

**Status**: Exploration (Session 78)
**Task**: Produce runnable CLAIR evaluator demonstrating core properties
**Key Question**: What does "extracting a working interpreter" from Lean 4 actually mean?

---

## 1. What Problem Are We Solving?

We have a formal Lean 4 specification of CLAIR. The question is: how do we get from "formal specification" to "runnable artifact that proves CLAIR works"?

The naive interpretation: "Extract the Lean code to some target language and run it."

The deeper question: What does extraction mean in Lean 4, and what can we actually extract?

---

## 2. Understanding Lean 4 Code Extraction

### 2.1 What Lean 4 Actually Supports

Lean 4 has several mechanisms for producing runnable code:

1. **Native compilation** (`lake build` produces native code directly)
2. **Interpretation via `#eval`** (Lean's evaluator can run definitions)
3. **Code extraction to other languages** (historically supported in Lean 3, more limited in Lean 4)

The primary way to "run" Lean 4 code is via its native compiler. Lean 4 compiles to C, then to native code. This is not "extraction" in the Coq/Agda sense—it's compilation.

### 2.2 What Can Be Compiled?

- Pure functions: Yes
- Inductive types: Yes
- Recursive functions: Yes (with termination proofs or partial)
- Type class instances: Yes
- `sorry`: Treated as `panic!` or error at runtime

### 2.3 The `partial` Keyword

Lean 4 allows `partial` functions for cases where termination is hard to prove. This is useful for:
- Interpreters with potentially non-terminating programs
- REPLs and interactive systems

---

## 3. What Would a "Working Interpreter" Look Like?

### 3.1 Definition of Success

From IMPLEMENTATION_PLAN.md:

> The interpreter must demonstrate:
> 1. Beliefs track confidence (not just true/false)
> 2. Evidence is affine (no double-counting)
> 3. Introspection is safe (stratification prevents paradox)
> 4. Defeat works (undercut/rebut modify confidence correctly)
> 5. Type checking is decidable (already proven)

### 3.2 Minimum Viable Interpreter

A working CLAIR interpreter needs:

**Core Components:**
1. **Parser**: Convert surface syntax to `Expr`
2. **Type Checker**: Implement `HasType` judgment
3. **Evaluator**: Implement `Step` (small-step semantics)
4. **REPL**: Interactive interface for testing

**Key Insight**: The Lean formalization provides the *specification*. The interpreter is an *implementation* of that specification.

### 3.3 Two Approaches

**Approach A: Compile the Lean code directly**

- Write a `Main.lean` that uses the existing formalization
- Add a parser for surface syntax
- Implement the missing semantic rules (the stub in Step.lean)
- Compile with `lake build`

**Approach B: Extract to another language**

- Not well-supported in Lean 4
- Would require manual implementation
- Not recommended

**Recommendation**: Use Approach A. The "extraction" is really "compilation" of Lean 4 code with a driver.

---

## 4. Gap Analysis: What's Missing?

### 4.1 Current State of Lean Formalization

| Component | Status | Gaps |
|-----------|--------|------|
| Confidence operations | Complete | None |
| Belief type | Complete | None |
| Syntax (Types, Expr) | Complete | None |
| Typing rules | Complete | Weakening is sorry |
| Substitution | Stub | 3 sorrys |
| Semantics (Step) | Minimal | Most rules missing |

### 4.2 What Must Be Added

To have a working interpreter, we need:

1. **Complete the Step relation** with:
   - Projection rules for pairs
   - Case analysis rules for sums
   - Belief construction/deconstruction
   - Derivation evaluation
   - Aggregation evaluation
   - Undercut/Rebut evaluation
   - Introspection evaluation

2. **Add a parser** (can be minimal, using Lean's built-in parser)

3. **Add a driver/Main** for the REPL

4. **Add examples** demonstrating the five key properties

---

## 5. Design of the Interpreter

### 5.1 Architecture

```
Source Code (String)
       ↓
   [Parser]
       ↓
    Expr (AST)
       ↓
[Type Checker]  ← Uses HasType judgment
       ↓
   Type or Error
       ↓
[Evaluator]     ← Uses Step relation
       ↓
   Value
```

### 5.2 Key Design Decisions

**Decision 1: Surface Syntax**

Should we use:
- Custom syntax (requires parser)
- Lean's syntax (reuse Lean parser)
- S-expression syntax (easy to parse)

Recommendation: Start with S-expressions for the MVP. Easy to parse, unambiguous, clear structure.

**Decision 2: Type Checking Strategy**

Two approaches:
- Bidirectional (synthesizing/checking modes)
- Full inference with constraints

Recommendation: Bidirectional, matching the formal `HasType` judgment structure.

**Decision 3: Evaluation Strategy**

- Call-by-value (matching Step.lean)
- Call-by-name
- Lazy

Recommendation: Call-by-value (already specified).

**Decision 4: Handling `sorry`**

The formalization has `sorry` in:
- Substitution (3 places)
- Subtype (1 place)
- HasType weakening (1 place)

These need to be completed or marked `partial`.

---

## 6. Demonstrating the Five Properties

### 6.1 Beliefs Track Confidence

Example:
```
(let temp (belief 23 0.9)
 (let converted (derive temp (λx. x * 9/5 + 32))
  (conf converted)))  ; Should be 0.9 (confidence preserved)
```

### 6.2 Evidence is Affine

Example showing evidence consumption:
```
(let ev (evidence "sensor1")
 (let b1 (use ev)
  (let b2 (use ev)  ; Error: ev already consumed
   ...)))
```

Note: The current formalization doesn't have explicit affine evidence in the syntax. This may need to be added or demonstrated at the semantic level.

### 6.3 Introspection is Safe

Example:
```
(let b (belief "hello" 0.8)
 (let i (introspect b)  ; Creates meta-belief at level 1
  (conf i)))  ; Should be 0.64 (Löb discount: 0.8²)
```

Key: Nested introspection decreases confidence: 0.8 → 0.64 → 0.4096 → ...

### 6.4 Defeat Works

Example:
```
(let b (belief "rain" 0.8)
 (let d (belief "dry ground" 0.7)  ; Undercutter
  (let defeated (undercut b d)
   (conf defeated))))  ; Should be 0.8 × (1-0.7) = 0.24
```

### 6.5 Type Checking is Decidable

The type checker should always terminate with a type or an error. This is guaranteed by the structure of `HasType` (inductive relation with decreasing term size).

---

## 7. Implementation Plan

### Phase 1: Complete Core Semantics

1. Finish substitution (`Subst.lean`)
2. Complete Step relation with all reduction rules
3. Prove/provide Step determinism (optional but good)

### Phase 2: Add Parser and Driver

1. S-expression parser for Expr
2. REPL loop
3. Error reporting

### Phase 3: Demonstration Examples

1. Create example programs showing each property
2. Document expected outputs
3. Automated test runner

### Phase 4: Integration

1. Add `Main.lean` entry point
2. Configure `lakefile.lean` for executable
3. Build and test

---

## 8. Philosophical Reflection

### 8.1 What Does "Extract" Mean Here?

In Coq, "extraction" produces OCaml/Haskell/Scheme code from proofs. In Lean 4, we compile to native code directly.

The spirit of Task 8.4 is: **Produce a runnable artifact from the formalization.**

This is achievable by:
1. Completing the executable parts of the formalization
2. Adding a driver
3. Compiling

### 8.2 The Gap Between Spec and Implementation

The Lean formalization is a *specification*. It defines what CLAIR means. The interpreter is an *implementation* of that specification.

The key insight: In dependent type theory, the specification can *be* the implementation if we:
- Use `partial` where termination is hard
- Avoid `sorry` in executable paths
- Provide concrete values (not just proofs)

### 8.3 Why This Matters

If we can produce a working interpreter from the formalization, we demonstrate that:
1. The formalization is complete enough to be executable
2. CLAIR is not just theory—it can run
3. The five key properties are implementable

This is the final proof that CLAIR could work as an LLM lingua franca.

---

## 9. Connection to Prior Work

### 9.1 CompCert

CompCert (Leroy et al.) extracts a verified C compiler from Coq. The approach:
- Specify semantics in Coq
- Write algorithms in Coq's computational fragment
- Extract to OCaml
- Run

CLAIR follows a similar pattern but in Lean 4.

### 9.2 CakeML

CakeML (Kumar et al.) is a verified ML implementation:
- Specify ML semantics
- Implement compiler in HOL4
- Produce verified machine code

CLAIR is simpler: we're producing an interpreter, not a compiler.

### 9.3 Idris

Idris 2 (Brady) compiles to Scheme/Chef. The philosophy:
- Types guide development
- Full dependent types
- Compilation to efficient code

CLAIR shares the "types first" philosophy but targets epistemic reasoning.

---

## 10. Conclusion and Next Steps

### 10.1 What Task 8.4 Actually Requires

Not "extraction" in the Coq sense, but "compilation" of the Lean 4 formalization with:
1. Complete semantics
2. Parser/driver
3. Demonstration examples

### 10.2 Estimated Work

- Complete Step relation: ~200 lines
- Finish substitution: ~50 lines (remove sorrys)
- Parser: ~150 lines
- Driver/REPL: ~100 lines
- Examples: ~200 lines
- **Total**: ~700 lines

### 10.3 Success Criteria

The task is complete when:
1. `lake build` produces an executable
2. Running `./clair` starts a REPL
3. Example programs demonstrate all five properties
4. Documentation explains how to use it

### 10.4 The Meta-Question

Does producing this interpreter "prove" CLAIR works as an LLM lingua franca?

**Claim**: It proves CLAIR *could* work. It demonstrates:
- The epistemic constructs are implementable
- Confidence tracking is computable
- Stratification prevents paradox
- The system runs

**Limitation**: It doesn't prove CLAIR *should* be used, or that LLMs *would* benefit from it. That's an empirical question for future work.

**Confidence**: 0.85 that completing Task 8.4 demonstrates CLAIR's viability as a formalism.

---

## 11. Open Questions

1. Should the interpreter support the full stratified type system, or just the core Belief type?
2. How should we handle the non-computable `rebut` (uses real division)?
3. Should we add pretty-printing for values?
4. How do we demonstrate "affine evidence" without explicit syntax for evidence variables?

---

**Next Action**: Complete the Step relation and add Main.lean for the interpreter driver.
