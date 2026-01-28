# Thread 8.4 Deep Dive: Extracting a Working Interpreter from Lean 4

**Status**: Analysis Complete (Session 79)
**Task**: 8.4 Extract interpreter — Produce runnable CLAIR evaluator
**Key Question**: What does completion of Task 8.4 actually entail, and what are the theoretical/practical considerations?

---

## 1. The Core Question

We have a substantial Lean 4 formalization of CLAIR. The question is: what does it mean to "extract" or "produce" a working interpreter from this formalization? And what would it prove about CLAIR's viability?

### 1.1 Two Interpretations of "Extract"

**Interpretation A: Coq-style Extraction**
- Transform proof terms/definitions into executable code in another language (OCaml, Haskell, Scheme)
- Used in CompCert, verified algorithms
- *Not well-supported in Lean 4*

**Interpretation B: Native Compilation**
- Lean 4 compiles directly to C, then to native code
- The formalization *is* the implementation when written computably
- *This is what Lean 4 actually supports*

### 1.2 Key Finding

Lean 4's approach is **not extraction but compilation**. The path to a working interpreter is:

```
Complete Formalization → Add Driver → lake build → Runnable Binary
```

This is philosophically different from Coq extraction:
- **Coq**: Prove → Extract to external language → Run
- **Lean 4**: Write computable definitions → Compile directly → Run

---

## 2. What "Completeness" Means for the Formalization

### 2.1 Current State Analysis

| Component | Status | Executable? | Gaps |
|-----------|--------|-------------|------|
| Confidence.Basic | ✓ Complete | Yes | None |
| Confidence.Oplus | ✓ Complete | Yes | None |
| Confidence.Undercut | ✓ Complete | Yes | None |
| Confidence.Rebut | ✓ Complete | Yes (noncomputable) | Uses `Real` division |
| Confidence.Min | ✓ Complete | Yes | None |
| Belief.Basic | ✓ Complete | Yes | None |
| Belief.Stratified | ✓ Complete | Yes | None |
| Syntax.Types | ✓ Complete | Yes | None |
| Syntax.Expr | ✓ Complete | Yes | None |
| Syntax.Context | ✓ Complete | Yes | None |
| Syntax.Subst | ~90% Complete | Yes | 3 lemmas as `sorry` |
| Typing.Subtype | ~90% Complete | Yes | 1 proof as `sorry` |
| Typing.HasType | ✓ Complete | Yes | Weakening as `sorry` |
| Semantics.Step | ~10% Complete | Partial | Most rules missing |

### 2.2 The Role of `sorry`

In Lean 4, `sorry` in definitions becomes `panic!` at runtime. For proofs, it's a placeholder. The key distinction:

- **Type signatures with `sorry`**: Still generate code, panic if executed
- **Proofs with `sorry`**: Don't affect executability (proofs are erased)

The 3 `sorry`s in `Subst.lean` are **proof lemmas**, not definitions. They don't block execution.

### 2.3 What Must Be Completed

To have a runnable interpreter, we need:

**Essential (blocks execution):**
1. Complete the `Step` inductive with all reduction rules
2. Implement a computable `eval` function (not just relation)
3. Add parser for surface syntax
4. Add `Main.lean` driver

**Optional (proofs only):**
- Substitution lemmas (type safety proofs)
- Weakening theorem (type safety proof)
- Subtype decidability proof

---

## 3. Design Decisions for the Interpreter

### 3.1 Relation vs Function for Semantics

The current `Step` is an **inductive relation** (small-step semantics):

```lean
inductive Step : Expr → Expr → Prop
```

Relations are not executable. We need a **function**:

```lean
def eval : Expr → Option Expr  -- Returns None if stuck/error
```

Or for a full interpreter with state:

```lean
def evalStep (e : Expr) : EvalM Expr
```

### 3.2 Handling Non-Determinism

The `Step` relation is technically non-deterministic (though CLAIR's design makes it deterministic). Options:

1. **Prove determinism**: `Step e e₁ → Step e e₂ → e₁ = e₂`
2. **Use `partial`**: Don't prove termination, just implement
3. **Use fuel**: Bounded evaluation steps

**Recommendation**: Use `partial` with implicit deterministic evaluation order (call-by-value).

### 3.3 The `noncomputable` Issue

`ConfBound.rebut` is marked `noncomputable` because it uses real division on rationals:

```lean
noncomputable def rebut (c_for c_against : ConfBound) : ConfBound :=
  if c_for + c_against = 0 then 1/2
  else c_for / (c_for + c_against)
```

This is **not actually noncomputable** for rationals. The issue is Lean's type class resolution. We can fix this with explicit rational division.

---

## 4. What the Interpreter Would Prove

### 4.1 The Five Key Properties

From `IMPLEMENTATION_PLAN.md`, the interpreter must demonstrate:

| Property | Formalization Status | Interpreter Demonstrates |
|----------|---------------------|-------------------------|
| 1. Beliefs track confidence | ✓ Lean definitions | Evaluating belief expressions shows confidence propagation |
| 2. Evidence is affine | ✓ Session 72-75 design | Type checker enforces linear usage |
| 3. Introspection is safe | ✓ Stratified types | Level constraints enforced at type checking |
| 4. Defeat works | ✓ Undercut/rebut ops | Evaluating defeat expressions modifies confidence correctly |
| 5. Type checking is decidable | ✓ Proven Session 74 | Type checker terminates |

### 4.2 What It Would NOT Prove

- **Correctness**: Without full proofs, we don't know the implementation matches the spec
- **Termination**: `partial` allows non-termination
- **Completeness**: Not all CLAIR features (full stratified reasoning)

### 4.3 The Meta-Claim

Producing a working interpreter demonstrates:

> CLAIR is not just a theoretical construct—it can be implemented and executed.

This is **practical viability**, not **formal verification**.

---

## 5. The Gap Between "Spec" and "Implementation"

### 5.1 The Formalization as Specification

The Lean formalization currently serves as a **mathematical specification**:
- Types define what exists
- Relations define what can happen
- Proofs (where complete) establish properties

### 5.2 The Interpreter as Implementation

A working interpreter is an **operational implementation**:
- Functions compute results
- Side effects (I/O) are possible
- Efficiency matters (somewhat)

### 5.3 The Beautiful Possibility: They Can Be the Same

In dependent type theory, the specification can **be** the implementation:

```lean
-- This is both a definition and executable code
def oplus (a b : ℚ) : ℚ := a + b - a * b

-- Can be run via #eval or compiled
def example : ℚ := oplus (1/2) (1/3)  -- = 2/3
```

The CLAIR formalization is already written in this style. The gap is:
1. `Step` is a relation, not a function
2. No I/O layer (parser, REPL)

---

## 6. Prior Art: Verified Interpreters

### 6.1 CompCert (Leroy et al.)

- **Approach**: Coq proof → extraction to OCaml
- **Result**: Verified C compiler
- **Relevance**: Extraction works, but requires Coq

### 6.2 CakeML (Kumar et al.)

- **Approach**: HOL4 specification → verified machine code
- **Result**: Verified ML implementation
- **Relevance**: Full verification is possible, but massive effort

### 6.3 Idris 2 (Brady)

- **Approach**: Self-hosted, compiles to Scheme/C
- **Result**: Practical dependently-typed language
- **Relevance**: Lean 4 follows similar philosophy

### 6.4 Lean 4 Itself

- **Approach**: Lean 4 compiles to C
- **Result**: Native binaries with proof erasure
- **Relevance**: This is exactly what we'd use

---

## 7. Practical Path to Completion

### 7.1 Option A: Minimal Viable Interpreter (Recommended)

**Scope**: Complete the Lean formalization with a driver

**Steps**:
1. Add remaining `Step` rules (~200 lines)
2. Add computable `eval` function (~100 lines)
3. Add S-expression parser (~150 lines)
4. Add `Main.lean` with REPL (~100 lines)
5. Configure `lakefile.lean` for executable
6. Build and test

**Total**: ~550 lines

**Pros**:
- Single codebase (no duplication)
- Changes to formalization automatically reflected
- Can add proofs incrementally

**Cons**:
- Lean 4 less mature for systems programming
- Parser requires metaprogramming knowledge

### 7.2 Option B: Separate Haskell Interpreter

**Scope**: Implement reference interpreter in Haskell

**Steps**:
1. Create Haskell project
2. Port types and operations (~400 lines)
3. Implement parser (~200 lines)
4. Implement evaluator (~400 lines)
5. Add REPL (~100 lines)

**Total**: ~1100 lines

**Pros**:
- Better tooling for standalone executables
- More accessible to non-Lean users
- Rich library ecosystem

**Cons**:
- Two codebases to maintain
- Risk of divergence from formalization
- No automatic verification

### 7.3 Recommendation

**Option A (Lean 4)** is the right choice because:
1. The formalization is the primary artifact
2. Lean 4's native compilation is production-ready
3. No semantic gap between spec and implementation
4. Demonstrates Lean 4 as a practical programming language

---

## 8. Theoretical Reflections

### 8.1 What Does It Mean for CLAIR to "Work"?

Three levels of "working":

1. **Syntactic**: Programs parse and type-check ✓
2. **Operational**: Programs evaluate to values (interpreter)
3. **Semantic**: Evaluation matches formal semantics (proof)

Task 8.4 achieves level 2.

### 8.2 The Löbian Constraint

From Thread 3: CLAIR cannot prove its own consistency. This applies to the interpreter too:

- The interpreter can run CLAIR programs
- It cannot prove that all CLAIR programs that should terminate do terminate
- We accept `partial` functions / fuel-based evaluation

This is not a bug—it's a fundamental limit.

### 8.3 The Epistemic Status of the Interpreter

If we produce a working interpreter, my confidence in CLAIR's viability increases:

| Claim | Before | After |
|-------|--------|-------|
| CLAIR is implementable | 0.75 | 0.95 |
| Confidence tracking works | 0.80 | 0.90 |
| Stratification prevents paradox | 0.85 | 0.90 |
| Defeat operations are computable | 0.80 | 0.90 |

---

## 9. Conclusion

### 9.1 What Task 8.4 Actually Requires

Not "extraction" in the Coq sense, but **completion and compilation**:

1. **Complete the Step relation** with all reduction rules
2. **Add a computable evaluator** (function, not relation)
3. **Add parser and driver** for interactive use
4. **Compile with `lake build`** to produce binary

### 9.2 The Gap is Smaller Than It Appears

The formalization is ~90% complete for executable purposes:
- Core types: Done
- Confidence operations: Done
- Syntax: Done
- Substitution: Done (lemmas are proofs only)
- Typing: Done (weakening is proof only)
- **Semantics**: Needs completion (~200 lines)
- **Driver**: Needs creation (~250 lines)

### 9.3 What Success Looks Like

```bash
$ lake build
$ ./.lake/build/bin/clair
CLAIR 0.1.0 - Comprehensible LLM AI Intermediate Representation
> (let b (belief 42 0.9)
    (conf b))
0.9
> (let b1 (belief "rain" 0.8)
    (let b2 (belief "wet ground" 0.7)
      (conf (derive b1 b2))))
0.56
```

### 9.4 Final Assessment

Task 8.4 is **ready for implementation**. The design is clear:
- Lean 4 native compilation
- Complete the Step relation
- Add parser and REPL
- Demonstrate five key properties

**Estimated work**: 450-700 lines
**Confidence this proves viability**: 0.85

---

## 10. Connection to Prior Work

### In CLAIR

- **Thread 7.1**: Reference interpreter design (Haskell recommended there; Lean 4 now preferred)
- **Thread 8.x series**: All Lean formalization work
- **Thread 8.12**: Syntax formalization (what we'd implement)

### In Literature

- **Pierce et al.**, "Software Foundations": Coq as programming language
- **Chlipala**, "Certified Programming with Dependent Types": Practical proving
- **de Moura et al.**, "The Lean 4 Theorem Prover": Native compilation approach

---

**Next Action**: Complete the Step relation and add Main.lean for the interpreter driver.

---

*Thread 8.4 Status: Analysis complete. Path forward is clear: complete Step relation, add driver, compile. Lean 4 native compilation replaces Coq-style extraction.*
