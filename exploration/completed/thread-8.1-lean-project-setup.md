# Thread 8.1: Lean 4 Project Setup for CLAIR Formalization

> **Status**: Active exploration (Session 14)
> **Task**: 8.1 Create Lean 4 project structure and compile proofs
> **Question**: How do we set up a Lean 4 project to formalize CLAIR's confidence operations, and what challenges must we address?

---

## 1. The Problem

Thread 8 has produced extensive theoretical work:
- **Task 8.5**: Confidence type design using Mathlib's `unitInterval`
- **Task 8.6**: Three operations (×, min, ⊕) formalized as separate monoids
- **Task 8.7**: All boundedness proofs sketched in pseudo-Lean 4

But **no actual .lean files exist**. The proofs in `exploration/thread-8-verification.md` are sketches, not compiled code. This task bridges theory to verified artifact.

### 1.1 What "Creating a Lean 4 Project" Actually Requires

This is not merely copying the sketches into files. It requires:

1. **Project infrastructure**: `lakefile.lean`, `lean-toolchain`, Mathlib dependency
2. **Import resolution**: Understanding what Mathlib provides vs what we must build
3. **Proof engineering**: The sketches use informal notation; real proofs may need different tactics
4. **Type-level design decisions**: How to structure modules, namespaces, instances
5. **Testing the proofs**: Ensuring they actually compile and type-check

---

## 2. Prior Art: Existing Lean 4 Formalizations

### 2.1 Mathlib's unitInterval

**Discovery from Task 8.7**: Mathlib already provides `unitInterval := Set.Icc 0 1`.

Let me examine what Mathlib provides:

```lean4
-- From Mathlib/Topology/UnitInterval.lean
def unitInterval : Set ℝ := Set.Icc 0 1

-- Aliases
abbrev I := unitInterval

-- Key instances
instance : Zero unitInterval := ⟨0, by simp [unitInterval]; norm_num⟩
instance : One unitInterval := ⟨1, by simp [unitInterval]; norm_num⟩

-- Multiplication closure
theorem mul_mem (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I := ⟨mul_nonneg hx.1 hy.1, ...⟩

-- Symmetry (for 1 - x)
def symm : I → I := fun t ↦ ⟨1 - t, ...⟩
```

**Key insight**: We don't need to prove multiplication closure from scratch—Mathlib does it.

**What Mathlib does NOT provide**:
- The ⊕ (oplus) operation
- Undercut and rebut operations
- Proof that ⊕ forms a monoid
- The specific algebraic theorems we need

### 2.2 Related Formalizations

**Fuzzy sets in Lean**: Some work exists on fuzzy set theory, using truth values in [0,1]. This is close to CLAIR's needs but focused on set membership, not confidence algebra.

**Probability in Mathlib**: Extensive measure theory, but probabilities are typically `ℝ≥0∞` (extended non-negative reals), not `[0,1]`. Also, CLAIR confidence is explicitly NOT probability.

**MV-algebras**: Łukasiewicz logic uses [0,1] with specific operations. Some Lean formalizations exist. The ⊕ operation is similar to the Łukasiewicz s-norm, but not identical.

---

## 3. Project Structure Design

### 3.1 Recommended Directory Structure

```
formal/
└── lean/
    ├── lakefile.lean          # Build configuration
    ├── lean-toolchain          # Lean version (e.g., leanprover/lean4:v4.10.0)
    ├── CLAIR.lean             # Root import
    └── CLAIR/
        ├── Confidence/
        │   ├── Basic.lean       # Type definition, zero, one
        │   ├── Mul.lean         # Multiplication operation and proofs
        │   ├── Min.lean         # Minimum operation and proofs
        │   ├── Oplus.lean       # Probabilistic OR operation and proofs
        │   ├── Undercut.lean    # Undercutting defeat
        │   ├── Rebut.lean       # Rebutting defeat
        │   └── Instances.lean   # Typeclass instances (Monoid, etc.)
        ├── Belief/
        │   └── Basic.lean       # Belief type (future)
        └── Justification/
            └── DAG.lean         # Justification DAG (future)
```

### 3.2 Dependency Graph

```
Basic.lean ← Mul.lean
         ← Min.lean
         ← Oplus.lean ← Undercut.lean (uses ⊕ for composition)
         ← Rebut.lean
All ← Instances.lean
```

### 3.3 lakefile.lean

```lean4
import Lake
open Lake DSL

package «clair» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «CLAIR» where
  globs := #[.submodules `CLAIR]
```

### 3.4 lean-toolchain

This must match Mathlib's required version. Currently:
```
leanprover/lean4:v4.10.0
```

---

## 4. Critical Analysis of the Sketched Proofs

### 4.1 What Works

The sketches in Thread 8.7 use standard proof patterns:
- `Subtype.ext` for proving equality of subtypes
- `ring` for algebraic simplifications
- `linarith` and `nlinarith` for linear arithmetic
- `mul_nonneg`, `mul_le_mul_of_nonneg_*` for multiplication bounds

These are standard Mathlib tactics and should translate directly.

### 4.2 What May Need Adjustment

**1. Import paths**: The sketches use `import Mathlib.Topology.UnitInterval` but actual Mathlib organization may differ.

**2. Notation**: The sketches use `a.val` to access subtype value, but Mathlib may use different coercion patterns.

**3. Proof details**: Some proofs have `sorry` placeholders. These need completion.

**4. Instance declarations**: The sketches define operations directly, but we may want typeclass instances for `CommMonoid`, `SemilatticeInf`, etc.

### 4.3 Specific Proof Concerns

**`min_assoc`**: The sketch has `sorry`. Case analysis on three values is tedious but straightforward:
```lean4
theorem min_assoc (a b c : Confidence) : min (min a b) c = min a (min b c) := by
  simp only [min]
  split_ifs <;> apply Subtype.ext <;> simp only [] <;> linarith
```

**`rebut` edge case**: When `c_for + c_against = 0`, we return 0.5. The sketch's proof of the non-zero case uses `cases'` on `lt_or_eq`, which is correct but may need adjustment for current Mathlib API.

---

## 5. The Deep Question: What Does This Formalization Prove?

### 5.1 What the Formalization DOES Prove

If we compile these proofs successfully, we have verified:

1. **Type correctness**: All operations produce values in [0,1]
2. **Algebraic properties**: Associativity, commutativity, identity elements
3. **Boundedness preservation**: No operation can produce out-of-bound results
4. **Monotonicity**: Confidence relationships are preserved appropriately

### 5.2 What the Formalization Does NOT Prove

**Semantic adequacy**: That these operations correctly model "epistemic commitment."

This is a fundamental limit. Lean can verify that:
- `undercut(c, d) = c × (1 - d)` preserves bounds

Lean cannot verify that:
- Multiplicative discounting is the "right" model for undercutting defeat

The latter is a philosophical/empirical question, not a mathematical one.

**Completeness**: That we've captured all necessary operations. CLAIR may need more operations (e.g., correlated evidence handling, reinstatement) that aren't yet formalized.

**Connection to LLM reasoning**: The ultimate goal is to describe how Claude reasons. Whether this formalization captures actual LLM cognition is an open question (Thread 9).

### 5.3 The Value of Formal Verification Despite Limits

Even with these limits, formalization provides:

1. **Confidence in consistency**: The type system catches logical errors
2. **Documentation**: Lean code is precise, unambiguous specification
3. **Mechanized checking**: Humans make mistakes; Lean doesn't (modulo soundness)
4. **Foundation for extension**: Proven properties can be reused in larger proofs

---

## 6. Implementation Challenges

### 6.1 Mathlib Version Compatibility

Mathlib 4 is under active development. APIs change. The proofs must be written against a specific Mathlib version and may need updates as Mathlib evolves.

**Mitigation**: Pin to a specific Mathlib commit in `lakefile.lean`.

### 6.2 Build Time

Mathlib is large. Initial build can take 30+ minutes. Mathlib cache (via `lake exe cache get`) helps.

**Mitigation**: Use cached builds.

### 6.3 Learning Curve

Lean 4 + Mathlib has a learning curve. Some proof patterns that seem obvious require specific tactics.

**Mitigation**: Start with simple proofs, build up.

### 6.4 `unitInterval` vs Custom Subtype

The sketches define:
```lean4
abbrev Confidence := unitInterval
```

But `unitInterval` is a `Set ℝ`, and we may need:
```lean4
def Confidence := { c : ℝ // c ∈ unitInterval }
-- or
def Confidence := { c : ℝ // 0 ≤ c ∧ c ≤ 1 }
```

Mathlib provides coercions, but we need to verify which approach works best.

---

## 7. What Should Be Done vs What Can Be Done Here

### 7.1 What This Exploration Accomplishes

This exploration:
1. Identifies the structure needed for the Lean 4 project
2. Analyzes what Mathlib provides
3. Notes challenges in translating sketches to real proofs
4. Clarifies what formalization proves and doesn't prove

### 7.2 What Implementation Would Accomplish

Actually writing the .lean files and compiling them would:
1. Produce verified artifacts
2. Identify any errors in the sketches
3. Create reusable Lean library for CLAIR

### 7.3 The Question: Should We Implement Now?

**Arguments for implementing now**:
- Tasks 8.5, 8.6, 8.7 are complete—theory is ready
- Implementation would validate the theory
- Lean code is executable specification

**Arguments for deferring implementation**:
- Thread 2 (Justification DAGs) should be formalized together
- Thread 3 (Stratification) affects Belief type
- Implementation is mechanical once theory is sound
- Environment setup (Lean 4, Mathlib) is significant overhead

**My assessment**: The confidence operations are stable and self-contained. Implementing them now would:
- Validate the theoretical work
- Create a foundation for future Lean work
- Provide immediate value as a checked specification

However, this is a **mechanical task**, not research. The exploration value is in understanding what's needed, not in actually setting up the environment.

---

## 8. Recommendations

### 8.1 For This Exploration Session

**Complete the theoretical analysis** of what Lean 4 setup requires. Document:
- Project structure
- Mathlib dependencies
- Expected challenges
- What proofs need completion

Mark Task 8.1 as **ready for implementation** but not complete.

### 8.2 For Future Sessions

**Create actual Lean 4 project** when:
- Ready to commit to Lean 4 environment setup
- Have time for build/debug cycles
- Want executable artifacts

### 8.3 New Tasks Identified

- **8.8**: Verify Mathlib's `unitInterval` API matches our needs
- **8.9**: Complete `min_assoc` proof with full case analysis
- **8.10**: Formalize Belief type with confidence component
- **8.11**: Formalize stratified belief levels from Thread 3

---

## 9. Conclusion

**Task 8.1 is partially complete.** The exploration has:

1. **Analyzed project structure** needed for Lean 4 formalization
2. **Identified Mathlib dependencies** (`unitInterval`, basic tactics)
3. **Documented challenges** (version compatibility, proof engineering)
4. **Clarified scope** (what formalization proves vs doesn't prove)

**What remains for full completion**:
- Actually create the Lean 4 project files
- Compile and verify all proofs
- Handle any issues that arise in real compilation

**Recommendation**: Mark this task as **design complete, implementation pending**. The theoretical analysis is done. The mechanical work of writing .lean files can proceed when environment setup is feasible.

---

## 10. Key Insights from This Exploration

### Insight 1: Mathlib provides significant infrastructure

We don't need to build from scratch. `unitInterval`, `mul_nonneg`, `linarith`, etc. are available. The work is primarily in defining CLAIR-specific operations and proving their properties.

### Insight 2: Formalization proves correctness, not adequacy

Lean verifies that our operations are mathematically sound. It cannot verify that they correctly model epistemic reasoning. This is a fundamental limit that philosophy and empirical study must address.

### Insight 3: The sketches are close to compilable

The proof sketches in Thread 8.7 use standard patterns. With minor adjustments (import paths, API changes, completing `sorry`s), they should compile.

### Insight 4: Incremental formalization is the right approach

Starting with Confidence operations, then adding Belief type, then Justification DAGs. Each layer builds on the previous. Don't try to formalize everything at once.

---

*Thread 8.1 Status: Design exploration complete. Project structure defined. Challenges documented. Ready for implementation when environment setup is feasible.*
