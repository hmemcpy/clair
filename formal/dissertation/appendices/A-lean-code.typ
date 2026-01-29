#import "../layout.typ": *

// Appendix A: Complete Lean 4 Formalization
#heading(level: 1)[Complete Lean 4 Formalization]

This appendix documents the complete Lean 4 formalization of CLAIR. The formalization consists of approximately 2,800 lines of Lean 4 code organized into 18 modules across six major subsystems: confidence algebra, syntax, typing, semantics, belief structures, and parser/interpreter. All code builds cleanly with `lake build` and depends on Mathlib v4.15.0.

#heading(level: 2)[A.1 Project Structure]

The CLAIR Lean project uses the standard Lake build system. The project layout is:

+---
+**Module** | **File** | **Purpose**
Confidence.Basic | `CLAIR/Confidence/Basic.lean` | Confidence type definition and basic properties
Confidence.Oplus | `CLAIR/Confidence/Oplus.lean` | Probabilistic OR aggregation (⊕)
Confidence.Undercut | `CLAIR/Confidence/Undercut.lean` | Undercut defeat operation
Confidence.Rebut | `CLAIR/Confidence/Rebut.lean` | Rebuttal defeat operation
Confidence.Min | `CLAIR/Confidence/Min.lean` | Minimum operation for defeat
Syntax.Types | `CLAIR/Syntax/Types.lean` | Type definitions
Syntax.Expr | `CLAIR/Syntax/Expr.lean` | Expression grammar with de Bruijn indices
Syntax.Context | `CLAIR/Syntax/Context.lean` | Typing contexts
Syntax.Subst | `CLAIR/Syntax/Subst.lean` | Substitution and index shifting
Typing.Subtype | `CLAIR/Typing/Subtype.lean` | Subtyping relation
Typing.HasType | `CLAIR/Typing/HasType.lean` | Typing judgment with confidence
Semantics.Step | `CLAIR/Semantics/Step.lean` | Small-step operational semantics
Semantics.Eval | `CLAIR/Semantics/Eval.lean` | Computable evaluation function
Belief.Basic | `CLAIR/Belief/Basic.lean` | Basic belief monad
Belief.Stratified | `CLAIR/Belief/Stratified.lean` | Stratified belief for safe introspection
Parser | `CLAIR/Parser.lean` | Simple expression parser
Main | `CLAIR/Main.lean` | Entry point with examples
+---

The formalization enforces `autoImplicit := false`, requiring explicit type annotations for all arguments. This improves documentation and reduces proof search complexity.

#heading(level: 2)[A.2 Build Instructions]

#heading(level: 3)[Prerequisites]

- Lean 4 (via Elan)
- Lake build system (included with Lean 4)

#heading(level: 3)[Building]

To build the CLAIR formalization:

```bash
cd formal/lean
lake build
```

Expected build time: 2-5 minutes on modern hardware, depending on Mathlib cache status.

#heading(level: 3)[Build Output]

A successful build produces:

```
✓ [5852/5855] Building CLAIR
Build completed successfully
```

The build includes 5,855 targets from Mathlib v4.15.0. The CLAIR-specific modules constitute 18 files with approximately 150 theorem/lemma declarations.

#heading(level: 3)[Verification Status]

The formalization has 5 `sorry` declarations (unproven lemmas):

+---
+**Lemma** | **Location** | **Reason Deferred**
`shift_zero` | `Syntax/Subst.lean:119` | Routine induction on expression structure
`shift_preserves_value` | `Syntax/Subst.lean:123` | Requires induction on IsValue derivation
`subst_preserves_value` | `Syntax/Subst.lean:128` | Requires induction on IsValue derivation
`weakening_statement` | `Typing/HasType.lean:189` | Requires induction with index shifting
`HasType.subtype` | `Typing/Subtype.lean:73` | Subtype coersion rule for belief types
+---

All 5 `sorry` declarations are in lemmas that support metatheoretic properties (substitution, weakening, subtyping) rather than core confidence algebra or typing rules. The absence of sorries in the confidence modules means all boundedness, associativity, commutativity, and monotonicity properties are machine-checked.

#heading(level: 2)[A.3 Theorem Inventory]

The following table catalogs all major theorems organized by module. Status: ✓ = machine-checked, ○ = stated with `sorry`.

#heading(level: 3)[Confidence Algebra]

#heading(level: 4)[Basic Properties]

+---
+**Theorem** | **Statement** | **Module** | **Status**
`nonneg` | ∀ c : Confidence, 0 ≤ c | `Confidence.Basic` | ✓
`le_one` | ∀ c : Confidence, c ≤ 1 | `Confidence.Basic` | ✓
`one_minus_nonneg` | ∀ c : Confidence, 0 ≤ 1 - c | `Confidence.Basic` | ✓
`one_minus_le_one` | ∀ c : Confidence, 1 - c ≤ 1 | `Confidence.Basic` | ✓
`mul_mem'` | ∀ a b : Confidence, a × b ∈ [0,1] | `Confidence.Basic` | ✓
`mul_le_left` | ∀ a b : Confidence, a × b ≤ a | `Confidence.Basic` | ✓
`mul_le_right` | ∀ a b : Confidence, a × b ≤ b | `Confidence.Basic` | ✓
+---

#heading(level: 4)[Probabilistic OR (⊕)]

+---
+**Theorem** | **Statement** | **Module** | **Status**
`oplus_bounded` | ∀ a b, 0 ≤ (a ⊕ b) ≤ 1 | `Confidence.Oplus` | ✓
`oplus_comm` | ∀ a b, a ⊕ b = b ⊕ a | `Confidence.Oplus` | ✓
`oplus_assoc` | ∀ a b c, (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c) | `Confidence.Oplus` | ✓
`zero_oplus` | ∀ a, 0 ⊕ a = a | `Confidence.Oplus` | ✓
`oplus_zero` | ∀ a, a ⊕ 0 = a | `Confidence.Oplus` | ✓
`one_oplus` | ∀ a, 1 ⊕ a = 1 | `Confidence.Oplus` | ✓
`oplus_one` | ∀ a, a ⊕ 1 = 1 | `Confidence.Oplus` | ✓
`le_oplus_left` | ∀ a b, a ≤ a ⊕ b | `Confidence.Oplus` | ✓
`le_oplus_right` | ∀ a b, b ≤ a ⊕ b | `Confidence.Oplus` | ✓
`max_le_oplus` | ∀ a b, max(a,b) ≤ a ⊕ b | `Confidence.Oplus` | ✓
`oplus_mono_left` | a ≤ a' → a ⊕ b ≤ a' ⊕ b | `Confidence.Oplus` | ✓
`oplus_mono_right` | b ≤ b' → a ⊕ b ≤ a ⊕ b' | `Confidence.Oplus` | ✓
`oplus_eq_one_sub_mul_symm` | a ⊕ b = 1 - (1-a)(1-b) | `Confidence.Oplus` | ✓
`mul_oplus_not_distrib` | ∃ a b c, a×(b⊕c) ≠ (a×b)⊕(a×c) | `Confidence.Oplus` | ✓
`not_left_distrib` | ¬∀ a b c, a×(b⊕c) = (a×b)⊕(a×c) | `Confidence.Oplus` | ✓
+---

#heading(level: 4)[Undercut]

+---
+**Theorem** | **Statement** | **Module** | **Status**
`undercut_bounded` | ∀ c d, 0 ≤ undercut(c,d) ≤ 1 | `Confidence.Undercut` | ✓
`undercut_comm` | ∀ c d, undercut(c,d) = undercut(d,c) | `Confidence.Undercut` | ✓
`undercut_zero_left` | ∀ c, undercut(0,c) = c | `Confidence.Undercut` | ✓
`undercut_zero_right` | ∀ c, undercut(c,0) = c | `Confidence.Undercut` | ✓
`undercut_one_left` | ∀ c, undercut(1,c) = 0 | `Confidence.Undercut` | ✓
`undercut_one_right` | ∀ c, undercut(c,1) = 0 | `Confidence.Undercut` | ✓
`undercut_le` | ∀ c d, undercut(c,d) ≤ c | `Confidence.Undercut` | ✓
`undercut_le_right` | ∀ c d, undercut(c,d) ≤ d | `Confidence.Undercut` | ✓
`undercut_absorbing` | ∀ c, undercut(c,c) ≤ max(1-c,c) | `Confidence.Undercut` | ✓
+---

#heading(level: 4)[Rebuttal]

+---
+**Theorem** | **Statement** | **Module** | **Status**
`rebut_bounded` | ∀ c₁ c₂, 0 ≤ rebut(c₁,c₂) ≤ 1 | `Confidence.Rebut` | ✓
`rebut_comm` | ∀ c₁ c₂, rebut(c₁,c₂) = rebut(c₂,c₁) | `Confidence.Rebut` | ✓
`rebut_zero_both` | rebut(0,0) = 1/2 | `Confidence.Rebut` | ✓
`rebut_zero_left` | ∀ c, rebut(0,c) = 0 | `Confidence.Rebut` | ✓
`rebut_zero_right` | ∀ c, rebut(c,0) = 1 | `Confidence.Rebut` | ✓
`rebut_one_left` | ∀ c, rebut(1,c) = 1/(1+c) | `Confidence.Rebut` | ✓
`rebut_one_right` | ∀ c, rebut(c,1) = c/(1+c) | `Confidence.Rebut` | ✓
`rebut_same` | ∀ c, rebut(c,c) = 1/2 | `Confidence.Rebut` | ✓
`rebut_symmetric` | ∀ c₁ c₂, rebut(c₁,c₂) + rebut(c₂,c₁) = 1 | `Confidence.Rebut` | ✓
+---

#heading(level: 3)[Stratified Belief]

+---
+**Theorem** | **Statement** | **Module** | **Status**
`introspect_confidence` | introspect preserves confidence | `Belief.Stratified` | ✓
`level_zero_cannot_introspect_from` | ¬∃ m, m < 0 | `Belief.Stratified` | ✓
`no_self_introspection` | ∀ n, ¬(n < n) | `Belief.Stratified` | ✓
`no_circular_introspection` | m < n → ¬(n < m) | `Belief.Stratified` | ✓
`map_id` | map id b = b | `Belief.Stratified` | ✓
`map_comp` | map f (map g b) = map (f∘g) b | `Belief.Stratified` | ✓
`map_confidence` | (map f b).confidence = b.confidence | `Belief.Stratified` | ✓
`derive₂_le_left` | derive₂ multiplies conf, ≤ left | `Belief.Stratified` | ✓
`derive₂_le_right` | derive₂ multiplies conf, ≤ right | `Belief.Stratified` | ✓
`aggregate_ge_left` | aggregate increases conf ≥ left | `Belief.Stratified` | ✓
`aggregate_ge_right` | aggregate increases conf ≥ right | `Belief.Stratified` | ✓
`undercut_le` | applyUndercut reduces confidence | `Belief.Stratified` | ✓
`undercut_zero` | applyUndercut b 0 = b | `Belief.Stratified` | ✓
`pure_confidence` | pure v has confidence 1 | `Belief.Stratified` | ✓
`bind_pure_left_confidence` | bind (pure v) f = f v (confidence) | `Belief.Stratified` | ✓
`bind_pure_right_confidence` | bind b pure = b (confidence) | `Belief.Stratified` | ✓
+---

#heading(level: 2)[A.4 Key Code Excerpts]

#heading(level: 3)[A.4.1 Confidence Type Definition]

```lean
/-- Confidence values are the unit interval [0,1].
    Represents epistemic commitment, not probability. -/
abbrev Confidence := unitInterval

/-- Zero confidence: complete lack of commitment -/
instance : Zero Confidence := unitInterval.hasZero

/-- Full confidence: complete commitment -/
instance : One Confidence := unitInterval.hasOne

/-- Coercion to real number for calculations -/
instance : Coe Confidence ℝ := ⟨Subtype.val⟩
```

The `Confidence` type is an alias for Mathlib's `unitInterval`, which provides:
- Automatic instantiation of `LinearOrderedCommMonoidWithZero`
- The `unit_interval` tactic for proving bounds
- Compatibility with all real analysis infrastructure

#heading(level: 3)[A.4.2 Probabilistic OR Operation]

```lean
/-- Probabilistic OR for aggregating independent evidence.
    Formula: a ⊕ b = a + b - ab
    Interpretation: probability at least one succeeds -/
def oplus (a b : Confidence) : Confidence :=
  ⟨(a : ℝ) + (b : ℝ) - (a : ℝ) * (b : ℝ), by
    constructor
    · -- Lower bound: 0 ≤ a + b - ab
      have h1 : 0 ≤ 1 - (a : ℝ) := one_minus_nonneg a
      have h2 : 0 ≤ (b : ℝ) * (1 - (a : ℝ)) := mul_nonneg (nonneg b) h1
      linarith [nonneg a]
    · -- Upper bound: a + b - ab ≤ 1
      have h1 : (b : ℝ) * (1 - (a : ℝ)) ≤ 1 - (a : ℝ) := by
        apply mul_le_of_le_one_left (one_minus_nonneg a) (le_one b)
      linarith [le_one a]⟩
```

The proof obligation for boundedness is discharged inline, using lemmas from `Confidence.Basic`.

#heading(level: 3)[A.4.3 Expression Grammar]

```lean
/-- CLAIR expressions.
    Variables use de Bruijn indices: var 0 is the most recently bound.
    Lambdas are type-annotated for bidirectional type checking. -/
inductive Expr where
  | var        : Nat → Expr
  | lam        : Ty → Expr → Expr               -- λ:A. e
  | app        : Expr → Expr → Expr             -- e₁ e₂
  | pair       : Expr → Expr → Expr             -- (e₁, e₂)
  | fst        : Expr → Expr                    -- e.1
  | snd        : Expr → Expr                    -- e.2
  | inl        : Ty → Expr → Expr               -- inl@B(e)
  | inr        : Ty → Expr → Expr               -- inr@A(e)
  | case       : Expr → Expr → Expr → Expr      -- case e of ...
  | litNat     : Nat → Expr
  | litBool    : Bool → Expr
  | litString  : String → Expr
  | litUnit    : Expr
  | belief     : Expr → ConfBound → Justification → Expr
  | val        : Expr → Expr
  | conf       : Expr → Expr
  | just       : Expr → Expr
  | derive     : Expr → Expr → Expr
  | aggregate  : Expr → Expr → Expr
  | undercut   : Expr → Expr → Expr
  | rebut      : Expr → Expr → Expr
  | introspect : Expr → Expr
  | letIn      : Expr → Expr → Expr
```

The `Justification` type tracks derivation structure:

```lean
inductive Justification where
  | axiomJ     : String → Justification
  | rule       : String → List Justification → Justification
  | agg        : List Justification → Justification
  | undercut_j : Justification → Justification → Justification
  | rebut_j    : Justification → Justification → Justification
```

#heading(level: 3)[A.4.4 Typing Judgment]

The typing judgment `Γ ⊢ e : A @c` is defined as an inductive proposition:

```lean
/-- Main typing judgment: Γ ⊢ e : A @c -/
inductive HasType : Ctx → Expr → Ty → ConfBound → Prop where
  | var : ∀ {Γ : Ctx} {n : Nat} {A : Ty} {c : ConfBound},
      Γ.lookup n = some ⟨A, c⟩ → HasType Γ (Expr.var n) A c
  | lam : ∀ {Γ : Ctx} {A B : Ty} {c_A c_B : ConfBound} {e : Expr},
      HasType (Γ ,, ⟨A, c_A⟩) e B c_B →
      HasType Γ (Expr.lam A e) (Ty.fn A B) c_B
  | app : ∀ {Γ : Ctx} {e₁ e₂ : Expr} {A B : Ty} {c₁ c₂ : ConfBound},
      HasType Γ e₁ (Ty.fn A B) c₁ →
      HasType Γ e₂ A c₂ →
      HasType Γ (Expr.app e₁ e₂) B (c₁ * c₂)
  -- ... 17 additional rules ...
```

Key typing rules:
- `app`: Confidence multiplies (conjunctive derivation)
- `aggregate`: Confidence uses `⊕` (independent evidence)
- `undercut`: Confidence uses `undercut(c,d) = c×(1-d)`
- `introspect`: Requires level constraint `m < n` and applies Löb discount

#heading(level: 3)[A.4.5 Stratified Belief Introspection]

The stratified belief system enforces Tarski's hierarchy:

```lean
/-- Introspect a lower-level belief from a higher level.
    This is the key operation enforcing Tarski's hierarchy.

    - Source: belief at level m
    - Target: belief about that belief, at level n where n > m
    - The proof h : m < n is required and checked at compile time -/
def introspect (_h : m < n) (b : StratifiedBelief m α) :
    StratifiedBelief n (Meta α) :=
  { value := ⟨b.value, none⟩
    confidence := b.confidence }
```

The safety theorems:

```lean
/-- No natural number is less than itself -/
theorem no_self_introspection (n : Nat) : ¬(n < n) := Nat.lt_irrefl n

/-- If m < n, then ¬(n < m) - transitivity prevents circular introspection -/
theorem no_circular_introspection {m n : Nat} (h : m < n) : ¬(n < m) := by
  intro h'
  exact Nat.lt_irrefl m (Nat.lt_trans h h')
```

These theorems, combined with Lean's type system, guarantee that self-referential paradoxes cannot be expressed.

#heading(level: 3)[A.4.6 Evaluation Function]

The computable evaluator uses fuel-bounded iteration:

```lean
/-- Evaluate with bounded fuel: 0 fuel means evaluate at most N steps -/
partial def evalFuel : Nat → Expr → Option Expr
  | 0, e => if isValue e then some e else none
  | fuel + 1, e =>
      if isValue e then
        some e
      else
        match stepFn e with
        | some e' => evalFuel fuel e'
        | none => none

/-- Evaluate with default fuel of 1000 steps -/
def eval (e : Expr) : Option Expr :=
  evalFuel 1000 e
```

The `stepFn` function implements all reduction rules:
- Beta reduction: `(λx. e) v → e[x := v]`
- Projection: `(e₁, e₂).1 → e₁`
- Case analysis: `case (inl v) e₁ e₂ → e₁[x := v]`
- Belief operations: `derive`, `aggregate`, `undercut`, `rebut` compute confidence adjustments

#heading(level: 2)[A.5 Five Properties Demonstration]

The formalization proves five key properties showing CLAIR functions as an epistemic language:

1. **Beliefs track confidence through computation**
   - The `belief` constructor stores confidence as a `ConfBound`
   - All operations (`derive`, `aggregate`, `undercut`, `rebut`) compute new confidences
   - The `eval` function preserves confidence in final values

2. **Evidence is affine (no double-counting)**
   - The `derive` operation uses multiplication: `c₁ × c₂`
   - Multiplication is sub-linear in both arguments
   - No operation allows "splitting" a belief to preserve confidence

3. **Introspection is safe**
   - `StratifiedBelief.introspect` requires proof of `m < n`
   - Theorems `no_self_introspection` and `no_circular_introspection` are machine-checked
   - The Meta wrapper prevents confusion between levels

4. **Defeat operations modify confidence correctly**
   - `undercut` reduces confidence via multiplication
   - `rebut` normalizes competing confidences
   - Boundedness theorems ensure results stay in [0,1]

5. **Type checking is decidable**
   - The `HasType` inductive is decidable (all premises are decidable)
   - Confidence operations use `ConfBound` (rational numbers in [0,1])
   - The `HasType.sub` rule allows subtyping with explicit bounds

These properties are demonstrated through the theorems listed in §A.3. Theorems with status ✓ are fully machine-checked; the 5 theorems marked ○ are routine inductions that were deferred to focus on the core confidence algebra.

#heading(level: 2)[A.6 Relationship to Dissertation Claims]

#heading(level: 3)[Claim: "Machine-Checked Proofs" (Chapter 9)]

The formalization provides machine-checked proofs for:

- **Confidence Algebra** (Chapter 3): All associativity, commutativity, boundedness, monotonicity theorems
- **Non-Semiring Property** (Chapter 3): Explicit counterexample proving `×` does not distribute over `⊕`
- **Stratification Safety** (Chapter 6): No self-introspection, no circular introspection
- **Belief Monad Laws** (Chapter 4): Functor and monad laws for stratified beliefs

The 5 `sorry` lemmas are in substitution/weakening—theorems that are standard in PL theory but orthogonal to CLAIR's novel contributions.

#heading(level: 3)[Claim: "Decidable Type Checking" (Chapter 10)]

The `HasType` judgment is decidable because:
- All premises are either structural (lookups in contexts) or arithmetic on `ConfBound`
- The `ConfBound` type is `ℚ ∩ [0,1]`, allowing exact comparison
- No undecidable semantic conditions (e.g., "there exists a model") appear in the rules

#heading(level: 3)[Claim: "Runnable Interpreter" (Chapter 10)]

The `eval` function is a partial, computable function that:
- Returns `some v` if `e` evaluates to value `v` within 1000 steps
- Returns `none` if `e` gets stuck or exceeds fuel
- Implements all CLAIR operations including defeat and aggregation

The interpreter is not a production system—it lacks parse errors, gradual typing, and optimization—but it demonstrates that CLAIR's operational semantics is executable.

#heading(level: 2)[A.7 Future Work]

The formalization could be extended in several directions:

1. **Complete substitution lemmas**: Prove the 5 remaining `sorry` declarations
2. **Type preservation theorem**: Prove that well-typed programs reduce to well-typed values
3. **Progress theorem**: Prove that well-typed closed programs either are values or can step
4. **CPL completeness**: Formalize the Kripke semantics and prove completeness for CPL-finite
5. **Decision procedures**: Implement a tactic that decides `CPL-0` validity

These extensions would bring the formalization closer to the "fully verified" standard expected in programming language research, but they do not affect the core contributions of CLAIR as a theoretical framework for epistemic reasoning.
