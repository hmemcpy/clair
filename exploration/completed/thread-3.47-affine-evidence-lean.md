# Thread 3.47: Affine Evidence Types in Lean

> **Status**: Active exploration (Session 75)
> **Task**: 3.47 Add affine context splitting and usage tracking to Lean typing judgment
> **Question**: How do we formalize affine evidence discipline in the Lean 4 formalization?
> **Prior Work**: Thread 3.46 (epistemic linearity), Thread 3.48 (linearity × defeat), Thread 3.49 (decidability)

---

## 1. The Gap

### 1.1 Current State

The current Lean formalization (`formal/lean/CLAIR/Typing/HasType.lean`) defines:

```lean
inductive HasType : Ctx → Expr → Ty → ConfBound → Prop where
  | var : Γ.lookup n = some ⟨A, c⟩ → HasType Γ (Expr.var n) A c
  | app : HasType Γ e₁ (Ty.fn A B) c₁ → HasType Γ e₂ A c₂ →
          HasType Γ (Expr.app e₁ e₂) B (c₁ * c₂)
  -- ...
```

This uses a **single context** `Γ : Ctx` where `Ctx = List CtxEntry`.

### 1.2 What's Missing

Thread 3.46 established that CLAIR needs **two contexts**:
- **Γ (unrestricted)**: Evidence marked with `!` that can be used any number of times
- **Δ (affine)**: Evidence that can be used at most once

The typing judgment should be:
```
Γ; Δ ⊢ e : A @c
```

With key properties:
1. **Context splitting** for aggregation: `Δ = Δ₁ ⊎ Δ₂` (disjoint union)
2. **Usage tracking** bottom-up: each subexpression reports which affine evidence it uses
3. **Disjointness checking** at aggregation points

### 1.3 The Core Challenge

The challenge is formalizing context splitting in Lean such that:
1. The type system prevents double-counting of affine evidence
2. Resource safety is provable (well-typed terms use each affine resource at most once)
3. The resulting type checking remains decidable (per Thread 3.49)

---

## 2. Design Options

### 2.1 Option A: Two Separate Contexts (Classical Linear Types)

Following Girard's linear logic and Walker's formalization:

```lean
-- Two separate contexts
structure DualCtx where
  unrestricted : Ctx  -- Γ: exponential evidence
  affine : Ctx        -- Δ: linear evidence

-- Extended typing judgment
inductive HasType : DualCtx → Expr → Ty → ConfBound → Prop where
  | var_unrestricted :
      ctx.unrestricted.lookup n = some ⟨A, c⟩ →
      HasType ctx (Expr.var n) A c
  | var_affine :
      ctx.affine.lookup n = some ⟨A, c⟩ →
      HasType { ctx with affine := ctx.affine.remove n } (Expr.var n) A c
  -- ...
```

**Pro**: Direct correspondence to linear logic literature
**Con**: Variable lookup becomes complex; need to track which context

### 2.2 Option B: Single Context with Multiplicity Annotations

Following Atkey's quantitative type theory and Linear Haskell:

```lean
-- Multiplicity annotation
inductive Mult where
  | zero   : Mult  -- Cannot use
  | one    : Mult  -- Use exactly/at most once (affine)
  | omega  : Mult  -- Use any number of times (unrestricted)

-- Context entry with multiplicity
structure CtxEntryWithMult where
  ty   : Ty
  conf : ConfBound
  mult : Mult

-- Single context, multiplicities tracked
abbrev MultCtx := List CtxEntryWithMult

-- Usage: scalar multiplication on contexts
def scaleCtx (m : Mult) (Γ : MultCtx) : MultCtx := ...

-- Splitting: Γ = Γ₁ + Γ₂ where multiplicities add
def splitCtx : MultCtx → MultCtx → MultCtx → Prop := ...
```

**Pro**: More flexible; handles gradations of linearity
**Con**: More complex; addition on multiplicities needs definition

### 2.3 Option C: Output Contexts (Affine Type Checking with Usage Sets)

Following Walker's bidirectional affine type checking:

```lean
-- Typing judgment returns which variables were used
-- Judgment: Γ ⊢ e : A @c ⇝ Used
-- where Used ⊆ dom(Γ) tracks affine variable usage

inductive HasTypeUsed : Ctx → Expr → Ty → ConfBound → Finset Nat → Prop where
  | var :
      Γ.lookup n = some ⟨A, c⟩ →
      HasTypeUsed Γ (Expr.var n) A c {n}
  | app :
      HasTypeUsed Γ e₁ (Ty.fn A B) c₁ U₁ →
      HasTypeUsed Γ e₂ A c₂ U₂ →
      Disjoint U₁ U₂ →  -- Key: affine constraint
      HasTypeUsed Γ (Expr.app e₁ e₂) B (c₁ * c₂) (U₁ ∪ U₂)
  -- ...
```

**Pro**: Simple extension of existing formalization; disjointness explicit
**Con**: All variables tracked uniformly; need separate marking for unrestricted

### 2.4 Option D: Hybrid (Unrestricted + Affine with Usage Sets)

Combining best of both worlds:

```lean
-- Unrestricted context (can always be used)
abbrev UnrestrictedCtx := Ctx

-- Affine context (tracked for usage)
abbrev AffineCtx := Ctx

-- Judgment: Γ; Δ ⊢ e : A @c ⇝ Used
-- where Used ⊆ dom(Δ) tracks which affine evidence was consumed

inductive HasType : UnrestrictedCtx → AffineCtx → Expr → Ty → ConfBound →
                    Finset Nat → Prop where
  | var_unrestricted :
      Γ.lookup n = some ⟨A, c⟩ →
      HasType Γ Δ (Expr.var n) A c ∅  -- No affine usage
  | var_affine :
      Δ.lookup n = some ⟨A, c⟩ →
      HasType Γ Δ (Expr.var n) A c {n}  -- Uses n from Δ
  | aggregate :
      HasType Γ Δ e₁ (Ty.belief A c₁) c_e₁ U₁ →
      HasType Γ Δ e₂ (Ty.belief A c₂) c_e₂ U₂ →
      Disjoint U₁ U₂ →  -- Evidence must be distinct
      HasType Γ Δ (Expr.aggregate e₁ e₂)
              (Ty.belief A (c₁ ⊕ c₂)) (c_e₁ ⊕ c_e₂) (U₁ ∪ U₂)
```

**Pro**: Clean separation; explicit disjointness; extends existing Ctx
**Con**: More parameters in judgment

---

## 3. Recommended Design: Option D (Hybrid)

### 3.1 Rationale

Option D best matches CLAIR's needs:

1. **Matches theory**: Thread 3.46's `Γ; Δ ⊢ e : A @c` maps directly
2. **Explicit disjointness**: The `Disjoint U₁ U₂` premise makes resource safety clear
3. **Minimal changes**: Extends existing `Ctx` type, adds usage tracking
4. **Decidability**: Usage sets are finite, disjointness is decidable (per Thread 3.49)
5. **Proof-friendly**: Resource safety theorem becomes: "all HasType derivations have non-overlapping usage sets at split points"

### 3.2 Key Insight: Usage vs. Consumption

The usage set `U` tracks which affine variables *could* be used by a subterm. At the top level, a term with `HasType Γ Δ e A c U` may leave some of `Δ` unused—this is fine for affine (vs. linear which requires exact use).

The critical property is: **at aggregation points, U₁ and U₂ must be disjoint**, preventing the same evidence from being counted twice.

---

## 4. Detailed Formalization

### 4.1 Extended Context Types

```lean
namespace CLAIR.Syntax

/-- Unrestricted (exponential) context: evidence that can be reused -/
abbrev UnrestrictedCtx := Ctx

/-- Affine context: evidence that can be used at most once -/
abbrev AffineCtx := Ctx

/-- Combined dual context -/
structure DualCtx where
  unrestricted : UnrestrictedCtx  -- Γ: freely reusable
  affine : AffineCtx              -- Δ: use at most once

namespace DualCtx

def empty : DualCtx := ⟨[], []⟩

def extendUnrestricted (ctx : DualCtx) (e : CtxEntry) : DualCtx :=
  { ctx with unrestricted := ctx.unrestricted.extend e }

def extendAffine (ctx : DualCtx) (e : CtxEntry) : DualCtx :=
  { ctx with affine := ctx.affine.extend e }

end DualCtx

end CLAIR.Syntax
```

### 4.2 Usage Sets

```lean
/-- Usage set: which affine variables are used by an expression.
    Represented as a finite set of de Bruijn indices. -/
abbrev UsageSet := Finset Nat

namespace UsageSet

/-- Check if two usage sets are disjoint -/
def disjoint (U₁ U₂ : UsageSet) : Prop := U₁ ∩ U₂ = ∅

instance : DecidablePred₂ disjoint := fun U₁ U₂ =>
  decidable_of_iff (U₁ ∩ U₂ = ∅) Iff.rfl

/-- Combine usage sets (must be disjoint for valid derivation) -/
def combine (U₁ U₂ : UsageSet) : UsageSet := U₁ ∪ U₂

/-- Singleton usage -/
def single (n : Nat) : UsageSet := {n}

/-- Empty usage -/
def empty : UsageSet := ∅

end UsageSet
```

### 4.3 Extended Typing Judgment

```lean
/-- Affine typing judgment with usage tracking.
    Γ; Δ ⊢ e : A @c ⇝ U
    "In unrestricted context Γ and affine context Δ,
     expression e has type A with confidence c,
     using affine evidence U ⊆ dom(Δ)" -/
inductive HasTypeAffine : UnrestrictedCtx → AffineCtx → Expr → Ty → ConfBound →
                          UsageSet → Prop where

  /-! ### Variable Rules -/

  /-- Variable from unrestricted context: no affine usage -/
  | var_unrestricted :
      Γ.lookup n = some ⟨A, c⟩ →
      HasTypeAffine Γ Δ (Expr.var n) A c ∅

  /-- Variable from affine context: marks usage -/
  | var_affine :
      Δ.lookup n = some ⟨A, c⟩ →
      HasTypeAffine Γ Δ (Expr.var n) A c {n}

  /-! ### Lambda Calculus -/

  /-- Lambda with affine parameter -/
  | lam_affine :
      HasTypeAffine Γ (Δ.extend ⟨A, c_A⟩) e B c_B U →
      -- Shift usage set to account for new binding
      HasTypeAffine Γ Δ (Expr.lam A e) (Ty.fn A B) c_B (U.image (· - 1) \ {0})

  /-- Application: must have disjoint usage -/
  | app :
      HasTypeAffine Γ Δ e₁ (Ty.fn A B) c₁ U₁ →
      HasTypeAffine Γ Δ e₂ A c₂ U₂ →
      U₁.disjoint U₂ →
      HasTypeAffine Γ Δ (Expr.app e₁ e₂) B (c₁ * c₂) (U₁ ∪ U₂)

  /-! ### Product Rules -/

  /-- Pair: must have disjoint usage -/
  | pair :
      HasTypeAffine Γ Δ e₁ A c₁ U₁ →
      HasTypeAffine Γ Δ e₂ B c₂ U₂ →
      U₁.disjoint U₂ →
      HasTypeAffine Γ Δ (Expr.pair e₁ e₂) (Ty.prod A B) (c₁ * c₂) (U₁ ∪ U₂)

  /-- First projection: preserves usage -/
  | fst :
      HasTypeAffine Γ Δ e (Ty.prod A B) c U →
      HasTypeAffine Γ Δ (Expr.fst e) A c U

  /-- Second projection: preserves usage -/
  | snd :
      HasTypeAffine Γ Δ e (Ty.prod A B) c U →
      HasTypeAffine Γ Δ (Expr.snd e) B c U

  /-! ### Belief Rules -/

  /-- Belief constructor -/
  | belief :
      HasTypeAffine Γ Δ v A 1 U →
      c_bound ≤ c_actual →
      HasTypeAffine Γ Δ (Expr.belief v c_actual j) (Ty.belief A c_bound) c_bound U

  /-- Value extraction -/
  | val :
      HasTypeAffine Γ Δ e (Ty.belief A c) c_e U →
      HasTypeAffine Γ Δ (Expr.val e) A c_e U

  /-! ### Derivation Rule -/

  /-- Binary derivation: disjoint usage required -/
  | derive :
      HasTypeAffine Γ Δ e₁ (Ty.belief A c₁) c_e₁ U₁ →
      HasTypeAffine Γ Δ e₂ (Ty.belief B c₂) c_e₂ U₂ →
      U₁.disjoint U₂ →
      HasTypeAffine Γ Δ (Expr.derive e₁ e₂)
                    (Ty.belief (Ty.prod A B) (c₁ * c₂))
                    (c_e₁ * c_e₂) (U₁ ∪ U₂)

  /-! ### Aggregation Rule (Key Affine Constraint) -/

  /-- Aggregation: MUST have disjoint evidence usage.
      This is the core rule preventing double-counting. -/
  | aggregate :
      HasTypeAffine Γ Δ e₁ (Ty.belief A c₁) c_e₁ U₁ →
      HasTypeAffine Γ Δ e₂ (Ty.belief A c₂) c_e₂ U₂ →
      U₁.disjoint U₂ →  -- Critical: prevents same evidence in both
      HasTypeAffine Γ Δ (Expr.aggregate e₁ e₂)
                    (Ty.belief A (c₁ ⊕ c₂))
                    (c_e₁ ⊕ c_e₂) (U₁ ∪ U₂)

  /-! ### Defeat Rules -/

  /-- Undercut: defeat evidence is also tracked -/
  | undercut :
      HasTypeAffine Γ Δ e (Ty.belief A c) c_e U_e →
      HasTypeAffine Γ Δ d (Ty.belief DefeatTy d_c) c_d U_d →
      U_e.disjoint U_d →  -- Defeat evidence distinct from original
      HasTypeAffine Γ Δ (Expr.undercut e d)
                    (Ty.belief A (ConfBound.undercut c d_c))
                    (c_e * c_d) (U_e ∪ U_d)

  /-- Rebut: counter-evidence tracked -/
  | rebut :
      HasTypeAffine Γ Δ e_for (Ty.belief A c_for) c_e₁ U₁ →
      HasTypeAffine Γ Δ e_against (Ty.belief A c_against) c_e₂ U₂ →
      U₁.disjoint U₂ →
      HasTypeAffine Γ Δ (Expr.rebut e_for e_against)
                    (Ty.belief A (ConfBound.rebut c_for c_against))
                    (c_e₁ * c_e₂) (U₁ ∪ U₂)

  /-! ### Introspection (Stratified) -/

  /-- Introspect: usage preserved -/
  | introspect :
      HasTypeAffine Γ Δ e (Ty.meta A m c) c_e U →
      m < n →
      HasTypeAffine Γ Δ (Expr.introspect e)
                    (Ty.meta (Ty.meta A m c) n (ConfBound.loebDiscount c))
                    c_e U

  /-! ### Let Binding (Cut) -/

  /-- Let: bound expression becomes unrestricted OR affine based on annotation.
      Here we assume let-bound values go to unrestricted context. -/
  | letIn :
      HasTypeAffine Γ Δ e₁ A c₁ U₁ →
      HasTypeAffine (Γ.extend ⟨A, c₁⟩) Δ e₂ B c₂ U₂ →
      U₁.disjoint U₂ →
      HasTypeAffine Γ Δ (Expr.letIn e₁ e₂) B (c₁ * c₂) (U₁ ∪ U₂)

  /-! ### Literals -/

  | litNat : HasTypeAffine Γ Δ (Expr.litNat n) Ty.nat 1 ∅
  | litBool : HasTypeAffine Γ Δ (Expr.litBool b) Ty.bool 1 ∅
  | litString : HasTypeAffine Γ Δ (Expr.litString s) Ty.string 1 ∅
  | litUnit : HasTypeAffine Γ Δ Expr.litUnit Ty.unit 1 ∅

  /-! ### Subsumption -/

  | sub :
      HasTypeAffine Γ Δ e A c U →
      A <: A' →
      c ≥ c' →
      HasTypeAffine Γ Δ e A' c' U

/-- Notation for affine typing -/
notation:40 Γ ";" Δ " ⊢ₐ " e " : " A " @" c " ⇝ " U => HasTypeAffine Γ Δ e A c U
```

---

## 5. Resource Safety Theorem

### 5.1 The Key Theorem

The point of affine typing is to guarantee resource safety. We need to prove:

**Theorem (Resource Safety)**: In any well-typed term, each affine variable is used at most once.

More precisely:

```lean
theorem resource_safety :
    HasTypeAffine Γ Δ e A c U →
    ∀ (n : Nat), n ∈ U → appears_once_in e n
```

But this requires defining what "appears once" means. A cleaner statement:

**Theorem (Disjoint Usage)**:
The typing rules guarantee that at every point where subterms are combined, their usage sets are disjoint.

This is actually built into the typing rules (the `U₁.disjoint U₂` premises). What we need to prove is:

**Theorem (Usage Correctness)**: If `HasTypeAffine Γ Δ e A c U`, then:
1. `U ⊆ dom(Δ)` (usage only from affine context)
2. For each `n ∈ U`, variable n appears in e (soundness)
3. For each affine variable n appearing in e, either `n ∈ U` or the variable is from Γ (completeness)

### 5.2 Proof Strategy

```lean
theorem usage_in_affine_context
    (h : HasTypeAffine Γ Δ e A c U) : U ⊆ Finset.range Δ.length := by
  induction h with
  | var_unrestricted _ => simp [UsageSet.empty]
  | var_affine hlookup =>
      -- If lookup succeeds, index is in range
      simp [Ctx.lookup] at hlookup
      sorry -- Need lemma: lookup_some_implies_in_range
  | app _ _ _ hU₁ hU₂ hdisj ih₁ ih₂ =>
      -- U = U₁ ∪ U₂, both subsets by IH
      sorry
  -- ... other cases
```

### 5.3 Non-Duplication Guarantee

The critical guarantee:

**Theorem (No Double Counting)**:
If `HasTypeAffine Γ Δ (Expr.aggregate e₁ e₂) (Ty.belief A c) c_e U` is derivable,
then the evidence used in e₁ and e₂ is disjoint.

This is immediate from the `aggregate` rule which requires `U₁.disjoint U₂`.

---

## 6. Decidability of Affine Type Checking

### 6.1 Algorithm Sketch

Per Thread 3.49, type checking should be decidable. The algorithm:

```lean
/-- Decidable type checking with usage computation -/
def typecheck (Γ : UnrestrictedCtx) (Δ : AffineCtx) (e : Expr)
    : Option (Ty × ConfBound × UsageSet) :=
  match e with
  | Expr.var n =>
      -- First check unrestricted context
      if let some ⟨A, c⟩ := Γ.lookup n then
        some (A, c, ∅)
      -- Then check affine context
      else if let some ⟨A, c⟩ := Δ.lookup n then
        some (A, c, {n})
      else
        none

  | Expr.app e₁ e₂ =>
      match typecheck Γ Δ e₁ with
      | some (Ty.fn A B, c₁, U₁) =>
          match typecheck Γ Δ e₂ with
          | some (A', c₂, U₂) =>
              if A = A' && U₁.disjoint U₂ then
                some (B, c₁ * c₂, U₁ ∪ U₂)
              else none
          | none => none
      | _ => none

  | Expr.aggregate e₁ e₂ =>
      match typecheck Γ Δ e₁, typecheck Γ Δ e₂ with
      | some (Ty.belief A c₁, c_e₁, U₁), some (Ty.belief A' c₂, c_e₂, U₂) =>
          if A = A' && U₁.disjoint U₂ then
            some (Ty.belief A (c₁ ⊕ c₂), c_e₁ ⊕ c_e₂, U₁ ∪ U₂)
          else none
      | _, _ => none

  -- ... other cases
```

### 6.2 Decidability Instance

```lean
instance : Decidable (HasTypeAffine Γ Δ e A c U) := by
  -- By structural induction on e, show each case decidable
  sorry -- Full proof requires careful handling of subsumption
```

The decidability follows from:
1. Context lookup is decidable
2. Type equality is decidable
3. Rational comparison is decidable
4. Disjointness of finite sets is decidable

---

## 7. Exponential Evidence (!)

### 7.1 Marking Reusable Evidence

Thread 3.48 established that some evidence should be reusable (exponential):
- Axioms
- Source reliability attacks
- Established facts

In the formalization:

```lean
/-- Evidence marker: affine or exponential -/
inductive EvidenceKind where
  | affine       -- Use at most once
  | exponential  -- Use any number of times (!)

/-- Extended context entry -/
structure CtxEntryExt where
  ty   : Ty
  conf : ConfBound
  kind : EvidenceKind
```

**Promotion rule**: Evidence used only in exponential context can be marked exponential:

```lean
/-- Promotion: if derivation uses only unrestricted evidence,
    result can be unrestricted -/
| promote :
    HasTypeAffine Γ [] e A c ∅ →  -- No affine usage
    HasTypeAffine (Γ.extend ⟨A, c⟩) Δ' e' B c' U →
    HasTypeAffine Γ Δ' (Expr.letExp e e') B c' U
```

### 7.2 Simplification: Two Separate Contexts

For the initial formalization, the simpler approach is:
- Unrestricted context Γ: no usage tracking needed
- Affine context Δ: usage tracking via sets

Evidence enters the unrestricted context via explicit annotation in the source:

```clair
let axiom : !Evidence<"2+2=4"> = ...  -- Goes to Γ
let testimony : Evidence<...> = ...    -- Goes to Δ
```

---

## 8. Implementation Plan

### 8.1 Phase 1: Core Types (This Session)

1. Define `UsageSet` and operations
2. Define `DualCtx` (Γ; Δ pair)
3. Create `HasTypeAffine` inductive type

### 8.2 Phase 2: Basic Properties

1. Prove `usage_in_affine_context`
2. Prove `disjoint_usage_at_splits`
3. Show substitution lemma (may need adjustment)

### 8.3 Phase 3: Decidability

1. Define `typecheck` function
2. Prove soundness: `typecheck returns some → HasTypeAffine`
3. Prove completeness: `HasTypeAffine → typecheck returns some`

### 8.4 Phase 4: Resource Safety

1. Define `uses_once` predicate
2. Prove resource safety theorem
3. Connect to Thread 3.46's theoretical guarantees

---

## 9. Comparison with Existing Formalization

### 9.1 Changes Required

| Component | Current | After 3.47 |
|-----------|---------|------------|
| Context | Single `Ctx` | Dual `(Γ, Δ)` |
| Judgment | `HasType Γ e A c` | `HasTypeAffine Γ Δ e A c U` |
| Variable | Single lookup | Check Γ, then Δ |
| App | No disjointness | Requires `U₁.disjoint U₂` |
| Aggregate | No constraint | Requires `U₁.disjoint U₂` |
| Defeat | No constraint | Requires disjoint usage |

### 9.2 What Can Be Preserved

- Type syntax (`Ty`) - unchanged
- Expression syntax (`Expr`) - unchanged
- Confidence operations - unchanged
- Subtyping relation - unchanged
- Many proof techniques - adaptable

### 9.3 Migration Path

The old `HasType` can be recovered as a special case:

```lean
/-- Original judgment as special case: everything unrestricted -/
def HasType Γ e A c := HasTypeAffine Γ [] e A c ∅
```

This shows the extension is conservative.

---

## 10. Open Questions

### 10.1 Lambda Binding

When we bind a lambda parameter, which context does it enter?

**Option A**: Always affine (conservative)
```lean
| lam_affine : HasTypeAffine Γ (Δ.extend ⟨A, c_A⟩) e B c_B U → ...
```

**Option B**: Syntax-directed (annotation chooses)
```lean
| lam_unrestricted : HasTypeAffine (Γ.extend ⟨A, c_A⟩) Δ e B c_B U → ...
| lam_affine : HasTypeAffine Γ (Δ.extend ⟨A, c_A⟩) e B c_B U → ...
```

For simplicity, Option A is likely sufficient—function parameters that need reuse can be explicitly marked.

### 10.2 Let Binding

Similarly for let:
- If the bound value is evidence, should it be affine by default?
- Should there be `let!` for unrestricted binding?

**Recommendation**: Default to unrestricted for non-evidence types, affine for evidence types.

### 10.3 De Bruijn Indices and Context Extension

With two contexts and de Bruijn indices, there's complexity:
- Which context does index 0 refer to?
- How do indices shift when extending either context?

**Simplification**: Use separate indexing for each context, with syntax distinguishing them:
- `var_u n` for unrestricted
- `var_a n` for affine

But this changes the expression syntax. Alternative: accept the complexity of a unified namespace.

---

## 11. Conclusions

### 11.1 Summary

**Task 3.47 design is substantially complete.**

The formalization approach:
1. **Dual contexts** (Γ; Δ) for unrestricted and affine evidence
2. **Usage sets** (U) tracking which affine evidence is used
3. **Disjointness constraints** at aggregation and combination points
4. **Decidable checking** by structural recursion with set operations

### 11.2 Key Theorems to Prove

1. **Usage Soundness**: U ⊆ dom(Δ)
2. **Disjoint Usage**: At split points, U₁ ∩ U₂ = ∅
3. **Resource Safety**: Each affine variable used at most once
4. **Decidability**: Type checking is decidable

### 11.3 Confidence Table

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Dual context approach is correct | 0.90 | Matches linear logic literature |
| Usage sets capture affine discipline | 0.85 | Standard technique (Walker 2005) |
| Design is decidable | 0.90 | Follows Thread 3.49 analysis |
| Integration with existing Lean is feasible | 0.80 | Requires careful index handling |
| Resource safety is provable | 0.85 | Direct from typing rules |

### 11.4 Next Steps

1. **Implement Phase 1** in Lean: types and judgment definition
2. **Test on examples** to verify rules work as expected
3. **Prove basic properties** (Phase 2)
4. **Connect to interpreter extraction** (Task 8.4)

### 11.5 Impact

This formalization:
- Makes CLAIR's evidence discipline machine-checkable
- Enables extraction of type-safe interpreter (Task 8.4)
- Proves the theoretical guarantees from Thread 3.46 are realizable
- Demonstrates CLAIR is a viable formal epistemic language

---

## 12. References

### CLAIR Internal

- Thread 3.46: exploration/completed/thread-3.46-epistemic-linearity.md
- Thread 3.48: exploration/completed/thread-3.48-linearity-defeat-interaction.md
- Thread 3.49: exploration/completed/thread-3.49-decidability-affine-clair.md
- Existing Lean: formal/lean/CLAIR/Typing/HasType.lean

### External

- **Walker, D.** (2005). "Substructural Type Systems." *Advanced Topics in Types and Programming Languages*.
- **Atkey, R.** (2018). "Syntax and Semantics of Quantitative Type Theory." *LICS*.
- **Bernardy et al.** (2018). "Linear Haskell: practical linearity in a higher-order polymorphic language." *POPL*.
- **Girard, J-Y.** (1987). "Linear Logic." *Theoretical Computer Science*.

---

*Thread 3.47 Status: Design exploration complete. Recommended approach: dual contexts (Γ; Δ) with usage set tracking (U). Disjointness constraints at aggregation points enforce evidence non-duplication. Ready for Lean implementation.*
