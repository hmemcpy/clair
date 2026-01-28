# Thread 8.12: CLAIR Syntax Formalization in Lean 4

> **Status**: Active exploration (Session 61)
> **Task**: 8.1 Define CLAIR syntax and typing in Lean 4
> **Question**: How should CLAIR's term language (Thread 2.22) be formalized in Lean 4?
> **Prior Work**: Thread 2.22 (Curry-Howard terms), Thread 2.16 (sequent calculus), formal/lean/ (semantic types)

---

## 1. The Problem

### 1.1 What Exists vs What's Needed

CLAIR's Lean 4 formalization currently has:

**Semantic types (what values look like at runtime):**
- `Confidence` - the [0,1] interval with operations (×, ⊕, undercut, rebut, min)
- `Belief<α>` - a value paired with confidence
- `StratifiedBelief<n, α>` - level-indexed beliefs for safe introspection

**What's missing (syntactic representation):**
- `Expr` - the grammar of CLAIR expressions
- `Ty` - the grammar of CLAIR types
- `HasType` - typing judgments (Γ ⊢ e : τ)
- `Step` - operational semantics (e → e')

This is the difference between:
- **Denotational semantics**: What does a CLAIR program *mean*? (Done)
- **Operational semantics**: How does a CLAIR program *run*? (Needed)
- **Type system**: Which CLAIR programs are *well-formed*? (Needed)

### 1.2 Why This Matters

With syntax formalization, we can:
1. **Prove type safety** (progress + preservation) - Task 8.2
2. **Prove confidence soundness** - Task 8.3
3. **Extract an interpreter** - Task 8.4
4. **Connect syntax to semantics** - prove that evaluation preserves meaning

### 1.3 The Core Challenge

CLAIR has features beyond standard type theory:
- **Graded types**: `Belief<A>[c]` carries a confidence bound
- **Defeat operations**: `undercut`, `rebut` as first-class term formers
- **Aggregation**: Multiple evidence combines via ⊕
- **Stratification**: Level-indexed introspection

The question is: **What Lean 4 representation strategy best captures CLAIR?**

---

## 2. Design Space Analysis

### 2.1 Variable Representation Strategies

Three main approaches exist for representing variables in formalized languages:

#### Option A: De Bruijn Indices

```lean
inductive Expr where
  | var : Nat → Expr
  | lam : Expr → Expr  -- binding implicit
  | app : Expr → Expr → Expr
```

**Pros:**
- No variable naming issues
- Canonical representation
- Works well with contexts as lists

**Cons:**
- Index shifting during substitution is error-prone
- Less readable terms
- Substitution requires careful index management

#### Option B: Parametric Higher-Order Abstract Syntax (PHOAS)

```lean
inductive Expr (rep : Ty → Type) : Ty → Type where
  | var : rep ty → Expr rep ty
  | lam : (rep A → Expr rep B) → Expr rep (A ⇒ B)
  | app : Expr rep (A ⇒ B) → Expr rep A → Expr rep B
```

**Pros:**
- Uses Lean's binding constructs
- No explicit substitution needed
- Very elegant

**Cons:**
- Harder to reason about (function in datatype)
- Less suited for operational semantics
- May complicate extraction

#### Option C: Named Variables with Well-Scopedness

```lean
abbrev Name := String

inductive Expr where
  | var : Name → Expr
  | lam : Name → Ty → Expr → Expr
  | app : Expr → Expr → Expr
```

**Pros:**
- Most readable
- Intuitive

**Cons:**
- Requires α-equivalence
- Substitution must avoid capture
- Name freshness obligations

### 2.2 Recommendation: De Bruijn Indices

For CLAIR, **de Bruijn indices** are the best choice because:

1. **Contexts are ordered** - CLAIR's contexts `Γ, x : Belief<A>[c]` map naturally to lists
2. **No α-equivalence needed** - Simplifies proofs
3. **Standard for formalization** - PLFaLean, Software Foundations use this
4. **Confidence bounds in context** - Context entries need to track confidence, easier with lists

The main cost (index shifting) is manageable with careful lemmas.

---

## 3. Type Grammar

### 3.1 Base Types

```lean
inductive BaseTy where
  | nat
  | bool
  | string
  | unit
  deriving Repr, DecidableEq
```

### 3.2 CLAIR Types

```lean
-- Confidence bounds for types
-- Using ℚ (rationals) for decidable equality
abbrev ConfBound := ℚ

inductive Ty where
  | base : BaseTy → Ty
  | fn : Ty → Ty → Ty                        -- A → B
  | prod : Ty → Ty → Ty                      -- A × B
  | sum : Ty → Ty → Ty                       -- A + B
  | belief : Ty → ConfBound → Ty             -- Belief<A>[c]
  | meta : Ty → Nat → ConfBound → Ty         -- Meta<A>[n][c] (stratified)
  deriving Repr, DecidableEq
```

**Design decisions:**
- **Confidence bounds are rational**: Enables decidable type checking
- **Belief carries both content type and confidence bound**
- **Meta is indexed by level and confidence** for stratification

### 3.3 Subtyping (Confidence-Based)

Per Thread 2.23, higher confidence is a subtype:
```
Belief<A>[c] <: Belief<A>[c']  when c ≥ c'
```

This will be a separate inductive relation:

```lean
inductive Subtype : Ty → Ty → Prop where
  | refl : Subtype A A
  | belief_sub : c ≥ c' → Subtype (Ty.belief A c) (Ty.belief A c')
  | fn_sub : Subtype A' A → Subtype B B' →
             Subtype (Ty.fn A B) (Ty.fn A' B')
  -- contravariant in argument, covariant in result
```

---

## 4. Expression Grammar

### 4.1 Core Expressions

```lean
-- Justification terms (simplified for now)
inductive Justification where
  | axiom : String → Justification
  | rule : String → List Justification → Justification
  | agg : List Justification → Justification
  | undercut_j : Justification → Justification → Justification
  | rebut_j : Justification → Justification → Justification

inductive Expr where
  -- Variables (de Bruijn)
  | var : Nat → Expr

  -- Standard lambda calculus
  | lam : Ty → Expr → Expr          -- λ:A. e (type-annotated)
  | app : Expr → Expr → Expr

  -- Products
  | pair : Expr → Expr → Expr
  | fst : Expr → Expr
  | snd : Expr → Expr

  -- Sums
  | inl : Ty → Expr → Expr          -- inl@B(e)
  | inr : Ty → Expr → Expr          -- inr@A(e)
  | case : Expr → Expr → Expr → Expr  -- case e of inl x => e₁ | inr y => e₂

  -- Belief constructors
  | belief : Expr → ConfBound → Justification → Expr  -- belief(v, c, j)
  | val : Expr → Expr               -- extract value
  | conf : Expr → Expr              -- extract confidence
  | just : Expr → Expr              -- extract justification

  -- Derivation
  | derive : Expr → Expr → Expr     -- derive(e₁, e₂) - binary derivation

  -- Aggregation
  | aggregate : Expr → Expr → Expr  -- aggregate(e₁, e₂)

  -- Defeat
  | undercut : Expr → Expr → Expr   -- undercut(e, d)
  | rebut : Expr → Expr → Expr      -- rebut(e_for, e_against)

  -- Introspection (stratified)
  | introspect : Expr → Expr        -- introspect(e)

  -- Let binding (corresponds to cut)
  | letIn : Expr → Expr → Expr      -- let x = e₁ in e₂

  deriving Repr
```

### 4.2 Values

```lean
inductive IsValue : Expr → Prop where
  | lam : IsValue (Expr.lam A e)
  | pair : IsValue v₁ → IsValue v₂ → IsValue (Expr.pair v₁ v₂)
  | inl : IsValue v → IsValue (Expr.inl B v)
  | inr : IsValue v → IsValue (Expr.inr A v)
  | belief : IsValue v → IsValue (Expr.belief v c j)
```

### 4.3 Substitution

With de Bruijn indices, substitution requires index shifting:

```lean
-- Shift indices in an expression by d, starting from cutoff c
def shift (d : Int) (c : Nat) : Expr → Expr
  | Expr.var n => Expr.var (if n < c then n else (n : Int) + d).toNat
  | Expr.lam A e => Expr.lam A (shift d (c + 1) e)
  | Expr.app e₁ e₂ => Expr.app (shift d c e₁) (shift d c e₂)
  | Expr.pair e₁ e₂ => Expr.pair (shift d c e₁) (shift d c e₂)
  -- ... similar for other constructors

-- Substitute expression s for variable k in expression e
def subst (k : Nat) (s : Expr) : Expr → Expr
  | Expr.var n =>
      if n < k then Expr.var n
      else if n = k then shift k 0 s
      else Expr.var (n - 1)
  | Expr.lam A e => Expr.lam A (subst (k + 1) (shift 1 0 s) e)
  | Expr.app e₁ e₂ => Expr.app (subst k s e₁) (subst k s e₂)
  -- ... similar for other constructors
```

---

## 5. Typing Judgments

### 5.1 Contexts

```lean
-- Context entry: a belief assumption with confidence bound
structure CtxEntry where
  ty : Ty
  conf : ConfBound

-- Context is a list (de Bruijn: position = variable number)
abbrev Ctx := List CtxEntry

-- Lookup in context
def Ctx.lookup (Γ : Ctx) (n : Nat) : Option CtxEntry :=
  Γ.get? n
```

### 5.2 Typing Relation

```lean
-- Main typing judgment: Γ ⊢ e : A @c
-- "In context Γ, expression e has type A with confidence bound c"
inductive HasType : Ctx → Expr → Ty → ConfBound → Prop where

  -- Variable
  | var : Γ.lookup n = some ⟨A, c⟩ →
          HasType Γ (Expr.var n) A c

  -- Lambda introduction
  | lam : HasType (⟨A, c_A⟩ :: Γ) e B c_B →
          HasType Γ (Expr.lam A e) (Ty.fn A B) c_B

  -- Application (modus ponens)
  | app : HasType Γ e₁ (Ty.fn A B) c₁ →
          HasType Γ e₂ A c₂ →
          HasType Γ (Expr.app e₁ e₂) B (c₁ * c₂)

  -- Pair introduction
  | pair : HasType Γ e₁ A c₁ →
           HasType Γ e₂ B c₂ →
           HasType Γ (Expr.pair e₁ e₂) (Ty.prod A B) (c₁ * c₂)

  -- Projections
  | fst : HasType Γ e (Ty.prod A B) c →
          HasType Γ (Expr.fst e) A c
  | snd : HasType Γ e (Ty.prod A B) c →
          HasType Γ (Expr.snd e) B c

  -- Belief constructor
  | belief : HasType Γ v A 1 →  -- Value has full confidence
             c_bound ≤ c_actual →  -- Actual confidence meets bound
             HasType Γ (Expr.belief v c_actual j) (Ty.belief A c_bound) c_bound

  -- Value extraction
  | val : HasType Γ e (Ty.belief A c) c_e →
          HasType Γ (Expr.val e) A c_e

  -- Derivation (binary)
  | derive : HasType Γ e₁ (Ty.belief A c₁) c_e₁ →
             HasType Γ e₂ (Ty.belief B c₂) c_e₂ →
             HasType Γ (Expr.derive e₁ e₂)
                       (Ty.belief (Ty.prod A B) (c₁ * c₂))
                       (c_e₁ * c_e₂)

  -- Aggregation
  | aggregate : HasType Γ e₁ (Ty.belief A c₁) c_e₁ →
                HasType Γ e₂ (Ty.belief A c₂) c_e₂ →
                HasType Γ (Expr.aggregate e₁ e₂)
                          (Ty.belief A (oplus c₁ c₂))
                          (oplus c_e₁ c_e₂)

  -- Undercut
  | undercut : HasType Γ e (Ty.belief A c) c_e →
               HasType Γ d (Ty.belief DefeatTy d_c) c_d →
               HasType Γ (Expr.undercut e d)
                         (Ty.belief A (c * (1 - d_c)))
                         (c_e * c_d)

  -- Rebut
  | rebut : HasType Γ e_for (Ty.belief A c_for) c_e₁ →
            HasType Γ e_against (Ty.belief A c_against) c_e₂ →
            HasType Γ (Expr.rebut e_for e_against)
                      (Ty.belief A (rebut_conf c_for c_against))
                      (c_e₁ * c_e₂)

  -- Introspection (stratified)
  | introspect : HasType Γ e (Ty.meta A m c) c_e →
                 m < n →  -- Level constraint
                 HasType Γ (Expr.introspect e)
                           (Ty.meta (Ty.meta A m c) n (c * c))  -- Löb discount
                           c_e

  -- Let (cut)
  | letIn : HasType Γ e₁ A c₁ →
            HasType (⟨A, c₁⟩ :: Γ) e₂ B c₂ →
            HasType Γ (Expr.letIn e₁ e₂) B (c₁ * c₂)

  -- Subsumption (subtyping)
  | sub : HasType Γ e A c →
          Subtype A A' →
          c ≥ c' →
          HasType Γ e A' c'

-- Helper for ⊕
def oplus (a b : ℚ) : ℚ := a + b - a * b

-- Helper for rebut confidence
def rebut_conf (c_for c_against : ℚ) : ℚ :=
  if c_for + c_against = 0 then 1/2
  else c_for / (c_for + c_against)
```

---

## 6. Operational Semantics

### 6.1 Single-Step Reduction

```lean
inductive Step : Expr → Expr → Prop where
  -- Beta reduction
  | beta : IsValue v →
           Step (Expr.app (Expr.lam A e) v) (subst 0 v e)

  -- Let reduction
  | letBeta : IsValue v →
              Step (Expr.letIn v e) (subst 0 v e)

  -- Projection reduction
  | fstBeta : IsValue v₁ → IsValue v₂ →
              Step (Expr.fst (Expr.pair v₁ v₂)) v₁
  | sndBeta : IsValue v₁ → IsValue v₂ →
              Step (Expr.snd (Expr.pair v₁ v₂)) v₂

  -- Belief extraction
  | valBeta : IsValue v →
              Step (Expr.val (Expr.belief v c j)) v

  -- Undercut reduction
  | undercutBeta : IsValue v → IsValue d →
                   Step (Expr.undercut (Expr.belief v c_v j_v)
                                       (Expr.belief d c_d j_d))
                        (Expr.belief v (c_v * (1 - c_d))
                                     (Justification.undercut_j j_v j_d))

  -- Rebut reduction
  | rebutBeta : IsValue v_for → IsValue v_against →
                Step (Expr.rebut (Expr.belief v_for c_for j_for)
                                 (Expr.belief v_against c_against j_against))
                     (Expr.belief v_for (rebut_conf c_for c_against)
                                  (Justification.rebut_j j_for j_against))

  -- Aggregation reduction
  | aggregateBeta : IsValue v₁ → IsValue v₂ →
                    -- v₁ = v₂ required (same value)
                    Step (Expr.aggregate (Expr.belief v₁ c₁ j₁)
                                        (Expr.belief v₂ c₂ j₂))
                         (Expr.belief v₁ (oplus c₁ c₂)
                                      (Justification.agg [j₁, j₂]))

  -- Congruence rules (evaluation contexts)
  | app₁ : Step e₁ e₁' → Step (Expr.app e₁ e₂) (Expr.app e₁' e₂)
  | app₂ : IsValue v → Step e₂ e₂' → Step (Expr.app v e₂) (Expr.app v e₂')
  | pair₁ : Step e₁ e₁' → Step (Expr.pair e₁ e₂) (Expr.pair e₁' e₂)
  | pair₂ : IsValue v → Step e₂ e₂' → Step (Expr.pair v e₂) (Expr.pair v e₂')
  | fst_cong : Step e e' → Step (Expr.fst e) (Expr.fst e')
  | snd_cong : Step e e' → Step (Expr.snd e) (Expr.snd e')
  | belief_cong : Step v v' → Step (Expr.belief v c j) (Expr.belief v' c j)
  | val_cong : Step e e' → Step (Expr.val e) (Expr.val e')
  | undercut₁ : Step e e' → Step (Expr.undercut e d) (Expr.undercut e' d)
  | undercut₂ : IsValue v → Step d d' → Step (Expr.undercut v d) (Expr.undercut v d')
  | rebut₁ : Step e e' → Step (Expr.rebut e d) (Expr.rebut e' d)
  | rebut₂ : IsValue v → Step d d' → Step (Expr.rebut v d) (Expr.rebut v d')
  | aggregate₁ : Step e₁ e₁' → Step (Expr.aggregate e₁ e₂) (Expr.aggregate e₁' e₂)
  | aggregate₂ : IsValue v → Step e₂ e₂' → Step (Expr.aggregate v e₂) (Expr.aggregate v e₂')
  | letIn_cong : Step e₁ e₁' → Step (Expr.letIn e₁ e₂) (Expr.letIn e₁' e₂)
```

### 6.2 Multi-Step Reduction

```lean
inductive Star (r : α → α → Prop) : α → α → Prop where
  | refl : Star r a a
  | step : r a b → Star r b c → Star r a c
```

---

## 7. Type Safety Statements

### 7.1 Progress

**Theorem (Progress)**: If `[] ⊢ e : A @c` (closed, well-typed), then either:
1. `IsValue e`, or
2. `∃ e', Step e e'`

```lean
theorem progress {e : Expr} {A : Ty} {c : ConfBound} :
    HasType [] e A c → IsValue e ∨ ∃ e', Step e e' := by
  sorry  -- To be proven
```

### 7.2 Preservation

**Theorem (Preservation)**: If `Γ ⊢ e : A @c` and `Step e e'`, then `Γ ⊢ e' : A @c'` where `c' ≤ c`.

```lean
theorem preservation {Γ : Ctx} {e e' : Expr} {A : Ty} {c : ConfBound} :
    HasType Γ e A c → Step e e' → ∃ c', c' ≤ c ∧ HasType Γ e' A c' := by
  sorry  -- To be proven
```

**Note**: Confidence may decrease during evaluation. This is correct: computation may reveal that initial confidence was too optimistic (e.g., defeat being applied).

### 7.3 Required Lemmas

To prove preservation, we need:

1. **Weakening**: `Γ ⊢ e : A @c → Γ, x:B ⊢ e : A @c` (suitably shifted)
2. **Substitution**: `Γ, x:A @c_A ⊢ e : B @c` and `Γ ⊢ v : A @c_A` implies `Γ ⊢ e[v/x] : B @c'`
3. **Confidence bounds preserved**: Operations preserve [0,1] bounds (already proven in CLAIR/Confidence/)

---

## 8. Connection to Existing Formalization

### 8.1 Semantic Interpretation

The existing `Belief<α>` type provides the denotational semantics:

```lean
-- Semantic interpretation of types
def Ty.sem : Ty → Type
  | .base .nat => Nat
  | .base .bool => Bool
  | .base .unit => Unit
  | .fn A B => A.sem → B.sem
  | .prod A B => A.sem × B.sem
  | .belief A _ => CLAIR.Belief A.sem
  | .meta A n _ => CLAIR.StratifiedBelief n A.sem

-- Semantic interpretation of expressions (evaluation)
def eval (env : Ctx.sem Γ) : (e : Expr) → (h : HasType Γ e A c) → A.sem
```

### 8.2 Adequacy

**Theorem (Adequacy)**: If `[] ⊢ e : A @c` and `Star Step e v` (evaluates to value), then `eval e = v.sem` (syntactic and semantic evaluation agree).

---

## 9. Key Findings

### 9.1 Design Decisions Made

1. **De Bruijn indices** for variable representation - canonical, works with list contexts
2. **Rational confidence bounds** for decidable type checking
3. **Graded typing** with confidence in both types and judgments
4. **Confidence decreases during evaluation** - preservation gives c' ≤ c
5. **Subtyping based on confidence** - higher confidence is subtype

### 9.2 Novel Aspects of CLAIR

Compared to standard type theory formalizations:

| Aspect | Standard | CLAIR |
|--------|----------|-------|
| Types | A | Belief<A>[c] with confidence bound |
| Judgments | Γ ⊢ e : A | Γ ⊢ e : A @c with judgment confidence |
| Preservation | Same type | Type preserved, confidence may decrease |
| Novel constructors | None | derive, aggregate, undercut, rebut, introspect |

### 9.3 The Dual-Monoid Challenge

CLAIR's confidence operations don't form a semiring:
```
a × (b ⊕ c) ≠ (a × b) ⊕ (a × c)
```

This means:
- Derivation uses × for confidence composition
- Aggregation uses ⊕ for confidence combination
- The type system must keep these separate

The typing rules correctly handle this:
- `derive` multiplies confidences (×)
- `aggregate` combines confidences (⊕)
- No rule mixes the two operations incorrectly

---

## 10. Recommendations

### 10.1 Implementation Phases

**Phase 1: Core syntax** (this task - 8.1)
- [ ] Define `Ty`, `Expr` inductive types
- [ ] Define substitution with de Bruijn
- [ ] Define `HasType` typing relation
- [ ] Define `Step` reduction relation

**Phase 2: Basic type safety** (Task 8.2)
- [ ] Prove weakening lemma
- [ ] Prove substitution lemma
- [ ] Prove progress theorem
- [ ] Prove preservation theorem

**Phase 3: Confidence soundness** (Task 8.3)
- [ ] Connect to existing CLAIR/Confidence/ proofs
- [ ] Prove that semantic evaluation agrees with operational
- [ ] Prove confidence bounds are preserved

**Phase 4: Extraction** (Task 8.4)
- [ ] Make definitions computable where possible
- [ ] Extract Haskell/OCaml interpreter
- [ ] Test on example programs

### 10.2 Module Organization

```
formal/lean/CLAIR/
├── Confidence/        -- [DONE] Semantic confidence operations
├── Belief/            -- [DONE] Semantic belief types
├── Syntax/            -- [NEW] Syntactic representation
│   ├── Types.lean     -- Type grammar
│   ├── Expr.lean      -- Expression grammar
│   ├── Subst.lean     -- Substitution
│   └── Context.lean   -- Typing contexts
├── Typing/            -- [NEW] Type system
│   ├── HasType.lean   -- Typing relation
│   └── Subtype.lean   -- Subtyping
├── Semantics/         -- [NEW] Operational semantics
│   ├── Step.lean      -- Single-step reduction
│   └── Eval.lean      -- Multi-step + evaluation
└── Safety/            -- [NEW] Metatheory
    ├── Progress.lean  -- Progress theorem
    └── Preservation.lean -- Preservation theorem
```

### 10.3 Next Steps

This exploration has designed the Lean 4 formalization of CLAIR syntax. The actual implementation should:

1. Start with Phase 1 (syntax definitions)
2. Test definitions on small examples
3. Proceed to Phase 2 only after Phase 1 compiles cleanly
4. Consider extracting an interpreter early for validation

---

## 11. Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| De Bruijn is correct choice | 0.85 | Standard approach, works with list contexts |
| Type grammar is complete | 0.75 | May need refinement for edge cases |
| Typing rules are sound | 0.80 | Based on Thread 2.22 design |
| Progress theorem holds | 0.85 | Standard technique applies |
| Preservation holds | 0.80 | Confidence decrease is novel but handled |
| Phases will work | 0.70 | Depends on implementation details |

---

## 12. Open Questions

1. **How to handle base type literals?** - Need constructors for Nat, Bool, String values
2. **Should confidence be ℚ or a custom finite lattice?** - ℚ for generality, but L₅ for decidability?
3. **How to formalize "independence" for aggregation?** - Currently implicit; may need explicit tracking
4. **What about polymorphism?** - Not addressed; may need for practical use
5. **Introspection levels** - How does level checking work in the typing rules?

---

## 13. Impact on Other Tasks

This exploration informs:

- **Task 8.2 (Type safety)**: Provides the structure to prove progress + preservation
- **Task 8.3 (Confidence soundness)**: Connects syntax to semantic CLAIR/Confidence/ proofs
- **Task 8.4 (Extract interpreter)**: Gives extractable definitions
- **Thread 7 (Implementation)**: Validates design for Haskell reference interpreter

---

*Thread 8.12 Status: Design complete. Ready for Lean 4 implementation.*
