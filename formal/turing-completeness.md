# Turing-Completeness of CLAIR

This document establishes that CLAIR is Turing-complete and discusses how to prove this with existing tools.

## 1. The Question

**Can CLAIR encode any computable function?**

More precisely: Is the computational core of CLAIR equivalent in power to Turing machines, lambda calculus, or other models of computation?

## 2. CLAIR's Computational Core

### Stripping Away Beliefs

CLAIR has two layers:
1. **Computational layer**: values, functions, types, evaluation
2. **Epistemic layer**: confidence, provenance, justification, invalidation

The epistemic layer is *metadata*—it tracks properties of computation but doesn't restrict what can be computed.

**Key operation:**
```clair
val : Belief<A> → A
```

This extracts the computational content, discarding metadata.

### The Core Language

CLAIR's computational core includes:

```
Types:
  τ ::= Base                    -- Int, Bool, String, etc.
      | τ → τ                   -- functions
      | τ × τ                   -- products
      | τ + τ                   -- sums
      | μα.τ                    -- recursive types (for data structures)

Terms:
  e ::= x                       -- variables
      | λx:τ.e                  -- abstraction
      | e e                     -- application
      | (e, e)                  -- pairs
      | fst e | snd e           -- projections
      | inl e | inr e           -- injections
      | case e of ...           -- case analysis
      | fix e                   -- fixed point (recursion)
      | primitives              -- arithmetic, etc.
```

This is **System F with recursive types** (or PCF-like), which is well-known to be Turing-complete.

## 3. Proof Strategy: Encoding Lambda Calculus

### Untyped Lambda Calculus

The untyped lambda calculus is Turing-complete. We show CLAIR can encode it.

**Lambda calculus:**
```
M ::= x | λx.M | M M
```

**Encoding in CLAIR:**

First, we need a universal type that can represent any lambda term. Using recursive types:

```clair
-- Universal domain (Scott encoding)
type D = μd. (d → d)

-- Or using explicit tagging:
type Term = μt.
  | Var Nat
  | Lam (t → t)
  | App t t
```

**Embedding:**
```clair
embed : LambdaTerm → Belief<D>
embed (Var x)   = belief (lookup x env) @ 1.0
embed (Lam f)   = belief (λd. embed (f (unembed d))) @ 1.0
embed (App m n) = belief ((val (embed m)) (val (embed n))) @ 1.0
```

The confidence is 1.0 throughout because this is pure computation—no uncertainty.

### Typed Encoding (Simpler)

For simply-typed terms, the encoding is direct:
```clair
-- Lambda calculus term: λx. x
-- CLAIR term: λx:A. x

-- Lambda calculus term: (λx. x) y
-- CLAIR term: (λx:A. x) y
```

CLAIR's λ directly corresponds to lambda calculus's λ.

## 4. Proof Strategy: Encoding Recursive Functions

### Primitive Recursive Functions

```clair
-- Zero
zero : Nat
zero = 0

-- Successor
succ : Nat → Nat
succ n = n + 1

-- Projection
proj : (Nat, Nat, ...) → Nat
proj_i (x₁, ..., xₙ) = xᵢ

-- Composition
compose : (B → C) → (A → B) → (A → C)
compose g f = λx. g (f x)

-- Primitive recursion
primrec : A → (Nat → A → A) → Nat → A
primrec base step 0 = base
primrec base step (n+1) = step n (primrec base step n)
```

All primitive recursive functions are encodable. ✓

### General Recursive Functions (μ-recursion)

The μ-operator (unbounded search) requires general recursion:

```clair
-- Fixed point combinator
fix : (A → A) → A
fix f = f (fix f)

-- Or with explicit recursion:
mu : (Nat → Bool) → Nat
mu p = go 0
  where
    go n = if p n then n else go (n + 1)
```

With `fix` (or recursive definitions), we can encode all μ-recursive functions. ✓

## 5. Proof Strategy: Simulating a Turing Machine

### Turing Machine Definition

A Turing machine is (Q, Σ, Γ, δ, q₀, qₐ, qᵣ) where:
- Q = finite set of states
- Σ = input alphabet
- Γ = tape alphabet (Σ ⊆ Γ)
- δ : Q × Γ → Q × Γ × {L, R} = transition function
- q₀ = initial state
- qₐ, qᵣ = accept/reject states

### CLAIR Encoding

```clair
type State = Nat  -- or an enumeration
type Symbol = Nat
type Direction = Left | Right

type Tape = {
  left  : List<Symbol>,  -- reversed left of head
  head  : Symbol,
  right : List<Symbol>
}

type TM = {
  transition : State → Symbol → (State, Symbol, Direction),
  accept : State,
  reject : State
}

type Config = {
  state : State,
  tape  : Tape
}

-- Move the tape head
move : Direction → Tape → Tape
move Left  {left = [],     head = h, right = r} = {left = [], head = 0, right = h :: r}
move Left  {left = l :: ls, head = h, right = r} = {left = ls, head = l, right = h :: r}
move Right {left = l, head = h, right = []}     = {left = h :: l, head = 0, right = []}
move Right {left = l, head = h, right = r :: rs} = {left = h :: l, head = r, right = rs}

-- Single step
step : TM → Config → Config
step tm cfg =
  let (q', s', d) = tm.transition cfg.state cfg.tape.head
  in { state = q',
       tape = move d (cfg.tape with head = s') }

-- Run until halt
run : TM → Config → Result<Bool>
run tm cfg =
  if cfg.state == tm.accept then Ok True
  else if cfg.state == tm.reject then Ok False
  else run tm (step tm cfg)  -- recursive call

-- This may not terminate (that's the point!)
```

CLAIR can simulate any Turing machine. ✓

## 6. Beliefs Don't Restrict Computation

**Theorem:** For any computable function f : A → B, there exists a CLAIR term:
```
f_clair : Belief<A> → Belief<B>
```
such that `val (f_clair (belief a)) = f a`.

**Proof:**
```clair
f_clair : Belief<A> → Belief<B>
f_clair ba =
  let a = val ba  -- extract value
  let b = f a     -- compute (using any encoding above)
  in belief b     -- wrap result
     @ conf ba    -- preserve confidence
     provenance: derived(prov ba)
     justification: rule(f, just ba)
     invalidation: inv ba
```

The belief layer is transparent to computation. QED.

## 7. The Converse: Can Beliefs Be Computed?

**Question:** Can we compute confidence, provenance, etc.?

**Yes**, they're first-class values:
```clair
get_confidence : Belief<A> → Float
get_confidence b = conf b

analyze_justification : Belief<A> → JustificationTree
analyze_justification b = just b
```

So CLAIR can reason about its own beliefs computationally.

## 8. Proving with Today's Tools

### Option A: Formalization in Lean 4

Lean 4 is a dependently-typed language that can:
1. Define CLAIR's syntax and semantics
2. Prove properties about it
3. Extract executable code

```lean
-- CLAIR syntax in Lean
inductive CLAIRType where
  | base : BaseType → CLAIRType
  | arrow : CLAIRType → CLAIRType → CLAIRType
  | belief : CLAIRType → CLAIRType

inductive CLAIRTerm where
  | var : Nat → CLAIRTerm
  | lam : CLAIRType → CLAIRTerm → CLAIRTerm
  | app : CLAIRTerm → CLAIRTerm → CLAIRTerm
  | belief_intro : CLAIRTerm → Confidence → Provenance → CLAIRTerm
  | belief_val : CLAIRTerm → CLAIRTerm
  -- ...

-- Semantics
def eval : CLAIRTerm → Env → Option Value := ...

-- Turing-completeness: embed λ-calculus
def embed_lambda : LambdaTerm → CLAIRTerm := ...

theorem embedding_correct :
  ∀ (m : LambdaTerm) (v : Value),
    lambda_eval m = some v →
    clair_eval (embed_lambda m) = some (embed_value v) := by
  -- proof here
```

### Option B: Formalization in Coq

Similar approach, perhaps more mature ecosystem for PL metatheory:

```coq
Inductive clair_type : Type :=
  | TBase : base_type -> clair_type
  | TArrow : clair_type -> clair_type -> clair_type
  | TBelief : clair_type -> clair_type.

Inductive clair_term : Type :=
  | Var : nat -> clair_term
  | Lam : clair_type -> clair_term -> clair_term
  | App : clair_term -> clair_term -> clair_term
  | BeliefIntro : clair_term -> confidence -> provenance -> clair_term
  | BeliefVal : clair_term -> clair_term.

(* Operational semantics *)
Inductive step : clair_term -> clair_term -> Prop := ...

(* Embed System T or PCF *)
Fixpoint embed (t : pcf_term) : clair_term := ...

Theorem turing_complete :
  forall (f : nat -> option nat),
  computable f ->
  exists (t : clair_term),
    forall n, clair_eval t n = f n.
Proof.
  (* By encoding UTM or showing PCF embedding *)
Admitted.
```

### Option C: Agda with Sized Types

Agda can handle potentially non-terminating computations with coinduction:

```agda
-- Partial computations
data Partial (A : Set) : Set where
  now   : A → Partial A
  later : ∞ (Partial A) → Partial A

-- CLAIR terms can produce partial results
eval : CLAIRTerm → Env → Partial Value
```

### Option D: Reference Interpreter

Write an interpreter in a real language and test it:

```haskell
-- Haskell interpreter for CLAIR
data Belief a = Belief
  { value      :: a
  , confidence :: Double
  , provenance :: Provenance
  , justification :: Justification
  , invalidation :: [Condition]
  }

eval :: Term -> Env -> Belief Value
eval (Var x) env = lookup x env
eval (Lam t body) env = Belief (VClosure env body) 1.0 Literal Axiom []
eval (App f x) env =
  let Belief (VClosure env' body) cf pf jf if_ = eval f env
      Belief vx cx px jx ix = eval x env
  in ...

-- Test: implement factorial, Ackermann, etc.
-- If they work, we have empirical evidence of Turing-completeness
```

### Option E: Translation to Existing Language

Show CLAIR compiles to a known Turing-complete language:

```
CLAIR → Haskell      (known Turing-complete)
CLAIR → JavaScript   (known Turing-complete)
CLAIR → LLVM IR      (known Turing-complete)
```

If the translation is semantics-preserving, and the target is Turing-complete, CLAIR is Turing-complete.

## 9. What Turing-Completeness Means for CLAIR

### Positive Implications

1. **Any algorithm is expressible** — CLAIR doesn't limit what you can compute
2. **Self-hosting is possible** — CLAIR compiler could be written in CLAIR
3. **Universal** — can simulate any other language

### Negative Implications (by Rice's Theorem)

1. **Non-trivial properties are undecidable** — can't decide if a CLAIR program terminates
2. **Confidence may be uncomputable** — some confidence values can't be determined
3. **Invalidation checking may not halt** — checking conditions may diverge

### The Tradeoff

Turing-completeness gives us **expressiveness** but costs us **decidability**.

CLAIR accepts this tradeoff. The tracking system doesn't try to decide everything—it makes undecidability explicit:

```clair
-- This might not terminate
let result = search_until_found(predicate)
  confidence: unknown  -- can't compute
  invalidation: {timeout(10.seconds)}  -- practical bound
```

## 10. Summary

| Question | Answer | Proof Method |
|----------|--------|--------------|
| Is CLAIR Turing-complete? | Yes | Encode λ-calculus, PCF, or TM |
| Do beliefs restrict computation? | No | `val` extracts pure computation |
| Can we prove it formally? | Yes | Lean, Coq, Agda formalization |
| What are the consequences? | Undecidability | Rice's theorem applies |

## 11. Next Steps for Formal Verification

1. **Minimal core**: Define the smallest Turing-complete fragment of CLAIR
2. **Formalize in Lean 4**: Syntax, typing, operational semantics
3. **Prove type safety**: Progress + preservation
4. **Prove Turing-completeness**: Embed PCF or System T
5. **Prove belief properties**: Confidence propagation, provenance well-formedness
6. **Extract interpreter**: Get runnable code from the proof

This is a substantial project but entirely feasible with today's tools.
