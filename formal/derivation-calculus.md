# Derivation Calculus

This document formalizes how beliefs are derived from other beliefs in CLAIR.

## 1. Derivation as Structured Inference

Traditional computation:
```
f(x, y) = z
```

CLAIR derivation:
```
derive z from x, y by f
  where z inherits:
    - confidence from x, y
    - provenance linking to x, y
    - justification recording f
    - invalidation conditions from x, y
```

## 2. Formal Definition

### Derivation Judgment

```
b₁, b₂, ..., bₙ ⊢[r] b

"From beliefs b₁ through bₙ, by rule r, derive belief b"
```

### Components of Derived Belief

Given:
- Input beliefs: `bᵢ = ⟨vᵢ, cᵢ, pᵢ, jᵢ, Iᵢ⟩` for i ∈ 1..n
- Rule: `r : (τ₁, ..., τₙ) ⇒ τ` with confidence factor `strength(r) ∈ [0,1]`

The derived belief `b = ⟨v, c, p, j, I⟩` has:

```
v = r(v₁, ..., vₙ)                           -- value: apply rule to values
c = combine(c₁, ..., cₙ, strength(r))         -- confidence: propagate
p = derived(b₁, ..., bₙ, r)                   -- provenance: record inputs
j = rule(r, j₁, ..., jₙ)                      -- justification: combine
I = ⋃ᵢ Iᵢ ∪ invalidation(r)                   -- invalidation: accumulate
```

## 3. Confidence Propagation

### Conservative (Default)
```
combine(c₁, ..., cₙ, s) = s · min(c₁, ..., cₙ)
```

The conclusion is no more confident than the least confident premise, scaled by rule strength.

### Conjunctive
```
combine(c₁, ..., cₙ, s) = s · ∏ᵢ cᵢ
```

For rules where all premises must be true (logical AND).

### Disjunctive
```
combine(c₁, ..., cₙ, s) = s · (1 - ∏ᵢ (1 - cᵢ))
```

For rules where any premise suffices (logical OR).

### Custom
Rules can specify custom propagation:
```
rule division:
  inputs: (x: Belief<Num>, y: Belief<Num>)
  output: Belief<Num>
  value: x.val / y.val
  confidence: min(x.conf, y.conf) · (1 - P(y.val ≈ 0))
  -- confidence decreases if y might be near zero
```

## 4. Derivation Rules

### Primitive Operations

```
───────────────────────────────────────────────── [D-Add]
b₁: Belief<Num>, b₂: Belief<Num> ⊢[+] Belief<Num>


───────────────────────────────────────────────── [D-Eq]
b₁: Belief<τ>, b₂: Belief<τ> ⊢[=] Belief<Bool>


b: Belief<List<τ>>
──────────────────────────────────────────────── [D-Head]
b ⊢[head] Belief<Option<τ>>
-- confidence may decrease if list might be empty
```

### Logical Operations

```
b₁: Belief<Bool>, b₂: Belief<Bool>
─────────────────────────────────────────────── [D-And]
b₁, b₂ ⊢[∧] Belief<Bool>
  conf = c₁ · c₂

b₁: Belief<Bool>, b₂: Belief<Bool>
─────────────────────────────────────────────── [D-Or]
b₁, b₂ ⊢[∨] Belief<Bool>
  conf = c₁ + c₂ - c₁ · c₂
```

### Conditional Derivation

```
b_cond: Belief<Bool>, b_then: Belief<τ>, b_else: Belief<τ>
──────────────────────────────────────────────────────────── [D-If]
b_cond, b_then, b_else ⊢[if] Belief<τ>
  value = if val(b_cond) then val(b_then) else val(b_else)
  conf = conf(b_cond) · conf(selected branch)
```

### Function Application

```
b_f: Belief<τ₁ → τ₂>, b_x: Belief<τ₁>
──────────────────────────────────────────────────────────── [D-App]
b_f, b_x ⊢[apply] Belief<τ₂>
  value = (val(b_f))(val(b_x))
  conf = min(conf(b_f), conf(b_x))
```

## 5. Derivation Trees

A derivation tree records the full history:

```
                    ┌─────────────────────────────────┐
                    │ can_drink: Belief<Bool>         │
                    │ value: true                     │
                    │ conf: 0.95                      │
                    │ just: rule(≥, j₁, j₂)          │
                    └────────────────┬────────────────┘
                                     │
                          ┌──────────┴──────────┐
                          │      [D-Geq]        │
                          │  (≥): (Nat,Nat)→Bool │
                          │  strength: 1.0      │
                          └──────────┬──────────┘
                                     │
               ┌─────────────────────┴─────────────────────┐
               │                                           │
    ┌──────────┴──────────┐                 ┌──────────────┴──────────────┐
    │ user_age            │                 │ drinking_age               │
    │ value: 25           │                 │ value: 21                  │
    │ conf: 0.95          │                 │ conf: 1.0                  │
    │ prov: db.users.age  │                 │ prov: literal              │
    │ just: axiom         │                 │ just: axiom                │
    └─────────────────────┘                 └─────────────────────────────┘
```

## 6. Justification Algebra

Justifications form a term algebra:

```
j ::= axiom                    -- primitive justification
    | rule(r, j₁, ..., jₙ)     -- derived by rule
    | assumption(a)            -- depends on assumption
    | choice(opts, c, reason)  -- result of decision
```

### Operations

**Combination** (used in derivation):
```
j₁ ⊗ j₂ = rule(∧, j₁, j₂)
```

**Weakening** (when confidence drops):
```
weaken(j, reason) = weakened(j, reason)
```

**Querying** (extract assumptions):
```
assumptions(axiom) = ∅
assumptions(rule(r, j₁, ..., jₙ)) = ⋃ᵢ assumptions(jᵢ)
assumptions(assumption(a)) = {a}
assumptions(choice(opts, c, r)) = assumptions_from_criteria(c)
```

## 7. Invalidation Propagation

### Accumulation Rule
```
invalidation(derive b₁, ..., bₙ by r) = ⋃ᵢ inv(bᵢ) ∪ inv(r)
```

Derived beliefs inherit all invalidation conditions from premises, plus any rule-specific conditions.

### Common Invalidation Conditions

```
inv_input_changed(source)      -- external input changed
inv_assumption_false(a)        -- assumption no longer holds
inv_confidence_below(c, thresh) -- confidence dropped too low
inv_constraint_violated(φ)     -- constraint no longer satisfied
inv_time_elapsed(duration)     -- time-based expiry
```

### Checking Invalidation

```
is_invalid(b, world_state) =
  ∃φ ∈ inv(b). evaluate(φ, world_state) = true
```

When a belief is invalid, it should be rederived or flagged for review.

## 8. Derivation vs. Computation

| Aspect | Traditional | CLAIR Derivation |
|--------|-------------|------------------|
| Input | Values | Beliefs |
| Output | Value | Belief |
| Trace | Discarded | Preserved (justification) |
| Confidence | N/A | Propagated |
| Invalidation | N/A | Accumulated |
| Reversibility | One-way | Queryable tree |

## 9. Example: Multi-Step Derivation

```
-- Input beliefs
let name: Belief<String> =
  ⟨"Alice", 1.0, input("user"), axiom, {input_changed("user")}⟩

let age: Belief<Nat> =
  ⟨25, 0.9, input("database"), axiom, {input_changed("database")}⟩

let min_age: Belief<Nat> =
  ⟨18, 1.0, literal, axiom, {}⟩

-- Derived beliefs
let is_adult: Belief<Bool> =
  derive age, min_age by (≥)
  -- value: true
  -- conf: 0.9 (limited by age)
  -- just: rule(≥, axiom, axiom)
  -- inv: {input_changed("database")}

let greeting: Belief<String> =
  derive name, is_adult by make_greeting
  where make_greeting(n, adult) =
    if adult then "Welcome, " ++ n else "Sorry, adults only"
  -- value: "Welcome, Alice"
  -- conf: 0.9 (limited by is_adult, which was limited by age)
  -- just: rule(make_greeting, axiom, rule(≥, axiom, axiom))
  -- inv: {input_changed("user"), input_changed("database")}
```

The final greeting belief carries the full derivation history and knows exactly what would invalidate it.

## 10. Optimization: Lazy Derivation Trees

Full derivation trees can be large. Optimizations:

1. **Hash-consing**: Share identical subtrees
2. **Lazy expansion**: Store tree structure, expand on query
3. **Summarization**: For deep trees, summarize intermediate steps
4. **Checkpointing**: Periodically snapshot, reconstruct from checkpoints

```
-- Compact representation
greeting.justification =
  rule(make_greeting,
    ref("j:name"),           -- reference to stored justification
    rule(≥,
      ref("j:age"),
      ref("j:min_age")))
```
