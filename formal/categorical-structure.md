# Categorical Structure of Belief

This document formalizes the categorical and type-theoretic structure of CLAIR's Belief type.

## 1. Belief as a Graded Monad

### Standard Monads (Review)

A monad on a category C is a triple (T, η, μ) where:
- T : C → C is an endofunctor
- η : Id → T is the unit (return)
- μ : T∘T → T is multiplication (join)

Satisfying:
```
μ ∘ Tμ = μ ∘ μT        (associativity)
μ ∘ Tη = μ ∘ ηT = id   (unit laws)
```

In Haskell notation:
```haskell
return : a → T a
(>>=)  : T a → (a → T b) → T b

-- Laws:
return a >>= f  ≡  f a                    (left identity)
m >>= return    ≡  m                      (right identity)
(m >>= f) >>= g ≡  m >>= (λx → f x >>= g) (associativity)
```

### Why Belief Isn't a Standard Monad

If we try:
```
return : A → Belief<A>
return a = belief(a, 1.0, literal, axiom, {})

(>>=) : Belief<A> → (A → Belief<B>) → Belief<B>
b >>= f = let b' = f (val b) in
          belief(val b',
                 conf b × conf b',  -- confidence multiplies
                 derived(prov b, prov b'),
                 rule(>>=, just b, just b'),
                 inv b ∪ inv b')
```

Check left identity:
```
return a >>= f
= belief(a, 1.0, ...) >>= f
= let b' = f a in belief(val b', 1.0 × conf b', ...)
= let b' = f a in belief(val b', conf b', ...)
≡ f a  ✓ (if we ignore provenance/justification differences)
```

Check right identity:
```
b >>= return
= let b' = return (val b) in belief(val b', conf b × 1.0, ...)
= belief(val b, conf b, derived(prov b, literal), ...)
≢ b  ✗ (provenance changed!)
```

The laws fail because metadata accumulates. This is intentional—we *want* to track derivation history.

### Graded Monads

A **graded monad** (also called indexed or parametric monad) is indexed by a monoid (M, ·, 1):

```
T : M → (C → C)

η : Id → T(1)
μ : T(m) ∘ T(n) → T(m · n)
```

For CLAIR, the grading monoid is **([0,1], ×, 1)**:
- Elements are confidence values in [0,1]
- Operation is multiplication
- Unit is 1.0

### Belief as a Graded Monad

```
Belief : [0,1] → (Type → Type)
Belief(c)(A) = Belief_c<A>

-- A belief with confidence exactly c
Belief_c<A> = { b : Belief<A> | conf(b) = c }
```

**Unit (η):**
```
η : A → Belief_1<A>
η a = belief(a, 1.0, literal, axiom, {})
```

**Multiplication (μ):**
```
μ : Belief_c<Belief_d<A>> → Belief_{c×d}<A>
μ bb = belief(val (val bb),
              c × d,
              derived(prov bb, prov (val bb)),
              rule(μ, just bb, just (val bb)),
              inv bb ∪ inv (val bb))
```

**Bind (derived):**
```
(>>=) : Belief_c<A> → (A → Belief_d<B>) → Belief_{c×d}<B>
b >>= f = μ (fmap f b)
```

### Graded Monad Laws

```
-- Left identity (graded)
η a >>= f : Belief_{1×d}<B>
         = Belief_d<B>
         ≡ f a  ✓

-- Right identity (graded)
b >>= η : Belief_{c×1}<A>
        = Belief_c<A>
        ≡ b  ✓ (up to provenance equivalence)

-- Associativity (graded)
(b >>= f) >>= g : Belief_{(c×d)×e}<C>
b >>= (λx → f x >>= g) : Belief_{c×(d×e)}<C>
-- Equal because × is associative on [0,1]  ✓
```

The laws hold **up to provenance/justification equivalence** if we consider beliefs with the same value and confidence as equivalent.

---

## 2. The Confidence Monoid

### Definition

```
Confidence = ([0,1], ×, 1)

where:
  [0,1] = { c ∈ ℝ | 0 ≤ c ≤ 1 }
  × = multiplication
  1 = multiplicative identity
```

### Properties

```
Associativity:  (a × b) × c = a × (b × c)  ✓
Identity:       1 × a = a × 1 = a          ✓
Commutativity:  a × b = b × a              ✓ (bonus)
```

This is actually a **commutative monoid**.

### Absorption

```
0 × a = a × 0 = 0
```

Zero confidence is absorbing—any derivation involving a zero-confidence belief has zero confidence.

### Alternative: Min Monoid

We could instead use:
```
Confidence_min = ([0,1], min, 1)
```

This is also a monoid:
```
Associativity:  min(min(a,b), c) = min(a, min(b,c))  ✓
Identity:       min(1, a) = min(a, 1) = a            ✓
Commutativity:  min(a, b) = min(b, a)                ✓
Idempotency:    min(a, a) = a                        ✓ (bonus)
```

With min, confidence is the minimum of all inputs—more conservative.

### Semiring Structure

For handling both conjunction (×) and disjunction (⊕), we might want a semiring:

```
Confidence_semiring = ([0,1], ⊕, ×, 0, 1)

where:
  a ⊕ b = a + b - a×b   (probabilistic OR)
  a × b = a × b          (probabilistic AND)
  0 = additive identity (certain falsity)
  1 = multiplicative identity (certain truth)
```

This satisfies semiring laws:
```
(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)     ✓
a ⊕ 0 = 0 ⊕ a = a             ✓
a ⊕ b = b ⊕ a                 ✓

(a × b) × c = a × (b × c)     ✓
a × 1 = 1 × a = a             ✓
a × b = b × a                 ✓

a × (b ⊕ c) = (a × b) ⊕ (a × c)  ✓ (distributivity)
a × 0 = 0 × a = 0             ✓ (annihilation)
```

---

## 3. Provenance as a Semilattice

### Definition

```
Provenance forms a join-semilattice under combination:

p₁ ⊔ p₂ = combined(p₁, p₂)
```

### Ordering

```
p₁ ⊑ p₂  iff  p₂ "contains" p₁'s information

literal ⊑ derived(literal, ...) ⊑ derived(derived(...), ...)
```

More derived = more provenance information.

### Properties

```
Idempotency:    p ⊔ p = p              (combining with self is identity)
Commutativity:  p₁ ⊔ p₂ = p₂ ⊔ p₁      (order doesn't matter)
Associativity:  (p₁ ⊔ p₂) ⊔ p₃ = p₁ ⊔ (p₂ ⊔ p₃)
```

### Provenance Graphs

Provenance forms a DAG (directed acyclic graph):
```
        result
         /  \
        /    \
    derived  derived
      /  \      |
     /    \     |
  input  literal input
```

The semilattice operation merges DAGs.

---

## 4. Justification as a Free Algebra

### Definition

Justifications form a free algebra over justification constructors:

```
data Justification where
  Axiom     : Justification
  Assumed   : Assumption → Justification
  External  : Source → Justification
  Rule      : RuleName → List Justification → Justification
  Choice    : List Option → Criteria → Justification
```

### No Equations

Unlike confidence (which has algebraic laws), justifications are **syntactic**—we don't quotient by equations. Two justifications are equal iff they're structurally identical.

This preserves full derivation history.

### Tree Structure

```
            Rule(verify, [j₁, j₂, j₃])
                  /    |    \
                 /     |     \
               j₁     j₂      j₃
              /       |        \
           Axiom   Rule(...)  External(db)
                      |
                    Assumed(a₁)
```

### Querying Justifications

```
-- Extract all assumptions
assumptions : Justification → Set Assumption
assumptions Axiom = {}
assumptions (Assumed a) = {a}
assumptions (External _) = {}
assumptions (Rule _ js) = ⋃ (map assumptions js)
assumptions (Choice _ _) = ... -- from criteria

-- Depth of justification
depth : Justification → Nat
depth Axiom = 0
depth (Assumed _) = 0
depth (External _) = 0
depth (Rule _ js) = 1 + max (map depth js)
depth (Choice _ _) = 1
```

---

## 5. Invalidation as a Boolean Algebra

### Definition

Invalidation conditions form a Boolean algebra:

```
Invalidation = ℘(Condition)  -- powerset of conditions

Operations:
  ∅           -- no invalidation (axioms)
  I₁ ∪ I₂     -- either set of conditions triggers
  I₁ ∩ I₂     -- both sets must trigger
  Iᶜ          -- complement (rarely used)
```

### Properties

Standard Boolean algebra laws hold.

### Propagation Rule

Derivation accumulates invalidation:
```
inv(derive b₁...bₙ by r) = inv(b₁) ∪ ... ∪ inv(bₙ) ∪ inv(r)
```

This is the join operation—invalidation only grows.

### Condition Evaluation

```
triggered : Invalidation → WorldState → Bool
triggered I w = ∃φ ∈ I. eval(φ, w)

valid : Belief<A> → WorldState → Bool
valid b w = ¬(triggered (inv b) w)
```

---

## 6. The Full Structure

### Belief Functor

```
Belief : [0,1] × Prov × Just × Inv → Type → Type

-- With all indices explicit:
Belief(c, p, j, I)(A) = { value : A,
                          confidence : c,
                          provenance : p,
                          justification : j,
                          invalidation : I }
```

### Simplified Graded Version

For practical use, we often care most about confidence:

```
Belief_c<A> = { b : Belief<A> | conf(b) = c }
```

With operations:
```
pure : A → Belief_1<A>
fmap : (A → B) → Belief_c<A> → Belief_c<B>
(>>=) : Belief_c<A> → (A → Belief_d<B>) → Belief_{c×d}<B>
```

### Full Indexed Version

With all indices:
```
Belief_{c,p,j,I}<A>

pure : A → Belief_{1, literal, axiom, ∅}<A>

fmap : (A → B) → Belief_{c,p,j,I}<A> → Belief_{c,p,j,I}<B>

(>>=) : Belief_{c₁,p₁,j₁,I₁}<A>
      → (A → Belief_{c₂,p₂,j₂,I₂}<B>)
      → Belief_{c₁×c₂, p₁⊔p₂, Rule(>>=,[j₁,j₂]), I₁∪I₂}<B>
```

---

## 7. Linear Structure

### Beliefs as Linear Resources

In a linear setting, beliefs are used exactly once:

```
-- Linear function type
(⊸) : Belief<A> ⊸ Belief<B>

-- Usage: the input belief is consumed
```

### Exponentials for Reusable Beliefs

```
!Belief<A>  -- a belief that can be used unlimited times

-- Promotion: stable beliefs can be reused
promote : Belief_1<A> → !Belief<A>
-- Only confidence-1 beliefs can be promoted (axioms, proven facts)

-- Dereliction: use a reusable belief once
derelict : !Belief<A> → Belief<A>
```

### Linear Derivation

```
-- Linear derivation consumes inputs
derive_linear : Belief<A> ⊸ Belief<B> ⊸ (A → B → C) → Belief<C>

-- After derivation, input beliefs are "spent"
-- Their confidence has been transferred to the output
```

### Confidence as Linear Resource

```
-- Confidence is consumed through derivation
-- Total confidence is not conserved (it decreases)
-- But it can't be created from nothing

conf(derive a b by f) ≤ min(conf a, conf b)
```

---

## 8. Dependent Types and Beliefs

### Dependent Belief Types

```
-- A belief about a dependent type
Belief<Π(x:A).B(x)>

-- vs a dependent function returning beliefs
Π(x:A).Belief<B(x)>
```

These are different!

### Distribution Laws

**Can we distribute Belief over Π?**
```
distribute : Belief<Π(x:A).B(x)> → Π(x:A).Belief<B(x)>
distribute bf = λx. derive bf by (apply x)

-- This works: we get a belief about B(x) for each x
-- But confidence is the same for all x (from bf)
```

**Can we collect?**
```
collect : Π(x:A).Belief<B(x)> → Belief<Π(x:A).B(x)>

-- This is harder:
-- - What's the confidence? (infimum over all x?)
-- - What's the provenance? (union over all x?)
-- - For infinite A, this may not be computable
```

### Dependent Sums

```
Belief<Σ(x:A).B(x)>  -- belief about an existential
-- Must have a witness! (constructive)

-- Contains:
-- - witness : A
-- - belief about B(witness)
```

---

## 9. The Belief Category

### Objects and Morphisms

Define a category **Belief**:

```
Objects: Types A, B, C, ...

Morphisms: A → B in Belief are functions
  f : Belief<A> → Belief<B>
  that preserve structure appropriately
```

### Belief-Preserving Morphisms

A morphism f : Belief<A> → Belief<B> is **belief-preserving** if:
```
conf(f(b)) ≤ conf(b)           -- confidence can only decrease
prov(f(b)) ⊒ prov(b)           -- provenance can only grow
just(f(b)) contains just(b)    -- justification extends
inv(f(b)) ⊇ inv(b)             -- invalidation accumulates
```

### Composition

```
(g ∘ f)(b) = g(f(b))

-- Confidence: conf(g(f(b))) ≤ conf(f(b)) ≤ conf(b)  ✓
-- Provenance: monotonically increases  ✓
-- Justification: extends  ✓
-- Invalidation: accumulates  ✓
```

### Identity

```
id : Belief<A> → Belief<A>
id b = b

-- Preserves all properties trivially  ✓
```

### Functor from Type to Belief

```
F : Type → Belief
F(A) = Belief<A>
F(f : A → B) = fmap f : Belief<A> → Belief<B>
```

---

## 10. Summary of Algebraic Structures

| Component | Structure | Operation | Identity |
|-----------|-----------|-----------|----------|
| Confidence | Commutative monoid | × (multiply) | 1.0 |
| Confidence (alt) | Commutative monoid | min | 1.0 |
| Confidence (full) | Semiring | ⊕, × | 0, 1 |
| Provenance | Join-semilattice | ⊔ (combine) | literal |
| Justification | Free algebra | constructors | — |
| Invalidation | Boolean algebra | ∪, ∩, ¬ | ∅ |
| Belief | Graded monad | >>= | pure |

### The Combined Structure

```
Belief : GradedMonad
  graded by: ([0,1], ×, 1)
  with:
    provenance accumulating via ⊔
    justification accumulating via tree extension
    invalidation accumulating via ∪
```

---

## 11. Formal Definitions (For Reference)

### Definition: Graded Monad

A graded monad over a monoid (M, ·, 1) on category C is:
- A family of endofunctors T_m : C → C for each m ∈ M
- A natural transformation η : Id → T_1
- Natural transformations μ_{m,n} : T_m ∘ T_n → T_{m·n}

Satisfying coherence conditions analogous to monad laws.

### Definition: Belief Graded Monad

```
Belief : GradedMonad([0,1], ×, 1)(Type)

Belief_c : Type → Type
Belief_c(A) = { b : RawBelief(A) | conf(b) = c }

η_A : A → Belief_1(A)
η_A(a) = (a, 1.0, literal, axiom, {})

μ_{c,d} : Belief_c(Belief_d(A)) → Belief_{c×d}(A)
μ_{c,d}(bb) = (val(val(bb)), c×d, prov(bb)⊔prov(val(bb)), ...)
```

### Theorem: Graded Monad Laws Hold

```
-- Left unit
μ_{1,d} ∘ η_{Belief_d(A)} = id_{Belief_d(A)}

-- Right unit
μ_{c,1} ∘ Belief_c(η_A) = id_{Belief_c(A)}

-- Associativity
μ_{c·d,e} ∘ μ_{c,d}_{Belief_e(A)} = μ_{c,d·e} ∘ Belief_c(μ_{d,e})
```

Proof: By computation, using associativity of × on [0,1]. ∎

---

## 12. Open Problems

1. **Full dependent belief types**: What are the correct rules for Belief<Π> and Belief<Σ>?

2. **Linear belief logic**: Formalize the linear type structure with !Belief.

3. **Categorical semantics**: Is there a topos or other categorical model?

4. **Graded comonads**: Beliefs also have a comonadic structure (extract, extend)?

5. **Higher grades**: What if confidence is in a more complex structure than [0,1]?
