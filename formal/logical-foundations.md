# Logical Foundations of CLAIR

This document traces CLAIR's connections to foundational work in logic, proof theory, and type theory beyond Church-Turing-Gödel-Gentzen.

> **⚠️ Paradigm Shift Note (2026-01-29)**
>
> This document was written when CLAIR was conceived as a programming language.
> CLAIR is now an **IR for reasoning traces** (see `clair-spec.md`).
>
> **Still Applies:**
> - §1 BHK Interpretation (conceptually—beliefs have constructive evidence)
> - §5 Epistemic Modal Logic (graded belief operators map directly to CLAIR)
> - §6 Paraconsistent Logic (CLAIR can track contradictory beliefs)
> - §7 Relevance Logic (justifications must be relevant)
>
> **Overkill / Obsolete:**
> - §2 Curry-Howard (full machinery not needed—content is opaque NL)
> - §3 Martin-Löf Judgments (dependent type machinery not needed)
> - §4 Linear Logic (resource tracking is over-engineered for an IR)
> - §8 Intuitionistic Type Theory (dependent types not applicable)
> - §9 Sequent Calculus (formal proof structure not needed)
> - §10 Category Theory (see archived `categorical-structure.md`)

## 1. BHK Interpretation (Brouwer-Heyting-Kolmogorov)

### The Constructive View

The BHK interpretation gives *meaning* to logical connectives in terms of proofs:

| Formula | BHK Interpretation |
|---------|-------------------|
| P ∧ Q | A proof of P AND a proof of Q |
| P ∨ Q | A proof of P OR a proof of Q (must specify which) |
| P → Q | A function transforming proofs of P into proofs of Q |
| ¬P | A function transforming proofs of P into absurdity |
| ∃x.P(x) | A witness x AND a proof of P(x) |
| ∀x.P(x) | A function from any x to a proof of P(x) |

### Key Difference from Classical Logic

Classical logic allows:
```
¬¬P → P                    (double negation elimination)
P ∨ ¬P                     (law of excluded middle)
((P → Q) → P) → P          (Peirce's law)
```

Constructive logic rejects these. You can't prove existence without a witness. You can't prove P ∨ ¬P without knowing which.

### Relevance to CLAIR

CLAIR beliefs are more constructive than classical:

```clair
-- Classical: "Either P or not P, I don't know which"
-- Constructive: "I have evidence for P" or "I have evidence against P"
-- CLAIR: belief(P, 0.7, evidence_e) or belief(¬P, 0.3, evidence_e')

-- The confidence IS the degree of constructive evidence
-- 0.5 means "I have no evidence either way" (neither P nor ¬P proven)
```

**BHK meets Belief:**
```
belief(P ∧ Q, c) requires: belief(P, c₁) AND belief(Q, c₂)
  -- We have "proofs" (justifications) for both

belief(P ∨ Q, c) requires: belief(P, c₁) OR belief(Q, c₂)
  -- We know WHICH disjunct we believe

belief(P → Q, c) is: a function from belief(P) to belief(Q)
  -- Confidence may decrease: c = f(c_input)

belief(∃x.P(x), c) requires: a witness x AND belief(P(x), c)
  -- We can't believe existence without a witness
```

This makes CLAIR *more* constructive than typical programming—we track the evidence.

---

## 2. Curry-Howard Correspondence

### The Correspondence

Haskell Curry (1934) and William Howard (1969) discovered:

| Logic | Type Theory |
|-------|-------------|
| Proposition | Type |
| Proof | Program/Term |
| P → Q | Function type A → B |
| P ∧ Q | Product type A × B |
| P ∨ Q | Sum type A + B |
| ⊥ (false) | Empty type (Void) |
| ⊤ (true) | Unit type |
| Proof normalization | Computation |

### Proofs as Programs

```haskell
-- A proof of A → B is a function
proof : A -> B
proof a = ... -- transform evidence for A into evidence for B

-- A proof of A ∧ B is a pair
proof : (A, B)
proof = (proof_a, proof_b)

-- A proof of A ∨ B is a tagged value
proof : Either A B
proof = Left proof_a   -- or Right proof_b
```

### Extending Curry-Howard for CLAIR

Standard Curry-Howard: `term : Type` means "term is a proof of Type"

CLAIR extension: `belief : Belief<Type>` means "belief is a *justified belief* about Type"

```
Curry-Howard:     a : A           "a proves A"
CLAIR:            b : Belief<A>   "b is believed with justification"
                  b.value : A     "the believed value"
                  b.just : Just   "the justification (like a proof, but partial)"
                  b.conf : [0,1]  "how strong the justification is"
```

**The key insight:** Curry-Howard proofs are *total*—they fully prove the proposition. CLAIR justifications are *partial*—they may be incomplete, uncertain, or defeasible.

### Curry's Paradox

Curry also discovered a paradox relevant to self-reference:

> Let X = "If X is true, then P"
> Assume X is true.
> Then "If X is true, then P" is true.
> So, by modus ponens with our assumption, P.
> Therefore X → P.
> But that's exactly X! So X is true.
> Therefore P is true.

This proves ANY P from self-referential assumptions.

**For CLAIR:** This is another reason self-referential beliefs are dangerous and must be flagged:

```clair
-- Curry-style paradox in beliefs:
let x : Belief<X> = belief
  value: (val(x) → P)
  justification: ???  -- circular!

-- CLAIR must reject this as ill-formed
```

---

## 3. Martin-Löf's Judgments

### Judgments vs Propositions

Per Martin-Löf distinguished:

| Judgment | Meaning |
|----------|---------|
| A : Type | A is a well-formed type |
| a : A | a is a term of type A |
| A = B : Type | A and B are equal types |
| a = b : A | a and b are equal terms of type A |

**Crucially:** Judgments are *asserted*, not proved. They're the level at which we speak.

### Four Forms of Judgment

```
A type           -- A is a type
A = B type       -- A and B are the same type
a : A            -- a is a term of type A
a = b : A        -- a and b are the same term of type A
```

### Hypothetical Judgments

```
x : A ⊢ B type         -- assuming x:A, B is a type (dependent types)
x : A ⊢ b : B          -- assuming x:A, b is a term of type B
```

### Relevance to CLAIR

CLAIR adds a new form of judgment:

```
Standard:     a : A              "a is a term of type A"
CLAIR:        b : Belief<A>      "b is a belief about type A"
              b ⊣ (c, p, j, I)   "b is held with confidence c, provenance p,
                                  justification j, invalidation I"
```

This is a **meta-judgment** about epistemic state, not just typing.

**Martin-Löf's meaning explanations:**

Martin-Löf gave *meaning explanations*—informal explanations of what judgments mean. For CLAIR:

```
Meaning of "b : Belief<A>":
  We hold a belief about something of type A.

Meaning of "b ⊣ (c, p, j, I)":
  We hold this belief with:
  - confidence c (how strongly)
  - provenance p (based on what)
  - justification j (why)
  - invalidation I (until when)

Meaning of "derive b₁...bₙ by r":
  From beliefs b₁...bₙ, using rule r, we form a new belief.
  The new belief's metadata is computed from the inputs.
```

---

## 4. Linear Logic (Girard, 1987)

### The Key Idea

Classical/intuitionistic logic allows:
- **Contraction:** Use a hypothesis multiple times
- **Weakening:** Ignore a hypothesis

Linear logic controls these. Resources are used *exactly once*.

### Linear Connectives

| Connective | Name | Meaning |
|------------|------|---------|
| A ⊗ B | Tensor | Both A and B (use both) |
| A ⅋ B | Par | A or B (but connected) |
| A ⊕ B | Plus | A or B (choose one) |
| A & B | With | A and B (choose one to use) |
| !A | Of course | Unlimited use of A |
| ?A | Why not | Lazily available A |
| A ⊸ B | Lollipop | A consumed to produce B |

### Relevance to CLAIR

Linear logic tracks *resource usage*. CLAIR tracks *epistemic state*. There's a connection:

**Beliefs as resources:**
```clair
-- A belief, once used in derivation, is "consumed" in a sense:
-- Its confidence contributes to the derived belief
-- Its provenance is recorded
-- Its invalidation propagates

-- Linear typing could enforce:
-- "This input belief was used exactly once in this derivation"
```

**Confidence as a resource:**
```clair
-- Confidence "flows" through derivation
-- It can't be created from nothing (no weakening of confidence)
-- It can't be duplicated without cost (multiplication ≤ original)

derive a, b by (∧)
-- conf(result) = conf(a) × conf(b) ≤ min(conf(a), conf(b))
-- Confidence is "consumed" and reduced
```

**Exponentials for reusable beliefs:**
```clair
-- Some beliefs can be used unlimited times (axioms, stable facts)
-- Like !A in linear logic

axiom pi : !Belief<Float>  -- can use unlimited times
-- vs
input x : Belief<Float>    -- use once, invalidation may trigger
```

This suggests a **linear belief calculus** where resource-sensitive reasoning is explicit:

```
A ⊸ B    "consuming belief A produces belief B"
!A       "belief A can be used unlimitedly"
A ⊗ B    "we have both beliefs and must use both"
```

---

## 5. Epistemic Modal Logic

### Modal Operators for Knowledge and Belief

Standard modal logic has □ (necessity) and ◇ (possibility).

Epistemic logic specializes these:

| Operator | Reading |
|----------|---------|
| Kₐ P | Agent a knows P |
| Bₐ P | Agent a believes P |
| ¬Kₐ ¬P | P is consistent with a's knowledge |

### Properties of Knowledge vs Belief

**Knowledge (typically):**
```
Kₐ P → P           (truth: you can only know true things)
Kₐ P → Kₐ Kₐ P     (positive introspection: you know what you know)
¬Kₐ P → Kₐ ¬Kₐ P   (negative introspection: you know what you don't know)
```

**Belief (typically):**
```
Bₐ P → P           NOT required (you can believe falsely)
Bₐ P → Bₐ Bₐ P     Might hold (you believe you believe)
¬Bₐ P → Bₐ ¬Bₐ P   Might not hold (you might not know what you don't believe)
```

### CLAIR as Epistemic Logic

CLAIR beliefs are closest to **graded belief**:

```
Bₐ,c P    "Agent a believes P with confidence c"
```

With CLAIR's additions:
```
Bₐ,c,p,j,I P    "Agent a believes P with confidence c,
                 provenance p, justification j, invalidation I"
```

**Possible worlds interpretation:**

In Kripke semantics, belief is relative to accessible possible worlds:
```
Bₐ P holds at world w iff P holds at all worlds accessible from w via a's belief relation
```

For CLAIR:
```
Bₐ,c P holds at world w iff
  P holds at c-fraction of worlds accessible from w
  (or some weighted measure of accessible worlds)
```

This gives a semantic grounding to confidence.

### Multi-Agent Epistemic Logic

When multiple AI agents collaborate:
```
B_claude P      -- Claude believes P
B_human P       -- Human believes P
B_claude B_human P  -- Claude believes that human believes P
```

CLAIR could track:
```clair
belief(P, 0.9, decided_by("claude"), reviewed_by("human"))
-- Provenance shows which agent contributed
```

---

## 6. Paraconsistent Logic

### The Problem of Contradiction

Classical logic has *ex falso quodlibet*: from a contradiction, anything follows:
```
P ∧ ¬P ⊢ Q    (for any Q)
```

This makes classical logic "explosive"—one contradiction destroys the system.

### Paraconsistent Response

Paraconsistent logics reject explosion. They allow reasoning with inconsistent information without everything becoming trivially provable.

### Relevance to CLAIR

CLAIR may hold contradictory beliefs:
```clair
belief(P, 0.6, source_a, ...)
belief(¬P, 0.5, source_b, ...)
```

This isn't a system failure—it's a realistic state:
- Different sources disagree
- We haven't resolved the conflict
- We track both beliefs with their confidences

**Paraconsistent confidence:**
```clair
-- If we believe both P and ¬P, confidence should reflect tension:
conf(P) + conf(¬P) > 1  -- overconfidence, contradiction
conf(P) + conf(¬P) < 1  -- underconfidence, uncertainty
conf(P) + conf(¬P) = 1  -- calibrated (ideal but rare)
```

**Belief revision vs paraconsistency:**
```clair
-- Option 1: Revise beliefs to remove contradiction
-- Option 2: Keep both, flag as inconsistent, lower confidence

type ConsistencyStatus :=
  | Consistent
  | Inconsistent (conflicting: List<Belief>)
  | Unknown
```

---

## 7. Relevance Logic

### The Problem of Relevance

Classical logic allows:
```
P ⊢ Q → P        (if P, then Q implies P, regardless of Q)
P, ¬P ⊢ Q        (from contradiction, anything—but Q is irrelevant!)
```

Relevance logic requires premises to be *actually used* in conclusions.

### Relevance to CLAIR

CLAIR justifications should be **relevant**:
```clair
-- Bad: justification doesn't actually support the belief
let b = belief
  value: "2 + 2 = 4"
  justification: "the sky is blue"  -- irrelevant!

-- Good: justification actually supports
let b = belief
  value: "2 + 2 = 4"
  justification: axiom(peano_arithmetic)  -- relevant
```

**Enforcing relevance:**
```clair
derive a, b by rule
-- Rule must actually USE a and b
-- If rule ignores b, the derivation is invalid

-- This connects to linear logic:
-- If a resource isn't used, it's suspicious
```

---

## 8. Intuitionistic Type Theory and Propositions-as-Types

### Beyond Simple Curry-Howard

Full intuitionistic type theory (Martin-Löf) extends Curry-Howard:

| Type Theory | Logic |
|-------------|-------|
| Π(x:A).B(x) | ∀x:A.B(x) (dependent function) |
| Σ(x:A).B(x) | ∃x:A.B(x) (dependent pair) |
| Id(A, a, b) | a = b (identity/equality type) |
| W-types | Well-founded trees (induction) |

### Propositions as Types, Proofs as Programs

```
Π(x:A).B(x)    -- A function that, given x:A, produces a B(x)
               -- This IS a proof of ∀x:A.B(x)

Σ(x:A).B(x)    -- A pair (x, p) where x:A and p:B(x)
               -- This IS a proof of ∃x:A.B(x)
               -- The witness is explicit!
```

### CLAIR Extension

```
-- Standard dependent type:
Π(x:A).B(x)    -- for all x:A, a B(x)

-- CLAIR belief type:
Π(x:A).Belief<B(x)>    -- for all x:A, a belief about B(x)

-- Or even:
Belief<Π(x:A).B(x)>    -- a belief about the universal statement
```

**Existential beliefs must have witnesses:**
```clair
-- Can't just believe ∃x.P(x) without a witness
-- This is the constructive requirement

belief(∃x.P(x), 0.9, ...)  -- must include the witness x
  witness: actual_x
  justification: proof_P(actual_x)
```

---

## 9. Sequent Calculus and Proof Structure

### Gentzen's Sequent Calculus

Sequents have the form:
```
Γ ⊢ Δ

"From assumptions Γ, conclude (one of) Δ"
```

Rules are structural (about sequent manipulation) or logical (about connectives).

### Structural Rules

```
Γ ⊢ Δ
────────── (weakening left)
Γ, A ⊢ Δ

Γ, A, A ⊢ Δ
─────────── (contraction left)
Γ, A ⊢ Δ

Γ, A, B ⊢ Δ
─────────── (exchange left)
Γ, B, A ⊢ Δ
```

### CLAIR as a Sequent System

```
Beliefs ⊢_track NewBelief

"From existing beliefs, track a new belief"
```

**CLAIR structural rules:**
```
B ⊢_track b
─────────────────── (confidence-weakening)
B ⊢_track b' where conf(b') ≤ conf(b)

-- Confidence can decrease but not increase through structure

B ⊢_track b
─────────────────────────────────── (provenance-extension)
B ⊢_track b' where prov(b') ⊇ prov(b)

-- Provenance can only grow (we don't lose track of origins)

B ⊢_track b
──────────────────────────────────────── (invalidation-extension)
B ⊢_track b' where inv(b') ⊇ inv(b)

-- Invalidation conditions accumulate (derived beliefs are more fragile)
```

---

## 10. Category Theory Connection (Brief)

### Functors and Natural Transformations

If we view:
- Types as objects
- Functions as morphisms

Then Belief is a **functor**:
```
Belief : Type → Type
Belief(A) = Belief<A>

-- And for f : A → B:
Belief(f) : Belief<A> → Belief<B>
Belief(f)(b) = derive b by f
```

### Monad-like Structure?

Is Belief a monad?
```
return : A → Belief<A>
return a = axiom(a)  -- belief with confidence 1.0

(>>=) : Belief<A> → (A → Belief<B>) → Belief<B>
b >>= f = derive b, (f (val b)) by composition
```

But this doesn't quite work:
- Confidence doesn't preserve monad laws cleanly
- `return` should give confidence 1.0, but `>>=` might lower it

**Graded monad?**
```
-- Indexed by confidence level
Belief_c<A>  where c ∈ [0,1]

return : A → Belief_1<A>
(>>=) : Belief_c<A> → (A → Belief_d<B>) → Belief_{c×d}<B>
```

This is a **graded monad** where the grade tracks confidence.

---

## 11. Summary Table

| Logic/Theory | Key Idea | CLAIR Connection |
|--------------|----------|------------------|
| BHK | Proofs are constructions | Beliefs have constructive witnesses |
| Curry-Howard | Types ↔ Propositions | Belief types extend the correspondence |
| Martin-Löf | Judgments vs propositions | CLAIR adds epistemic judgments |
| Linear Logic | Resources used exactly once | Confidence as consumable resource |
| Epistemic Logic | Kₐ P, Bₐ P | CLAIR is graded belief Bₐ,c P |
| Paraconsistent | Handle contradictions | CLAIR tracks conflicting beliefs |
| Relevance Logic | Premises must be used | Justifications must be relevant |
| Sequent Calculus | Proof structure | Derivation rules, cut-free justifications |

---

## 12. Open Questions

### For Future Formalization

1. **What is the exact categorical structure of Belief?**
   - Graded monad? Indexed monad? Something else?

2. **Can we give a Kripke semantics for CLAIR?**
   - Possible worlds = possible states of knowledge
   - Confidence = measure on accessible worlds

3. **Is there a linear belief calculus?**
   - Linear types for resource-sensitive belief tracking
   - !Belief<A> for reusable beliefs

4. **How do dependent types interact with beliefs?**
   - Belief<Π(x:A).B(x)> vs Π(x:A).Belief<B(x)>
   - When can we distribute?

5. **What is the proof theory of CLAIR?**
   - Cut elimination for belief derivations?
   - Normal forms for justifications?

---

## 13. References

### Primary

- **Brouwer, L.E.J.** (1907). *Over de Grondslagen der Wiskunde*. (Foundations of intuitionism)

- **Heyting, A.** (1956). *Intuitionism: An Introduction*. North-Holland.

- **Kolmogorov, A.N.** (1932). "Zur Deutung der intuitionistischen Logik." *Mathematische Zeitschrift*, 35, 58-65.

- **Curry, H.B.** (1934). "Functionality in Combinatory Logic." *Proceedings of the National Academy of Sciences*, 20, 584-590.

- **Howard, W.A.** (1980). "The Formulae-as-Types Notion of Construction." In *To H.B. Curry: Essays on Combinatory Logic*.

- **Martin-Löf, P.** (1984). *Intuitionistic Type Theory*. Bibliopolis.

- **Girard, J.-Y.** (1987). "Linear Logic." *Theoretical Computer Science*, 50, 1-102.

- **Hintikka, J.** (1962). *Knowledge and Belief*. Cornell University Press. (Epistemic logic)

- **Priest, G.** (2006). *In Contradiction*. Oxford University Press. (Paraconsistent logic)

- **Anderson, A.R. & Belnap, N.D.** (1975). *Entailment: The Logic of Relevance and Necessity*. Princeton.

### Secondary

- **Troelstra, A.S. & van Dalen, D.** (1988). *Constructivism in Mathematics* (2 vols). North-Holland.

- **Sorensen, M.H. & Urzyczyn, P.** (2006). *Lectures on the Curry-Howard Isomorphism*. Elsevier.

- **Restall, G.** (2000). *An Introduction to Substructural Logics*. Routledge. (Linear, relevance logic)

- **Fagin, R. et al.** (1995). *Reasoning About Knowledge*. MIT Press. (Multi-agent epistemic logic)
