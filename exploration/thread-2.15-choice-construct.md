# Thread 2.15: The Choice Construct for Justification Logic Compatibility

> **Status**: Substantially explored (Session 59)
> **Task**: 2.15 Add Choice construct for JL compatibility
> **Question**: Should CLAIR add a JL-style sum/choice operation distinct from aggregation? If so, what are its semantics?
> **Prior Work**: Thread 2.4 (JL connection), Thread 2.18 (conservative extension), Thread 2.22 (Curry-Howard terms), Thread 2.11 (aggregation)

---

## 1. The Problem

### 1.1 Background: Two Kinds of "Multiple Justifications"

When multiple justifications support a conclusion, there are fundamentally **two different situations**:

**Situation A: Independent Evidence (Aggregation)**
- Multiple independent sources each provide evidence for the same conclusion
- Example: Three independent witnesses all saw the suspect at the scene
- Combined confidence INCREASES: 0.6 ⊕ 0.6 ⊕ 0.6 = 0.936
- CLAIR's `aggregate` operation models this

**Situation B: Alternative Justifications (Choice)**
- Multiple sufficient justifications exist; any one of them would suffice
- Example: I can prove the theorem using induction OR using contradiction
- Combined confidence: the MAXIMUM of the alternatives
- JL's `+` (sum) operation models this

**The gap**: CLAIR has aggregation but lacks choice. Thread 2.4 and Thread 2.18 both identified this as a significant semantic gap.

### 1.2 Why This Matters

From Thread 2.18 (Conservative Extension):
> "JL's sum `t + s` is 'any suffices'—confidence = max(component confidences). CLAIR's aggregation is 'both contribute'—confidence = c₁ ⊕ c₂ (probabilistic OR). The semantics are fundamentally different."

From Thread 2.4:
> "Neither subsumes the other: JL sum doesn't increase 'strength', while CLAIR aggregate is strictly about same-conclusion evidence, not alternative justifications."

**Without Choice, CLAIR cannot faithfully represent**:
- "I believe P because A justifies it (or B would work too)"
- Proof alternatives where any proof suffices
- Fallback justifications when primary justification is uncertain
- The JL fragment (breaking conservative extension guarantees)

### 1.3 The Design Question

> Should CLAIR add a Choice construct? If so:
> 1. What are the precise semantics (confidence, provenance, justification)?
> 2. How does Choice interact with other CLAIR operations (derivation, defeat, aggregation)?
> 3. What are the type-theoretic implications (Curry-Howard correspondence)?
> 4. How does it affect decidability?

---

## 2. Prior Art Survey

### 2.1 Artemov's Justification Logic Sum (+)

In JL (LP - Logic of Proofs), the sum operation `+` has these axioms:

**Sum Axioms (Monotonicity)**:
```
t : φ → (t + s) : φ
s : φ → (t + s) : φ
```

**Interpretation**: "If t justifies φ, then t + s also justifies φ (for any s)."

**Key Properties**:
- **Monotonic**: Adding alternatives never weakens justification
- **Ungraded**: JL has no confidence; t + s either justifies or doesn't
- **Choice semantics**: t + s represents "t OR s, whichever works"
- **Idempotent for provability**: t + t ≡ t (for justification purposes)

**Connection to Modal Logic**: JL's sum corresponds to the modal principle □A → □A (reflexivity) combined with frame conditions allowing alternative accessibility paths.

### 2.2 Dung's Argumentation: Alternative Attack Lines

In abstract argumentation frameworks (Dung 1995), an argument can be defended by multiple counterarguments:

```
A is acceptable iff every attacker B has some counterattacker C
```

The "some" here is **choice semantics**: any defender suffices.

**CLAIR analog**: If belief B is under attack from D, and B has multiple potential defeaters-of-D (E₁, E₂, ...), any one sufficing is choice, not aggregation.

### 2.3 Game Theory: Strategy Alternatives

In game-theoretic semantics (Lorenzen games, dialogue logic):
- Proponent has **choice** among moves at OR-nodes
- Opponent has **choice** among moves at AND-nodes

A winning strategy exists iff there exists SOME branch the proponent can choose that leads to winning (choice), not that ALL branches work (conjunction).

### 2.4 Type Theory: Sum Types vs Product Types

In the Curry-Howard correspondence:
- **Product types** (A × B) correspond to conjunction: must have both
- **Sum types** (A + B) correspond to disjunction: have one or the other

JL's `+` should correspond to a **sum/coproduct** structure, not a product.

**Key insight**: CLAIR's aggregation is more like a "continuous product" (both contribute), while JL's sum is a "continuous coproduct" (either suffices).

### 2.5 Fuzzy Logic: T-Conorms for Disjunction

In fuzzy logic, the disjunction of truth values uses t-conorms:
- Maximum: max(a, b) — **this is Choice semantics**
- Probabilistic OR: a + b - ab — this is CLAIR's ⊕ (aggregation)

Both are valid t-conorms, but they model different things:
- max: "best case scenario" / "either suffices"
- ⊕: "independent evidence combination" / "survival of doubt"

---

## 3. Design Analysis

### 3.1 Semantics of Choice

**Definition**: A Choice node in CLAIR's justification DAG represents "any of these justifications would suffice for the conclusion."

**Components**:

1. **Value**: All alternatives must justify the same value (or compatible values)
2. **Confidence**: Maximum of alternative confidences
3. **Provenance**: Records that alternatives exist; primary is the maximum-confidence one
4. **Justification**: New node type `Choice { alternatives: List JustificationEdge }`
5. **Invalidation**: Union of invalidation conditions? Or only the selected alternative?

**Confidence Semantics — The Max Rule**:
```
confidence(choice(e₁, e₂, ..., eₙ)) = max(conf(e₁), conf(e₂), ..., conf(eₙ))
```

**Justification**:
- If any alternative suffices, we're as confident as our best option
- This is the "pessimist's interpretation": I could use t or s, so I'm at least as confident as my best justification
- Unlike aggregation, choice does NOT combine evidence—it selects among alternatives

### 3.2 Choice vs Aggregation: Semantic Contrast

| Property | Aggregation (⊕) | Choice (max) |
|----------|-----------------|--------------|
| Interpretation | "Both support" | "Either suffices" |
| Confidence formula | 1 - ∏(1-cᵢ) | max(cᵢ) |
| Adding evidence | Always increases confidence | May not increase (if new < max) |
| Independence assumption | Yes (critical) | No (alternatives, not evidence) |
| JL correspondence | None (novel to CLAIR) | Sum (+) |
| Type-theoretic analog | Product-like | Sum-like |

**Illustrative Example**:

Suppose I have two justifications for "It will rain tomorrow":
- Justification A: Weather model says 70% chance (confidence 0.7)
- Justification B: Barometric pressure dropping (confidence 0.6)

**If independent evidence (Aggregation)**:
```
0.7 ⊕ 0.6 = 1 - 0.3 × 0.4 = 0.88
```
"Both sources support rain; combined we're 88% confident"

**If alternatives (Choice)**:
```
max(0.7, 0.6) = 0.7
```
"Either source suffices to justify my belief; I'm 70% confident (my best source)"

**The difference is REAL**: Aggregation assumes the sources provide independent incremental evidence. Choice assumes they're alternative routes to the same conclusion—using both doesn't give you "more" justification, just redundancy.

### 3.3 When to Use Choice vs Aggregation

**Use Aggregation when**:
- Multiple independent sources observe the same phenomenon
- Each source provides additional evidence beyond the others
- Combining them should increase confidence (Condorcet jury-style)
- Example: Three witnesses, satellite imagery, and DNA evidence

**Use Choice when**:
- Multiple proof methods for the same theorem
- Fallback justifications (if A fails, B still works)
- Redundant systems (any one of three servers can handle request)
- Example: Prove by induction OR by contradiction OR by model theory

### 3.4 Formal Definition

**Syntax Extension**:
```lean
inductive JustificationNode where
  -- ... existing constructors ...
  | choice : List JustificationEdge → JustificationNode
```

**Confidence Computation**:
```lean
def choiceConfidence (alternatives : List JustificationEdge) : Confidence :=
  alternatives.map (fun e => getConfidence e.target)
              .foldl max 0
```

**Type Rule**:
```
Γ ⊢ e₁ : Belief<A>[c₁]   Γ ⊢ e₂ : Belief<A>[c₂]   ...   Γ ⊢ eₙ : Belief<A>[cₙ]
─────────────────────────────────────────────────────────────────────────────────────
            Γ ⊢ choice(e₁, e₂, ..., eₙ) : Belief<A>[max(c₁, c₂, ..., cₙ)]
```

**Sequent Calculus Rule (Choice Introduction)**:
```
Γ ⊢ A @c₁ : j₁    Γ ⊢ A @c₂ : j₂
────────────────────────────────────  [Choice]
   Γ ⊢ A @max(c₁,c₂) : choice(j₁,j₂)
```

**Note**: Unlike aggregation (which can be applied to any two beliefs about the same proposition), choice represents an explicit epistemic stance that "these are alternatives, not cumulative evidence."

---

## 4. Interactions with Other CLAIR Operations

### 4.1 Choice and Derivation

**Question**: How does derivation interact with choice in the premises?

**Case 1: Derivation from a choice**
```
choice(j₁, j₂) : A    k : A → B
───────────────────────────────────
         ? : B
```

**Option A (Preserve choice)**: The derivation has two alternative justifications
```
choice(derive(j₁, k), derive(j₂, k)) : B
confidence = max(c₁ × c_k, c₂ × c_k) = max(c₁, c₂) × c_k
```

**Option B (Collapse choice)**: Just use the best justification
```
derive(choice(j₁, j₂), k) : B
confidence = max(c₁, c₂) × c_k
```

**Analysis**: Both give the same confidence. Option A preserves justification structure (useful for revision), Option B is simpler. **Recommendation**: Option A for full fidelity.

**Theorem (Choice-Derivation Distributivity)**:
```
derive(choice(a, b), f) ≡ choice(derive(a, f), derive(b, f))
```
at the confidence level: max(c_a, c_b) × c_f = max(c_a × c_f, c_b × c_f)

This distributivity holds because max(a,b) × c = max(a×c, b×c) for c ∈ [0,1].

### 4.2 Choice and Aggregation

**Question**: How do choice and aggregation interact?

**Case: Aggregating a choice**
```
choice(j₁, j₂)    j₃    (all justify A)
```

**Interpretation matters**:
- If j₃ is independent evidence: aggregate(choice(j₁, j₂), j₃)
- If j₃ is another alternative: choice(j₁, j₂, j₃)

**Mixed case**:
```
aggregate(choice(j₁, j₂), j₃)
confidence = max(c₁, c₂) ⊕ c₃
```

This is coherent: "I have either j₁ or j₂ as one piece of evidence, and j₃ as independent additional evidence."

**Non-distributivity**:
```
aggregate(choice(a, b), c) ≠ choice(aggregate(a, c), aggregate(b, c))

LHS: max(c_a, c_b) ⊕ c_c
RHS: max(c_a ⊕ c_c, c_b ⊕ c_c)
```

**Counterexample**: c_a = 0.5, c_b = 0.3, c_c = 0.4
- LHS: max(0.5, 0.3) ⊕ 0.4 = 0.5 ⊕ 0.4 = 0.7
- RHS: max(0.5 ⊕ 0.4, 0.3 ⊕ 0.4) = max(0.7, 0.58) = 0.7

Actually equal in this case! Let's try another:
c_a = 0.8, c_b = 0.2, c_c = 0.5
- LHS: max(0.8, 0.2) ⊕ 0.5 = 0.8 ⊕ 0.5 = 0.9
- RHS: max(0.8 ⊕ 0.5, 0.2 ⊕ 0.5) = max(0.9, 0.6) = 0.9

Also equal! Let me check if this is a general property...

**Theorem attempt**: aggregate(choice(a, b), c) = choice(aggregate(a, c), aggregate(b, c))?

LHS: max(a, b) ⊕ c = 1 - (1 - max(a,b))(1-c)
RHS: max(a ⊕ c, b ⊕ c) = max(1-(1-a)(1-c), 1-(1-b)(1-c))

For a ≥ b:
LHS = 1 - (1-a)(1-c)
RHS = max(1-(1-a)(1-c), 1-(1-b)(1-c)) = 1-(1-a)(1-c)

Yes! **Distributivity holds**: aggregate(choice(a, b), c) = choice(aggregate(a, c), aggregate(b, c))

This is because max and ⊕ are both monotone, and when a ≥ b, we have a ⊕ c ≥ b ⊕ c.

### 4.3 Choice and Defeat

**Question**: How does defeat interact with choice?

**Case 1: Undercutting one alternative**
```
choice(j₁, j₂) : A
d undercuts j₁
```

**Result**: choice(undercut(j₁, d), j₂) : A
**Confidence**: max(c₁ × (1-d), c₂)

**Interpretation**: One alternative is weakened; the other remains. The belief survives via the remaining alternative.

**Case 2: Undercutting the choice itself**
```
choice(j₁, j₂) : A
d undercuts the choice as a whole
```

**Result**: undercut(choice(j₁, j₂), d) : A
**Confidence**: max(c₁, c₂) × (1-d)

**Interpretation**: All alternatives are equally undermined.

**Case 3: Rebut against a choice**
```
choice(j₁, j₂) justifies A with confidence max(c₁, c₂)
r justifies ¬A with confidence c_r
```

**Result**: rebut(choice(j₁, j₂), r)
**Confidence**: max(c₁, c₂) / (max(c₁, c₂) + c_r)

**Distributivity for undercut?**
```
undercut(choice(a, b), d) vs choice(undercut(a, d), undercut(b, d))

LHS: max(c_a, c_b) × (1-d)
RHS: max(c_a × (1-d), c_b × (1-d)) = max(c_a, c_b) × (1-d)
```

**Undercut distributes over choice**: undercut(choice(a, b), d) = choice(undercut(a, d), undercut(b, d))

This is because scalar multiplication distributes over max.

---

## 5. Type-Theoretic Analysis (Curry-Howard)

### 5.1 Choice as Sum Type

In the Curry-Howard correspondence:
- Proofs of A ∨ B are values of type A + B (tagged union)
- Introduction: inl : A → A + B, inr : B → A + B
- Elimination: case analysis

For CLAIR's graded setting:
```
choice : Belief<A>[c₁] → Belief<A>[c₂] → Belief<A>[max(c₁,c₂)]
```

But this is different from standard sum types! In standard type theory:
- A + B requires proving A OR proving B (exclusive)
- CLAIR's choice allows proving A AND proving B, then picking the best

**CLAIR's Choice is Non-Linear**: It doesn't consume alternatives; it aggregates their availability.

### 5.2 Choice vs Aggregation in Type Terms

From Thread 2.22 (Curry-Howard):
```
aggregate : Belief<A>[c₁] → Belief<A>[c₂] → Belief<A>[c₁ ⊕ c₂]
choice    : Belief<A>[c₁] → Belief<A>[c₂] → Belief<A>[max(c₁,c₂)]
```

**Type-level difference**:
- Aggregation: c₁ ⊕ c₂ ≥ max(c₁, c₂) always
- Choice: max(c₁, c₂) ≤ c₁ ⊕ c₂ always

Aggregation gives strictly higher (or equal) confidence. So why would anyone use choice?

**The answer is semantic, not just confidence-level**:
- Aggregation claims: "These are independent pieces of evidence for the same conclusion"
- Choice claims: "These are alternative justifications; any one suffices"

If the alternatives are NOT independent evidence (e.g., two proofs using the same lemma), aggregation is semantically incorrect and would overcount.

### 5.3 Reduction Rules

**Choice-Derivation**:
```
derive(choice(e₁, e₂), f) ⟶ choice(derive(e₁, f), derive(e₂, f))
```

**Choice Projection** (when one alternative is eliminated):
```
choice(e, ⊥) ⟶ e    where ⊥ has confidence 0
```

**Choice Idempotence**:
```
choice(e, e) ⟶ e    (up to justification equivalence)
```

---

## 6. Decidability Considerations

### 6.1 Impact on CLAIR Fragments

From Thread 2.21, CLAIR-finite and CLAIR-stratified are decidable.

**Adding Choice to CLAIR-finite**:
- max over finite lattice L_n is decidable
- No new complexity introduced
- CLAIR-finite + Choice remains decidable

**Adding Choice to CLAIR-stratified**:
- max over rationals is computable
- Choice doesn't introduce self-reference
- CLAIR-stratified + Choice remains decidable

**General CLAIR**:
- Choice uses max, which is simpler than ⊕
- No impact on the Vidal-style undecidability argument (which targets transitivity + continuity)
- CLAIR + Choice has same decidability profile as CLAIR without Choice

### 6.2 Equivalence with Choice

**Question**: When are two justifications with Choice equivalent?

With choice, we need to consider:
```
choice(a, b) ≡ choice(b, a)     (commutativity)
choice(a, choice(b, c)) ≡ choice(choice(a, b), c)     (associativity)
choice(a, a) ≡ a     (idempotence at confidence level)
```

These are all decidable operations on normal forms.

---

## 7. Implementation Design

### 7.1 Syntax Extension

**Surface Syntax**:
```clair
-- Explicit choice
let b : Belief<Int> = choice [b1, b2, b3]

-- Pattern: "any of these works"
let b : Belief<Int> = any_of [b1, b2, b3]

-- With annotation
let b : Belief<Int> =
  choice [b1, b2]
    rationale: "Either method proves the theorem"
```

### 7.2 Lean Formalization

```lean
namespace CLAIR.Belief

/-- Create a choice between alternatives. Confidence = max of alternatives. -/
def choice (b₁ b₂ : Belief α) (h : b₁.value = b₂.value) : Belief α :=
  ⟨b₁.value, Confidence.max b₁.confidence b₂.confidence⟩

/-- Choice is commutative in confidence -/
theorem choice_comm (b₁ b₂ : Belief α) (h : b₁.value = b₂.value) :
    (choice b₁ b₂ h).confidence = (choice b₂ b₁ (h.symm)).confidence := by
  simp [choice, Confidence.max_comm]

/-- Choice is idempotent -/
theorem choice_idem (b : Belief α) :
    choice b b rfl = b := by
  simp [choice, Confidence.max_self]

/-- Choice is associative in confidence -/
theorem choice_assoc (b₁ b₂ b₃ : Belief α)
    (h₁₂ : b₁.value = b₂.value) (h₂₃ : b₂.value = b₃.value) :
    let c₁₂ := choice b₁ b₂ h₁₂
    let c₂₃ := choice b₂ b₃ h₂₃
    (choice c₁₂ b₃ (by rw [h₁₂]; exact h₂₃)).confidence =
    (choice b₁ c₂₃ (by rw [h₁₂, h₂₃])).confidence := by
  simp [choice, Confidence.max_assoc]

/-- Choice confidence is at least each alternative -/
theorem choice_ge_left (b₁ b₂ : Belief α) (h : b₁.value = b₂.value) :
    (b₁.confidence : ℝ) ≤ ((choice b₁ b₂ h).confidence : ℝ) :=
  Confidence.le_max_left b₁.confidence b₂.confidence

theorem choice_ge_right (b₁ b₂ : Belief α) (h : b₁.value = b₂.value) :
    (b₂.confidence : ℝ) ≤ ((choice b₁ b₂ h).confidence : ℝ) :=
  Confidence.le_max_right b₁.confidence b₂.confidence

/-- Aggregation gives higher confidence than choice -/
theorem aggregate_ge_choice (b₁ b₂ : Belief α)
    (h : b₁.value = b₂.value) (combine : α → α → α) :
    ((choice b₁ b₂ h).confidence : ℝ) ≤
    ((aggregate b₁ b₂ combine).confidence : ℝ) :=
  Confidence.max_le_oplus b₁.confidence b₂.confidence

end CLAIR.Belief
```

### 7.3 Justification Graph Extension

```lean
inductive JustificationNode where
  -- ... existing constructors ...
  | choice : List JustificationEdge → JustificationNode

structure ChoiceData where
  alternatives : List JustificationId
  rationale : Option String
  selected : Option JustificationId  -- which one is "primary"
```

---

## 8. Comparison with JL's Sum

### 8.1 What CLAIR Choice Inherits from JL

**Monotonicity**:
```
JL: t : φ → (t + s) : φ
CLAIR: b : Belief<A>[c] → choice(b, b') : Belief<A>[max(c, c')] where max(c,c') ≥ c
```

**Commutativity**:
```
JL: t + s = s + t (up to provability)
CLAIR: choice(b₁, b₂) ≡ choice(b₂, b₁) (equal confidence)
```

**Associativity**:
```
JL: (t + s) + u = t + (s + u)
CLAIR: choice(choice(b₁, b₂), b₃) ≡ choice(b₁, choice(b₂, b₃))
```

### 8.2 What CLAIR Choice Adds Beyond JL

**Graded confidence**: JL's sum is ungraded; CLAIR choice has max semantics.

**Interaction with defeat**: JL has no defeat; CLAIR choice interacts with undercut and rebut.

**DAG integration**: CLAIR choice nodes are part of the justification DAG; JL terms are trees.

**Revision**: When a choice alternative is invalidated, CLAIR can recompute confidence using remaining alternatives.

### 8.3 Conservative Extension Revisited

With Choice, the conservative extension result from Thread 2.18 becomes cleaner:

**Theorem (Refined Conservative Extension)**:
CLAIR with Choice is a conservative extension of JL (LP) for the JL-fragment at confidence 1, where:
- JL's `+` maps to CLAIR's `choice`
- JL's `·` maps to CLAIR's `derive`
- JL's `!` maps to CLAIR's `introspect`

The mapping is now **semantically exact** for the JL fragment.

---

## 9. Open Questions

### 9.1 N-ary Choice vs Binary Choice

**Design choice**: Should choice be binary or n-ary?

**Arguments for binary**:
- Simpler formalization
- Matches JL's binary sum
- Associativity allows encoding n-ary

**Arguments for n-ary**:
- More natural surface syntax
- Avoids deep nesting
- More efficient representation

**Recommendation**: Support both. Primitive is n-ary; binary is syntactic sugar.

### 9.2 Weighted Choice?

**Question**: Should alternatives have weights affecting the choice?

Standard choice: confidence = max(c₁, c₂, ..., cₙ)
Weighted choice: confidence = max(w₁·c₁, w₂·c₂, ..., wₙ·cₙ)?

**Analysis**: This seems to conflate choice with derivation. If weights represent "reliability of this alternative," that's a different operation. Standard max semantics is cleaner.

**Recommendation**: No weighted choice. Use derivation to adjust alternative confidences before choice if needed.

### 9.3 Choice and Provenance

**Question**: What is the provenance of a choice?

**Options**:
A. Record all alternatives in provenance
B. Record only the max-confidence alternative
C. Record the choice structure itself

**Recommendation**: Option C. The provenance is `Provenance.Choice(alternatives)`, capturing that the belief came from selecting among options. The specific alternatives are recorded in the justification DAG.

---

## 10. Conclusions

### 10.1 Key Findings

1. **Choice is necessary for JL compatibility**: Without it, CLAIR cannot faithfully represent JL's sum operation.

2. **Choice differs from aggregation semantically**: Aggregation combines independent evidence (⊕); choice selects among alternatives (max).

3. **Confidence semantics**: choice(b₁, ..., bₙ) has confidence max(c₁, ..., cₙ).

4. **Algebraic properties**:
   - Choice is commutative, associative, idempotent
   - Undercut distributes over choice
   - Aggregate distributes over choice
   - Choice gives lower confidence than aggregation (max ≤ ⊕)

5. **Type-theoretic view**: Choice is like a sum type, but non-linear (alternatives aren't consumed).

6. **Decidability**: Adding choice doesn't affect decidability of CLAIR fragments.

7. **Implementation**: Extend JustificationNode with `choice` constructor; add `choice` operation to Belief.

### 10.2 Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Choice should use max semantics | 0.90 | Matches JL, intuitive "best alternative" |
| Choice differs from aggregation | 0.95 | Clear semantic distinction |
| Undercut distributes over choice | 0.95 | Algebraically verified |
| Aggregate distributes over choice | 0.90 | Algebraically verified |
| Adding choice preserves decidability | 0.85 | max is simpler than ⊕; no new complexity |
| Choice needed for JL conservative extension | 0.90 | Direct correspondence to JL sum |

### 10.3 Recommendations

1. **Add Choice to CLAIR**: Define the `choice` constructor for justification nodes.

2. **Use max semantics**: confidence(choice(e₁, ..., eₙ)) = max(conf(eᵢ))

3. **Support both binary and n-ary**: N-ary is primitive; binary is derived.

4. **Formalize in Lean**: Add choice to CLAIR.Belief module.

5. **Update syntax**: Add `choice [...]` and `any_of [...]` surface forms.

6. **Clarify documentation**: Distinguish choice (alternatives) from aggregation (evidence).

---

## 11. Impact on Other Threads

### Thread 2.18 (Conservative Extension)
- With Choice, conservative extension over JL becomes cleaner
- JL's sum (+) maps exactly to CLAIR's choice

### Thread 2.22 (Curry-Howard)
- Add choice as a term constructor
- Reduction rules: choice-derivation distributivity

### Thread 8 (Lean Formalization)
- Add choice to CLAIR/Belief/Basic.lean
- Prove algebraic properties (comm, assoc, idem)

### Thread 7 (Implementation)
- Extend JustificationGraph with choice nodes
- Add surface syntax

---

## 12. References

### Primary Sources

- **Artemov, S.** (2001). "Explicit Provability and Constructive Semantics." *Bull. Symb. Logic*, 7(1), 1-36.

- **Artemov, S. & Fitting, M.** (2019). *Justification Logic: Reasoning with Reasons*. Cambridge University Press.

- **Dung, P. M.** (1995). "On the Acceptability of Arguments." *Artificial Intelligence*, 77(2), 321-357.

### CLAIR Internal

- Thread 2.4: exploration/thread-2.4-justification-logic-connection.md
- Thread 2.11: exploration/thread-2.11-aggregation.md
- Thread 2.18: exploration/thread-2.18-conservative-extension.md
- Thread 2.22: exploration/thread-2.22-curry-howard-terms.md
- Thread 2.21: exploration/thread-2.21-decidable-fragments.md

---

*Thread 2.15 Status: Substantially explored. Choice construct fully designed with max semantics. Recommended for implementation.*
