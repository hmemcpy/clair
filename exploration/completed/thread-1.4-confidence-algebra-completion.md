# Thread 1.4: Confidence Algebra Completion

> **Status**: Active exploration (Session 77)
> **Task**: 1.4 Confidence algebra - Prove monad laws, defeat composition
> **Question**: What remains to prove Belief is a graded monad, and what are the defeat composition properties?

---

## 1. The Problem

Task 1.4 asks us to complete the confidence algebra formalization with two goals:
1. **Prove graded monad laws** for Belief
2. **Prove defeat composition theorems**

Let me analyze what's already done and what remains.

---

## 2. Current State Analysis

### 2.1 Confidence Operations (Complete)

All core confidence operations are proven in Lean:

| Operation | File | Status | Key Theorems |
|-----------|------|--------|--------------|
| Multiplication (×) | Basic.lean | ✓ Complete | `mul_mem'`, `mul_le_left/right` |
| Oplus (⊕) | Oplus.lean | ✓ Complete | Commutative monoid, `oplus_assoc/comm`, `le_oplus_left/right` |
| Undercut | Undercut.lean | ✓ Complete | `undercut_compose`, `undercut_le` |
| Rebut | Rebut.lean | ✓ Complete | Boundedness, anti-symmetry, monotonicity |
| Min | Min.lean | ✓ Complete | Bounded meet-semilattice |

### 2.2 Belief Operations (Partially Complete)

| Operation | File | Status | Gap |
|-----------|------|--------|-----|
| `map` (functor) | Belief/Basic.lean | ✓ | `map_id`, `map_comp` proven |
| `bind` | Belief/Basic.lean | ✓ | Defined correctly |
| `pure` | Belief/Basic.lean | ✓ | Defined as `certain` |
| Left identity (conf) | Belief/Basic.lean | ✓ | `bind_pure_left_confidence` |
| Right identity (conf) | Belief/Basic.lean | ✓ | `bind_pure_right_confidence` |
| **Left identity (value)** | - | **MISSING** | Need to prove |
| **Right identity (value)** | - | **MISSING** | Need to prove |
| **Associativity** | - | **MISSING** | Need full proof |
| **Graded monad formalization** | - | **MISSING** | Structure not defined |

---

## 3. Graded Monad Analysis

### 3.1 What is a Graded Monad?

A **graded monad** (also: indexed monad, parametric monad) is a monad where the type constructor is indexed by elements of a monoid M = (M, ⊗, 1):

```
T : M → Type → Type

pure  : A → T₁ A                           -- grade is identity
bind  : T_m A → (A → T_n B) → T_{m⊗n} B    -- grades multiply
```

The monad laws must respect grading:
1. `bind (pure a) f = f a` with grade `1 ⊗ n = n`
2. `bind m pure = m` with grade `m ⊗ 1 = m`
3. `bind (bind m f) g = bind m (λx. bind (f x) g)` with grade `(m ⊗ n) ⊗ p = m ⊗ (n ⊗ p)`

### 3.2 CLAIR's Graded Monad Structure

For CLAIR:
- **Grading monoid**: M = ([0,1], ×, 1) — confidence under multiplication
- **Indexed type**: `Belief_c A` where c is the confidence

But Lean's current formulation uses a simpler approach:
```lean
structure Belief (α : Type*) where
  value : α
  confidence : Confidence
```

The grading is implicit: confidence is tracked at the value level, not the type level.

### 3.3 Why Not Type-Level Grading?

Type-level grading would look like:
```lean
-- Hypothetical type-level indexed belief
def Belief (c : Confidence) (α : Type*) :=
  { b : BeliefRaw α // b.confidence = c }
```

**Problems**:
1. **Dependent types complexity**: Would need sophisticated dependent type features
2. **Practical usability**: Confidence is often computed, not known statically
3. **Match with semantics**: CLAIR's confidence is runtime-computed

**CLAIR's approach**: Track confidence at value level, prove grade laws algebraically.

---

## 4. Proving the Monad Laws

### 4.1 Left Identity

**Statement**: `bind (pure a) f = f a`

**Proof sketch**:
```lean
bind (pure a) f
= bind ⟨a, 1⟩ f
= let result := f a in ⟨result.value, 1 × result.confidence⟩
= ⟨(f a).value, (f a).confidence⟩    -- since 1 × c = c
= f a                                   -- by extensionality
```

**Value component**: `(bind (pure a) f).value = (f a).value`
- This follows directly from the definition of bind.

**Confidence component**: `(bind (pure a) f).confidence = (f a).confidence`
- Already proven as `bind_pure_left_confidence`.

**Full equality**: Follows from Belief extensionality.

### 4.2 Right Identity

**Statement**: `bind m pure = m`

**Proof sketch**:
```lean
bind m pure
= let result := pure m.value in ⟨result.value, m.confidence × result.confidence⟩
= ⟨(pure m.value).value, m.confidence × (pure m.value).confidence⟩
= ⟨m.value, m.confidence × 1⟩         -- pure gives confidence 1
= ⟨m.value, m.confidence⟩             -- since c × 1 = c
= m                                     -- by extensionality
```

**Value component**: `(bind m pure).value = m.value`
- Follows from definition.

**Confidence component**: Already proven as `bind_pure_right_confidence`.

### 4.3 Associativity

**Statement**: `bind (bind m f) g = bind m (λx. bind (f x) g)`

**Proof sketch**:

Left side:
```lean
bind (bind m f) g
= let r1 := f m.value in
  let r2 := bind ⟨r1.value, m.confidence × r1.confidence⟩ g in
  ...wait, need to be careful...

Actually:
bind m f = ⟨(f m.value).value, m.confidence × (f m.value).confidence⟩

bind (bind m f) g =
  let result := g (bind m f).value in
  ⟨result.value, (bind m f).confidence × result.confidence⟩
= let result := g (f m.value).value in
  ⟨result.value, (m.confidence × (f m.value).confidence) × result.confidence⟩
```

Right side:
```lean
bind m (λx. bind (f x) g)
= let result := (λx. bind (f x) g) m.value in
  ⟨result.value, m.confidence × result.confidence⟩
= let result := bind (f m.value) g in
  ⟨result.value, m.confidence × result.confidence⟩
= let r := g (f m.value).value in
  ⟨r.value, m.confidence × ((f m.value).confidence × r.confidence)⟩
```

**Value component**:
- LHS: `g (f m.value).value).value`
- RHS: `(g (f m.value).value).value`
- These are identical.

**Confidence component**:
- LHS: `(m.confidence × (f m.value).confidence) × (g (f m.value).value).confidence`
- RHS: `m.confidence × ((f m.value).confidence × (g (f m.value).value).confidence)`
- These are equal by associativity of × on Confidence.

**Conclusion**: Associativity follows from:
1. Value equality (definitional)
2. Confidence associativity (already proven for × on unitInterval via Mathlib)

---

## 5. Lean 4 Formalization

### 5.1 New Theorems to Add to Belief/Basic.lean

```lean
/-!
## Full Monad Laws
-/

/-- Left identity law for bind (full equality, not just confidence) -/
theorem bind_pure_left (v : α) (f : α → Belief β) :
    bind (pure v) f = f v := by
  simp only [bind, pure, certain]
  ext
  · -- value component
    rfl
  · -- confidence component
    simp only [Subtype.coe_mk, unitInterval.coe_one, one_mul]

/-- Right identity law for bind (full equality) -/
theorem bind_pure_right (b : Belief α) :
    bind b pure = b := by
  simp only [bind, pure, certain]
  ext
  · -- value component
    rfl
  · -- confidence component
    simp only [Subtype.coe_mk, unitInterval.coe_one, mul_one]
    rfl

/-- Associativity law for bind -/
theorem bind_assoc (b : Belief α) (f : α → Belief β) (g : β → Belief γ) :
    bind (bind b f) g = bind b (fun x => bind (f x) g) := by
  simp only [bind]
  ext
  · -- value component: both sides reduce to (g (f b.value).value).value
    rfl
  · -- confidence component: associativity of multiplication
    simp only [Subtype.coe_mk]
    ring  -- multiplication is associative
```

### 5.2 Graded Monad Typeclass (Optional)

We could define a graded monad typeclass for generality:

```lean
/-- A graded monad indexed by a monoid M -/
class GradedMonad (M : Type*) [Monoid M] (T : M → Type* → Type*) where
  pure : ∀ {α}, α → T 1 α
  bind : ∀ {m n α β}, T m α → (α → T n β) → T (m * n) β
  bind_pure_left : ∀ {n α β} (a : α) (f : α → T n β),
    bind (pure a) f = f a  -- uses 1 * n = n
  bind_pure_right : ∀ {m α} (t : T m α),
    bind t pure = t  -- uses m * 1 = m
  bind_assoc : ∀ {m n p α β γ} (t : T m α) (f : α → T n β) (g : β → T p γ),
    bind (bind t f) g = bind t (fun x => bind (f x) g)  -- uses (m*n)*p = m*(n*p)
```

However, this requires dependent types to express `T m α` properly. CLAIR's simpler approach suffices.

---

## 6. Defeat Composition Analysis

### 6.1 Undercut Composition (Already Proven)

The key theorem is already in Undercut.lean:

```lean
theorem undercut_compose (c d₁ d₂ : Confidence) :
    undercut (undercut c d₁) d₂ = undercut c (d₁ ⊕ d₂)
```

**Interpretation**: Sequential undercutting defeats compose via ⊕.

This is a beautiful result connecting defeat semantics to the aggregation operation.

### 6.2 Rebut Composition Analysis

**Question**: Is there a clean composition law for rebut?

**Rebut definition**: `rebut(c_for, c_against) = c_for / (c_for + c_against)`

**Attempt at composition**:
```
rebut(rebut(c, d₁), d₂)
= rebut(c / (c + d₁), d₂)
= (c / (c + d₁)) / ((c / (c + d₁)) + d₂)
= c / (c + d₁ + d₂(c + d₁))
= c / (c + d₁ + d₂c + d₁d₂)
= c / ((1 + d₂)c + (1 + d₂)d₁)
= c / ((1 + d₂)(c + d₁))
```

This doesn't simplify to a clean form like `rebut(c, d₁ ⊕ d₂)`.

**Verification**:
```
rebut(c, d₁ ⊕ d₂) = c / (c + d₁ + d₂ - d₁d₂)
```

Compare:
- Sequential rebut: `c / ((1 + d₂)(c + d₁))`
- Single rebut with ⊕: `c / (c + d₁ + d₂ - d₁d₂)`

These are NOT equal in general.

**Counterexample**: c = 0.5, d₁ = 0.3, d₂ = 0.2
- Sequential: 0.5 / ((1.2)(0.8)) = 0.5 / 0.96 ≈ 0.521
- Single ⊕: 0.5 / (0.5 + 0.3 + 0.2 - 0.06) = 0.5 / 0.94 ≈ 0.532

**Conclusion**: **Rebut does NOT compose via ⊕**.

### 6.3 Why the Difference?

**Undercut** is multiplicative discounting:
- `undercut(c, d) = c × (1 - d)`
- Sequential: `c × (1-d₁) × (1-d₂) = c × ((1-d₁)(1-d₂)) = c × (1 - (d₁ ⊕ d₂))`
- The De Morgan relationship makes it work.

**Rebut** is ratio-based:
- `rebut(c, d) = c / (c + d)`
- This is NOT multiplicative; it's a "market share" calculation.
- Sequential application creates nested ratios.

### 6.4 Alternative Rebut Composition?

Is there ANY clean composition for rebut?

Consider: `rebut(c, d₁) = c / (c + d₁)`

If we sequentially apply rebut with d₂:
```
rebut(c / (c + d₁), d₂) = (c / (c + d₁)) / ((c / (c + d₁)) + d₂)
                        = c / (c + d₁ + d₂(c + d₁))
```

This could be rewritten as:
```
= c / (c + d₁ + d₂c + d₁d₂)
= c / (c(1 + d₂) + d₁(1 + d₂))
= c / ((c + d₁)(1 + d₂))
```

So: `rebut(rebut(c, d₁), d₂) = rebut(c, d₁) / (1 + d₂)` when d₂ is small? No, that's not right either.

**Alternative formulation**: Perhaps:
```
rebut(rebut(c, d₁), d₂) = rebut(c, f(d₁, d₂))
```

where `f` is some combining function. But what `f`?

From the algebra:
```
c / ((c + d₁)(1 + d₂)) = c / (c + f(d₁, d₂))
⟹ (c + d₁)(1 + d₂) = c + f(d₁, d₂)
⟹ f(d₁, d₂) = (c + d₁)(1 + d₂) - c
             = c + d₁ + cd₂ + d₁d₂ - c
             = d₁ + cd₂ + d₁d₂
             = d₁(1 + d₂) + cd₂
```

This depends on c! There's no c-independent combining function.

**Final conclusion**: **Rebut has no clean composition law.**

### 6.5 Semantic Interpretation

Why does undercut compose cleanly but rebut doesn't?

**Undercut** models discounting of the inferential link:
- "I discount your argument by 30%, then further by 20%"
- These are independent discounts that multiply
- Total discount = 1 - (1-0.3)(1-0.2) = 1 - 0.56 = 0.44 = 0.3 ⊕ 0.2

**Rebut** models competing evidence:
- "I have evidence against, you have evidence for, what's the balance?"
- Sequential rebuttal changes the baseline
- First rebut: c becomes c/(c+d₁)
- Second rebut: this new value competes with d₂
- The competition is relative to current state, not original

**Analogy**:
- Undercut is like applying multiplicative taxes: 30% tax then 20% tax = 44% total (order-independent)
- Rebut is like market competition: if you have 50% share and lose 30% to competitor A, then lose 20% of remaining to B, order matters and there's no simple formula.

---

## 7. Summary of Findings

### 7.1 Graded Monad Laws

| Law | Value Level | Confidence Level | Status |
|-----|-------------|------------------|--------|
| Left Identity | ✓ Definitional | ✓ Proven (`bind_pure_left_confidence`) | **Ready to prove full** |
| Right Identity | ✓ Definitional | ✓ Proven (`bind_pure_right_confidence`) | **Ready to prove full** |
| Associativity | ✓ Definitional | ✓ Follows from × associativity | **Ready to prove** |

**Action**: Add three theorems to Belief/Basic.lean: `bind_pure_left`, `bind_pure_right`, `bind_assoc`.

### 7.2 Defeat Composition

| Operation | Composition Law | Status |
|-----------|-----------------|--------|
| Undercut | `undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)` | ✓ **Proven** |
| Rebut | No clean law exists | ✓ **Documented** |

**Finding**: Rebut's ratio-based semantics prevent clean composition. This is mathematically fundamental, not a gap to fill.

### 7.3 Non-Distributivity

Already documented but worth formalizing as a counterexample:

```lean
/-- Counterexample: × and ⊕ do not distribute -/
theorem mul_oplus_not_distrib :
    ∃ a b c : Confidence, a * (b ⊕ c) ≠ (a * b) ⊕ (a * c) := by
  use ⟨0.5, by norm_num, by norm_num⟩
  use ⟨0.5, by norm_num, by norm_num⟩
  use ⟨0.5, by norm_num, by norm_num⟩
  simp only [HMul.hMul, Mul.mul, oplus, Subtype.coe_mk, ne_eq]
  norm_num
  -- 0.5 × (0.5 ⊕ 0.5) = 0.5 × 0.75 = 0.375
  -- (0.5 × 0.5) ⊕ (0.5 × 0.5) = 0.25 ⊕ 0.25 = 0.4375
```

---

## 8. Lean Code Updates

The following should be added to `formal/lean/CLAIR/Belief/Basic.lean`:

```lean
/-!
## Graded Monad Laws

Belief forms a graded monad over ([0,1], ×, 1).
The grading is tracked at the value level, not the type level.
-/

/-- Left identity: bind (pure a) f = f a -/
theorem bind_pure_left (v : α) (f : α → Belief β) :
    bind (pure v) f = f v := by
  simp only [bind, pure, certain]
  rfl

/-- Right identity: bind b pure = b -/
theorem bind_pure_right (b : Belief α) :
    bind b pure = b := by
  simp only [bind, pure, certain]
  congr 1
  simp only [Subtype.coe_mk, unitInterval.coe_one, mul_one]
  rfl

/-- Associativity: bind (bind b f) g = bind b (λx. bind (f x) g) -/
theorem bind_assoc (b : Belief α) (f : α → Belief β) (g : β → Belief γ) :
    bind (bind b f) g = bind b (fun x => bind (f x) g) := by
  simp only [bind]
  congr 1
  · rfl  -- values match
  · -- confidences match via associativity
    apply Subtype.ext
    simp only [Subtype.coe_mk]
    ring
```

---

## 9. Remaining Gaps

After this exploration, the confidence algebra is essentially complete. Remaining items:

1. **Add monad law theorems to Lean** (straightforward, proofs sketched above)
2. **Add non-distributivity counterexample to Lean** (optional, for documentation)
3. **Document rebut non-composition** (done in this file)

**What's NOT a gap**:
- Rebut composition: no clean law exists (fundamental, not missing)
- Full graded monad typeclass: CLAIR's simpler approach suffices

---

## 10. Conclusion

**Task 1.4 is substantially complete.**

**Graded monad laws**:
- All three laws are straightforward to prove
- Value components are definitional
- Confidence components follow from × associativity
- Ready to add formal proofs to Lean

**Defeat composition**:
- Undercut composition via ⊕: ✓ Already proven
- Rebut composition: ✓ Documented as not existing (fundamental)

**Non-distributivity**:
- ✓ Documented with counterexample

**Recommendation**: Mark Task 1.4 as complete after adding the three monad law theorems to Belief/Basic.lean.

---

*Thread 1.4 Status: Exploration complete. Proofs designed and ready for implementation. Key finding: rebut has no clean composition law (mathematically fundamental).*
