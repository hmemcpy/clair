# Thread 8.3: Confidence Soundness for CLAIR

> **Status**: Active exploration (Session 66)
> **Task**: 8.3 Prove confidence propagation preserves [0,1] bounds
> **Question**: How do we prove that CLAIR's confidence system maintains valid bounds through evaluation?
> **Prior Work**: Thread 8 (Confidence operations), Thread 8.1-impl (Lean syntax), Thread 8.2 (Type safety)

---

## 1. The Problem

### 1.1 What Is Confidence Soundness?

Confidence soundness means: **All confidence values in CLAIR remain within [0,1] throughout computation.**

This has three dimensions:

1. **Static Soundness**: Well-formed types have valid confidence bounds
2. **Operational Soundness**: Each evaluation step preserves [0,1] bounds
3. **Semantic Soundness**: The syntactic (ℚ) and semantic (ℝ) confidence types are compatible

### 1.2 The Current Architecture

CLAIR's Lean formalization has two confidence representations:

**Semantic Confidence** (`CLAIR.Confidence`):
- Type: `unitInterval` (subtype of ℝ with `0 ≤ c ∧ c ≤ 1`)
- Operations: `oplus`, `undercut`, `rebut`, multiplication, min
- All operations proven to preserve bounds

**Syntactic Confidence** (`CLAIR.Syntax.ConfBound`):
- Type: `ℚ` (rationals, for decidable type checking)
- Operations: `oplus`, `undercut`, `rebut`, `loebDiscount`
- **No bounds preservation proofs yet!**

### 1.3 The Gap

The gap is clear: syntactic confidence operations lack bounds proofs. This means:
- Type checking might accept programs with invalid (out-of-bounds) confidence
- The semantic model doesn't validate the syntactic operations
- Type safety depends on confidence soundness (defeat operations change confidence)

---

## 2. Analysis of Confidence Operations

### 2.1 Operations and Their Semantics

| Operation | Formula | Used In |
|-----------|---------|---------|
| Multiplication (×) | `a × b` | Derivation, application |
| Oplus (⊕) | `a + b - a × b` | Aggregation |
| Undercut | `c × (1 - d)` | Defeat (link attack) |
| Rebut | `c_for / (c_for + c_against)` | Defeat (conclusion attack) |
| Löb Discount | `c × c` | Introspection |
| Min | `min(a, b)` | Conservative combination |

### 2.2 Bounds Requirements

For each operation f on confidence values c₁, c₂ ∈ [0,1]:
- **Lower bound**: `f(c₁, c₂) ≥ 0`
- **Upper bound**: `f(c₁, c₂) ≤ 1`

### 2.3 Current State in Lean

**Proven (on ℝ)** in `CLAIR/Confidence/*.lean`:
- `mul_mem'`: Multiplication preserves bounds
- `oplus_bounded`: Oplus preserves bounds
- `undercut_bounded`: Undercut preserves bounds
- `rebut_bounded`: Rebut preserves bounds
- `min`: Trivially preserves bounds (lattice operation)

**Not Proven (on ℚ)** in `CLAIR/Syntax/Types.lean`:
- `ConfBound.oplus`: No bounds proof
- `ConfBound.undercut`: No bounds proof
- `ConfBound.rebut`: No bounds proof
- `ConfBound.loebDiscount`: No bounds proof

---

## 3. Proof Strategy

### 3.1 Two Approaches

**Approach A: Prove directly on ℚ**
- Add bounds proofs to each `ConfBound` operation
- Similar structure to the ℝ proofs
- Pro: Direct, no embedding needed
- Con: Duplicates work from semantic Confidence

**Approach B: Embed ℚ into ℝ**
- Show ℚ ∩ [0,1] embeds into unitInterval
- Lift proofs from ℝ to ℚ
- Pro: Reuses existing proofs
- Con: More complex setup, coercion overhead

**Recommendation**: Approach A for simplicity. The proofs are algebraic and work identically on ℚ and ℝ.

### 3.2 Proof Obligations

For each operation, we need:

```lean
-- For oplus
theorem ConfBound.oplus_valid (a b : ConfBound) :
    a.valid → b.valid → (ConfBound.oplus a b).valid

-- For undercut
theorem ConfBound.undercut_valid (c d : ConfBound) :
    c.valid → d.valid → (ConfBound.undercut c d).valid

-- For rebut
theorem ConfBound.rebut_valid (c_for c_against : ConfBound) :
    c_for.valid → c_against.valid → (ConfBound.rebut c_for c_against).valid

-- For Löb discount
theorem ConfBound.loebDiscount_valid (c : ConfBound) :
    c.valid → (ConfBound.loebDiscount c).valid
```

Where `valid c = 0 ≤ c ∧ c ≤ 1`.

### 3.3 Proof Sketches

**Multiplication** (`a × b`):
- Lower: `0 ≤ a × b` because `0 ≤ a`, `0 ≤ b`, and product of non-negatives is non-negative
- Upper: `a × b ≤ 1` because `a × b ≤ a × 1 = a ≤ 1`

**Oplus** (`a + b - a × b`):
- Rewrite as `a + b × (1 - a)`
- Lower: Sum of non-negatives (since `b ≥ 0` and `1 - a ≥ 0` when `a ≤ 1`)
- Upper: `a + b × (1 - a) ≤ a + 1 × (1 - a) = a + 1 - a = 1`

**Undercut** (`c × (1 - d)`):
- Lower: Product of non-negatives (since `c ≥ 0` and `1 - d ≥ 0` when `d ≤ 1`)
- Upper: `c × (1 - d) ≤ 1 × 1 = 1`

**Rebut** (`c_for / (c_for + c_against)`):
- Edge case: When `c_for + c_against = 0`, return 1/2 ∈ [0,1]
- Otherwise:
  - Lower: `c_for / (c_for + c_against) ≥ 0` since numerator and denominator non-negative
  - Upper: `c_for / (c_for + c_against) ≤ 1` since numerator ≤ denominator

**Löb Discount** (`c × c = c²`):
- Special case of multiplication: `c² = c × c ≤ c × 1 = c ≤ 1`
- Lower: `c² ≥ 0` (square of real is non-negative)

---

## 4. Typing Preserves Validity

### 4.1 Well-Typed Terms Have Valid Confidence

**Theorem** (Typing Validity): If `Γ ⊢ e : A @c` and all entries in Γ have valid confidence, then:
1. `c.valid` (judgment confidence is valid)
2. If `A = Ty.belief B c_b`, then `c_b.valid`
3. If `A = Ty.meta B n c_m`, then `c_m.valid`

**Proof**: By induction on the typing derivation.

**Base cases** (literals):
- `HasType.litNat/Bool/String/Unit`: Confidence is 1, which is valid.

**Inductive cases**:

1. **Variable** (`HasType.var`):
   - Confidence comes from context entry
   - By assumption, context entries have valid confidence

2. **Lambda** (`HasType.lam`):
   - Result confidence is `c_B` from body
   - By IH on body (with extended context), `c_B.valid`

3. **Application** (`HasType.app`):
   - Result confidence is `c₁ × c₂`
   - By IH, `c₁.valid` and `c₂.valid`
   - By multiplication bounds, `(c₁ × c₂).valid`

4. **Pair** (`HasType.pair`):
   - Result confidence is `c₁ × c₂`
   - Same as application

5. **Derive** (`HasType.derive`):
   - Type confidence: `c₁ × c₂` (valid by multiplication)
   - Judgment confidence: `c_e₁ × c_e₂` (valid by multiplication)

6. **Aggregate** (`HasType.aggregate`):
   - Type confidence: `c₁ ⊕ c₂` (valid by oplus bounds)
   - Judgment confidence: `c_e₁ ⊕ c_e₂` (valid by oplus bounds)

7. **Undercut** (`HasType.undercut`):
   - Type confidence: `undercut(c, d_c)` (valid by undercut bounds)
   - Judgment confidence: `c_e × c_d` (valid by multiplication)

8. **Rebut** (`HasType.rebut`):
   - Type confidence: `rebut(c_for, c_against)` (valid by rebut bounds)
   - Judgment confidence: `c_e₁ × c_e₂` (valid by multiplication)

9. **Introspect** (`HasType.introspect`):
   - Type confidence: `loebDiscount(c) = c²` (valid by Löb bounds)
   - Judgment confidence: preserved from subderivation

10. **Case** (`HasType.case`):
    - Result confidence: `c × (c₁ ⊕ c₂)`
    - By IH, all valid; by multiplication and oplus bounds, result valid

11. **Let** (`HasType.letIn`):
    - Result confidence: `c₁ × c₂`
    - By multiplication bounds

12. **Belief** (`HasType.belief`):
    - Given `c_bound ≤ c_actual`
    - If `c_bound.valid`, that's what we need
    - Note: The typing rule doesn't enforce this directly!

13. **Subsumption** (`HasType.sub`):
    - Confidence `c'` where `c ≥ c'`
    - If `c.valid`, then `c'.valid` since `0 ≤ c' ≤ c ≤ 1`

### 4.2 The Belief Constructor Issue

There's a subtle issue in `HasType.belief`:

```lean
| belief : HasType Γ v A 1 →
           c_bound ≤ c_actual →
           HasType Γ (Expr.belief v c_actual j) (Ty.belief A c_bound) c_bound
```

This rule requires `c_bound ≤ c_actual` but doesn't explicitly require either to be valid!

**Resolution Options**:

A. **Add validity as premise**:
```lean
| belief : HasType Γ v A 1 →
           c_bound.valid →
           c_actual.valid →
           c_bound ≤ c_actual →
           HasType Γ (Expr.belief v c_actual j) (Ty.belief A c_bound) c_bound
```

B. **Use valid confidence subtype**:
```lean
abbrev ValidConfBound := { c : ℚ // c.valid }
```
Then all confidence operations work on `ValidConfBound`.

C. **Well-formedness judgment**:
Separate the typing judgment from well-formedness. A term is "well-typed" only if its typing derivation uses valid confidences.

**Recommendation**: Option A (add explicit validity premises) is simplest and makes the issue explicit in the rules.

---

## 5. Evaluation Preserves Validity

### 5.1 The Statement

**Theorem** (Evaluation Validity): If `e → e'` and all confidence values in `e` are valid, then all confidence values in `e'` are valid.

### 5.2 Key Cases

**Beta reductions** (function, let, projections, case):
- These are structural; they substitute values but don't create new confidences
- Substitution preserves validity (no confidence operations)

**Belief extraction** (`valBeta`):
- `val(belief v c j) → v`
- No confidence in result; trivially valid

**Derive beta** (`deriveBeta`):
- `derive(belief(v₁, c₁, j₁), belief(v₂, c₂, j₂)) → belief(pair(v₁, v₂), c₁×c₂, ...)`
- New confidence: `c₁ × c₂`
- By multiplication bounds: valid if `c₁`, `c₂` valid

**Aggregate beta** (`aggregateBeta`):
- `aggregate(belief(v₁, c₁, j₁), belief(v₂, c₂, j₂)) → belief(v₁, c₁⊕c₂, ...)`
- New confidence: `c₁ ⊕ c₂`
- By oplus bounds: valid if `c₁`, `c₂` valid

**Undercut beta** (`undercutBeta`):
- `undercut(belief(v, c, j), belief(d, c_d, j_d)) → belief(v, c×(1-c_d), ...)`
- New confidence: `undercut(c, c_d)`
- By undercut bounds: valid if `c`, `c_d` valid

**Rebut beta** (`rebutBeta`):
- `rebut(belief(v_for, c_for, j_for), belief(v_against, c_against, j_against)) → belief(v_for, rebut(c_for, c_against), ...)`
- New confidence: `rebut(c_for, c_against)`
- By rebut bounds: valid if `c_for`, `c_against` valid

**Congruence rules**:
- These step a subterm; by IH, subterm confidence preserved
- No new confidences created

### 5.3 Proof in Lean

```lean
theorem Step.preserves_validity :
    ∀ (e e' : Expr),
    e ⟶ e' →
    e.allConfidencesValid →
    e'.allConfidencesValid := by
  intro e e' hstep hvalid
  induction hstep with
  | deriveBeta hv1 hv2 =>
    -- New confidence is c₁ × c₂
    simp [Expr.allConfidencesValid] at hvalid ⊢
    obtain ⟨hc1, hc2, _⟩ := hvalid
    exact ⟨mul_valid hc1 hc2, hv1.confidenceValid, hv2.confidenceValid⟩
  | aggregateBeta hv1 hv2 =>
    -- New confidence is c₁ ⊕ c₂
    simp [Expr.allConfidencesValid] at hvalid ⊢
    obtain ⟨hc1, hc2, _⟩ := hvalid
    exact ⟨oplus_valid hc1 hc2, hv1.confidenceValid⟩
  | undercutBeta hv hvd =>
    -- New confidence is undercut(c, c_d)
    simp [Expr.allConfidencesValid] at hvalid ⊢
    obtain ⟨hc, hcd, _⟩ := hvalid
    exact ⟨undercut_valid hc hcd, hv.confidenceValid⟩
  | rebutBeta hvf hva =>
    -- New confidence is rebut(c_for, c_against)
    simp [Expr.allConfidencesValid] at hvalid ⊢
    obtain ⟨hcf, hca, _⟩ := hvalid
    exact ⟨rebut_valid hcf hca, hvf.confidenceValid⟩
  -- ... congruence cases: IH applies
  | _ => simp_all [Expr.allConfidencesValid]
```

---

## 6. Connecting Syntactic and Semantic Confidence

### 6.1 The Embedding

The syntactic confidence (ℚ) embeds into semantic confidence (ℝ):

```lean
/-- Embed a valid rational confidence into the semantic Confidence type -/
def ConfBound.toConfidence (c : ConfBound) (h : c.valid) : Confidence :=
  ⟨(c : ℝ), by
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2⟩
```

### 6.2 Homomorphism Properties

The embedding should preserve operations:

```lean
theorem oplus_hom (a b : ConfBound) (ha : a.valid) (hb : b.valid) :
    (ConfBound.oplus a b).toConfidence (oplus_valid ha hb) =
    Confidence.oplus (a.toConfidence ha) (b.toConfidence hb) := by
  simp [ConfBound.oplus, Confidence.oplus, ConfBound.toConfidence]
  ring

theorem undercut_hom (c d : ConfBound) (hc : c.valid) (hd : d.valid) :
    (ConfBound.undercut c d).toConfidence (undercut_valid hc hd) =
    Confidence.undercut (c.toConfidence hc) (d.toConfidence hd) := by
  simp [ConfBound.undercut, Confidence.undercut, ConfBound.toConfidence]
  ring

-- Similarly for rebut, loebDiscount, multiplication
```

This shows that the syntactic type system is **sound** with respect to the semantic model.

---

## 7. Complete Soundness Theorem

### 7.1 Statement

**Theorem** (Confidence Soundness): For any CLAIR program:

1. **Static**: All types in a well-formed typing derivation have valid confidence bounds.

2. **Dynamic**: Evaluation preserves confidence validity.

3. **Semantic**: The syntactic confidence operations faithfully model the semantic operations.

### 7.2 Corollary: Type Safety Implies Confidence Safety

If we have type safety (progress + preservation), then:
- Every intermediate term in evaluation has valid confidence
- The final value (if evaluation terminates) has valid confidence

Combined with the typing validity theorem:
- **All observable confidence values are in [0,1]**

---

## 8. Required Lean Additions

### 8.1 Immediate Work

1. **Add validity proofs to `ConfBound`** in `CLAIR/Syntax/Types.lean`:

```lean
namespace ConfBound

theorem mul_valid (a b : ConfBound) (ha : a.valid) (hb : b.valid) :
    (a * b).valid := by
  constructor
  · exact mul_nonneg ha.1 hb.1
  · calc a * b ≤ a * 1 := mul_le_mul_of_nonneg_left hb.2 ha.1
           _ = a := mul_one a
           _ ≤ 1 := ha.2

theorem oplus_valid (a b : ConfBound) (ha : a.valid) (hb : b.valid) :
    (oplus a b).valid := by
  constructor
  · -- a + b - ab ≥ 0 iff a + b(1-a) ≥ 0
    have h1 : 0 ≤ 1 - a := by linarith [ha.2]
    have h2 : 0 ≤ b * (1 - a) := mul_nonneg hb.1 h1
    linarith [ha.1]
  · -- a + b - ab ≤ 1 iff a + b(1-a) ≤ 1
    have h1 : b * (1 - a) ≤ 1 - a := by
      apply mul_le_of_le_one_left
      · linarith [ha.2]
      · exact hb.2
    linarith [ha.2]

theorem undercut_valid (c d : ConfBound) (hc : c.valid) (hd : d.valid) :
    (undercut c d).valid := by
  constructor
  · exact mul_nonneg hc.1 (by linarith [hd.2])
  · calc c * (1 - d) ≤ 1 * (1 - d) := by
          apply mul_le_mul_of_nonneg_right hc.2
          linarith [hd.2]
       _ = 1 - d := one_mul _
       _ ≤ 1 := by linarith [hd.1]

theorem rebut_valid (c_for c_against : ConfBound)
    (hf : c_for.valid) (ha : c_against.valid) :
    (rebut c_for c_against).valid := by
  simp only [rebut]
  split_ifs with h
  · -- Edge case: 1/2 is valid
    constructor <;> norm_num
  · constructor
    · -- c_for / (c_for + c_against) ≥ 0
      apply div_nonneg hf.1
      linarith [hf.1, ha.1]
    · -- c_for / (c_for + c_against) ≤ 1
      have sum_pos : 0 < c_for + c_against := by
        cases' (hf.1.lt_or_eq) with hlt heq
        · linarith [ha.1]
        · cases' (ha.1.lt_or_eq) with hlt' heq'
          · linarith
          · exfalso; apply h; linarith
      rw [div_le_one sum_pos]
      linarith [ha.1]

theorem loebDiscount_valid (c : ConfBound) (hc : c.valid) :
    (loebDiscount c).valid :=
  mul_valid c c hc hc

end ConfBound
```

2. **Add `allConfidencesValid` predicate** to `Expr`:

```lean
/-- All confidence values in an expression are valid [0,1] -/
def Expr.allConfidencesValid : Expr → Prop
  | belief v c j => c.valid ∧ v.allConfidencesValid ∧ j.allConfidencesValid
  | pair e₁ e₂ => e₁.allConfidencesValid ∧ e₂.allConfidencesValid
  | app e₁ e₂ => e₁.allConfidencesValid ∧ e₂.allConfidencesValid
  -- ... other constructors
  | _ => True
```

3. **Modify typing rules** to enforce validity:

Either add explicit validity premises to `HasType.belief`, or use a validated confidence type.

### 8.2 Future Work

- Prove the embedding homomorphism theorems
- Prove evaluation preserves validity
- Connect to type safety proof

---

## 9. Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Validity proofs for ConfBound | 0.95 | Same algebra as semantic proofs |
| Typing preserves validity | 0.85 | Straightforward induction, needs belief rule fix |
| Evaluation preserves validity | 0.90 | Each step preserves by operation bounds |
| Semantic embedding is sound | 0.95 | Pure algebra |
| All proofs completable in Lean | 0.80 | Needs careful case work |

---

## 10. Impact on Other Tasks

### Task 8.2 (Type Safety)
- Type safety depends on confidence soundness for preservation
- Defeat operations change confidence; need bounds for valid typing

### Task 8.4 (Extract Interpreter)
- Extracted interpreter inherits confidence soundness
- Can validate runtime confidence values

### Task 2.24 (Type Inference)
- Inference needs confidence operations to be well-defined
- Bounds proofs ensure principal types have valid confidence

---

## 11. Conclusion

Confidence soundness for CLAIR is achievable through:

1. **Bounds proofs for syntactic operations**: Direct algebraic proofs on ℚ, paralleling the semantic proofs on ℝ.

2. **Typing judgment modification**: Either add validity premises to belief constructor, or use a validated confidence subtype.

3. **Evaluation preservation**: Follows from operation bounds and structural induction on step rules.

4. **Semantic embedding**: The syntactic operations faithfully model semantic operations via a homomorphism.

**Key insight**: The dual representation (ℚ for syntax, ℝ for semantics) is sound because:
- The algebraic properties are identical
- ℚ embeds into ℝ
- The operations on ℚ are restrictions of operations on ℝ

**Estimated effort**:
- Validity proofs: ~50 lines
- Typing validity theorem: ~100 lines
- Evaluation validity: ~80 lines
- Embedding proofs: ~30 lines

---

## 12. References

### CLAIR Internal

- Thread 8: exploration/thread-8-verification.md (semantic confidence)
- Thread 8.1-impl: exploration/thread-8.1-impl-syntax-implementation.md
- Thread 8.2: exploration/thread-8.2-type-safety.md
- Lean confidence: formal/lean/CLAIR/Confidence/*.lean
- Lean syntax: formal/lean/CLAIR/Syntax/Types.lean

### Prior Art

- Wright, A.K. & Felleisen, M. (1994). "A Syntactic Approach to Type Soundness."
- Orchard, D., Liepelt, V., & Eades, H. (2019). "Quantitative Program Reasoning with Graded Modal Types."
- Jøsang, A. (2016). "Subjective Logic." (confidence algebra)

---

*Thread 8.3 Status: Substantially explored. Proof strategy complete. Ready for Lean implementation.*
