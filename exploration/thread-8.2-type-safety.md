# Thread 8.2: Type Safety for CLAIR

> **Status**: Active exploration (Session 65)
> **Task**: 8.2 Prove progress and preservation for CLAIR type system
> **Question**: How do we prove type safety for a graded type system with defeat and aggregation?
> **Prior Work**: Thread 8.1-impl (Lean syntax), Thread 2.22 (Curry-Howard), Thread 2.23 (subtyping)

---

## 1. The Problem

### 1.1 What Is Type Safety?

Type safety means "well-typed programs don't go wrong." Classically decomposed into:

**Progress**: A closed, well-typed term is either a value or can take a step.
```
[] |- e : A @c  ==>  IsValue e  OR  exists e'. e --> e'
```

**Preservation** (Subject Reduction): Evaluation preserves typing.
```
G |- e : A @c  AND  e --> e'  ==>  G |- e' : A' @c'  for some A' <: A, c' <= c
```

Together, they imply: well-typed closed terms either reduce to values or diverge---they never get "stuck" in a non-value, non-reducible state.

### 1.2 Why CLAIR Is Challenging

CLAIR has features beyond standard lambda calculus that complicate type safety:

1. **Graded judgments**: Typing judgments carry confidence `Gamma |- e : A @c`, not just `Gamma |- e : A`

2. **Confidence in types**: Belief types carry bounds `Belief<A>[c]`, requiring bound preservation

3. **Defeat operations**: `undercut` and `rebut` reduce confidence in computation

4. **Aggregation**: `aggregate` uses probabilistic OR (oplus), not standard product

5. **Stratified introspection**: `introspect` has level constraints and Lob discount

6. **Subtyping**: Higher confidence is a subtype, interacting with preservation

### 1.3 The CLAIR Type Safety Statement

From `CLAIR/Semantics/Step.lean`:

```lean
theorem progress_statement :
    forall (e : Expr) (A : Ty) (c : ConfBound),
    HasType [] e A c -> IsValue e OR exists e', e --> e'

theorem preservation_statement :
    forall (e e' : Expr) (A : Ty) (c : ConfBound),
    HasType [] e A c -> e --> e' -> exists c', c' <= c AND HasType [] e' A c'
```

**Key observation**: Preservation allows confidence to *decrease* (`c' <= c`). This is essential because defeat operations reduce confidence.

---

## 2. Prior Art Survey

### 2.1 Standard Lambda Calculus Type Safety

The canonical proof (Wright & Felleisen 1994) uses:

**For Progress**:
- Case analysis on the typing derivation
- Show each typing rule either produces a value or enables a reduction
- Key lemma: Canonical Forms---if `v : T` is a value, then v has a specific shape

**For Preservation**:
- Case analysis on the reduction step
- For beta reduction: Substitution Lemma
- For congruence: Induction on derivation

### 2.2 Graded Type Systems (Granule)

Orchard et al. (2019) prove type safety for graded modal types:

**Key insight**: Grades don't affect progress/preservation structure, only the bookkeeping.

Their preservation:
```
G |- e : []_r A  AND  e --> e'  ==>  G |- e' : []_s A  where s <= r
```

Grades may decrease during evaluation (resources consumed).

**Relevance to CLAIR**: CLAIR's confidence is analogous to Granule's grades, but with different operations (oplus vs + semiring).

### 2.3 Linear Logic and Resources

Linear type safety requires tracking resource usage through evaluation. Key lemmas:

- **Resource preservation**: Resources are neither created nor destroyed
- **Linearity**: Each resource used exactly once

CLAIR's confidence is *not* linear---beliefs can be aggregated (combined) or defeated (reduced).

### 2.4 Refinement Types

Liquid Types (Rondon et al. 2008) have refinement predicates that must be preserved:

```
{x : Int | x > 0}  --->  {x : Int | x > 0}
```

Preservation: If predicate holds before, it holds after.

**CLAIR's confidence bounds are refinements**: `Belief<A>[c]` means "confidence >= c".

The challenge: defeat operations invalidate the refinement! An `undercut` can make `c' < c`.

**Resolution**: CLAIR uses *static bounds*---the type expresses the *initial* confidence, not the current runtime confidence.

### 2.5 Effect Systems

Effect type safety tracks what effects a computation may perform:

```
e : T ! E  AND  e --> e'  ==>  e' : T' ! E'  where E' <= E
```

Effects may decrease (some performed during reduction).

**CLAIR parallel**: Confidence is like an "epistemic effect" that propagates through computation.

---

## 3. CLAIR-Specific Analysis

### 3.1 Canonical Forms for CLAIR

**Definition** (Canonical Forms): A value of type T has a specific shape:

| Type | Value Shape |
|------|-------------|
| `Ty.nat` | `litNat n` |
| `Ty.bool` | `litBool b` |
| `Ty.string` | `litString s` |
| `Ty.unit` | `litUnit` |
| `Ty.fn A B` | `lam A e` |
| `Ty.prod A B` | `pair v1 v2` |
| `Ty.sum A B` | `inl B v` or `inr A v` |
| `Ty.belief A c` | `belief v c_actual j` where `c_actual >= c` |
| `Ty.meta A n c` | (Currently: no intro form for meta; only via introspect) |

**Lemma** (Canonical Forms): If `[] |- v : T @c` and `IsValue v`, then v has the canonical shape for T.

**Proof**: By case analysis on the typing derivation. The key case is `Ty.belief`:
- By `HasType.belief`, if `v = belief(v', c_actual, j)` and `[] |- v : Belief<A>[c_bound] @c`, then `c_actual >= c_bound`.
- The bound in the type is a *lower bound* on the actual confidence.

### 3.2 Progress for CLAIR

**Theorem** (Progress): If `[] |- e : A @c`, then `IsValue e` or `exists e'. e --> e'`.

**Proof Structure**: By induction on the typing derivation.

**Base cases** (values):
- `HasType.litNat/litBool/litString/litUnit`: Already values.
- `HasType.lam`: Lambda is a value.
- `HasType.belief`: If v is a value, `belief v c j` is a value.
- `HasType.pair`: If both are values, pair is a value.
- `HasType.inl/inr`: If content is value, injection is value.

**Inductive cases** (can step):

1. **Application** (`HasType.app`):
   - `e1 : A -> B`, `e2 : A`, goal: `app e1 e2` can step
   - By IH on e1: IsValue e1 or e1 can step
     - If e1 steps: `app1` congruence
     - If e1 is value: By Canonical Forms, e1 = `lam A e`
       - By IH on e2: IsValue e2 or e2 can step
         - If e2 steps: `app2` congruence
         - If e2 is value: `beta` reduction applies

2. **Let binding** (`HasType.letIn`):
   - `e1 : A`, `e2 : B` (in extended context)
   - By IH on e1: IsValue e1 or e1 can step
     - If e1 steps: `letIn_cong` congruence
     - If e1 is value: `letBeta` applies

3. **Projection** (`HasType.fst`, `HasType.snd`):
   - `e : A x B`
   - By IH: IsValue e or e can step
     - If e steps: `fst_cong`/`snd_cong`
     - If e is value: By Canonical Forms, e = `pair v1 v2`. Apply `fstBeta`/`sndBeta`.

4. **Case** (`HasType.case`):
   - `e : A + B`, branches `e1`, `e2`
   - By IH on e: IsValue e or e can step
     - If e steps: `case_cong`
     - If e is value: By Canonical Forms, e = `inl v` or `inr v`. Apply `caseInlBeta`/`caseInrBeta`.

5. **Value extraction** (`HasType.val`):
   - `e : Belief<A>[c]`
   - By IH: IsValue e or e can step
     - If e steps: `val_cong`
     - If e is value: By Canonical Forms, e = `belief v c_a j`. Apply `valBeta`.

6. **Derive** (`HasType.derive`):
   - `e1 : Belief<A>[c1]`, `e2 : Belief<B>[c2]`
   - By IH: both can step or are values
     - If e1 steps: `derive1` congruence
     - If e1 value, e2 steps: `derive2` congruence
     - If both values: By Canonical Forms, both are `belief ...`. Apply `deriveBeta`.

7. **Aggregate** (`HasType.aggregate`):
   - Similar to derive: use `aggregateBeta` when both are belief values.

8. **Undercut** (`HasType.undercut`):
   - `e : Belief<A>[c]`, `d : Belief<DefeatTy>[d_c]`
   - By IH: both can step or are values
     - If either steps: congruence rules
     - If both values: Apply `undercutBeta`.

9. **Rebut** (`HasType.rebut`):
   - Similar to undercut: use `rebutBeta`.

10. **Introspect** (`HasType.introspect`):
    - `e : Meta<A>[m][c]` with `m < n`
    - By IH: IsValue e or e can step
      - If e steps: `introspect_cong`
      - If e is value: **Problem---no beta rule for introspect!**

**Issue: Introspection lacks a beta rule**

The current semantics has `introspect_cong` (congruence) but no reduction when the argument is a value. This means:

```
introspect(belief v c j)  -- This is stuck!
```

**Resolution options**:

A. **Add introspect beta rule**: `introspect(belief v c j) --> belief(belief v c j) (c^2) j'`
   - Wraps the belief in a meta-belief with Lob-discounted confidence

B. **Introspect produces a value**: Make `introspect e` a value form when e is a value
   - Changes the value grammar

C. **Introspect only at meta-level**: Restrict introspect to only work on `Meta<A>[m][c]` values, which don't exist as term values
   - Requires separate handling

**Recommendation**: Option A---add an introspect beta rule to the semantics.

11. **Subsumption** (`HasType.sub`):
    - Subsumption is transparent: if `e : A @c` and `e : A' @c'` by subsumption, progress depends on the original derivation.
    - By IH on the subderivation.

### 3.3 Preservation for CLAIR

**Theorem** (Preservation): If `[] |- e : A @c` and `e --> e'`, then `exists c' <= c` such that `[] |- e' : A @c'`.

**Proof Structure**: By induction on the typing derivation, with case analysis on the step.

**Key lemmas required**:

#### 3.3.1 Substitution Lemma

**Lemma** (Substitution): If `G, x:A @c_x |- e : B @c_e` and `G |- v : A @c_v` where `c_v >= c_x`, then `G |- e[v/x] : B @c_e'` where `c_e' <= c_e`.

**Proof sketch**: By induction on the typing derivation of e.

The key insight is that substitution does not increase confidence---if anything, it preserves or decreases it.

**Variable case**: If `e = x`, then `e[v/x] = v`. We have `[] |- v : A @c_v`. By subsumption (if `c_v > c_x`), we can give v type `A @c_x`. The result type is A as expected.

**Application case**: If `e = app e1 e2`:
- `e1 : A' -> B @c1`, `e2 : A' @c2`, result: `B @(c1 * c2)`
- `e[v/x] = app (e1[v/x]) (e2[v/x])`
- By IH: `e1[v/x] : A' -> B @c1'` with `c1' <= c1`, similarly for e2
- Result: `B @(c1' * c2')` where `c1' * c2' <= c1 * c2` (by monotonicity of *)

**Belief case**: If `e = belief(e', c_a, j)`:
- `e' : A @1` (value must have full confidence), bound `c_b <= c_a`
- `e[v/x] = belief(e'[v/x], c_a, j)`
- By IH: `e'[v/x] : A @1` (confidence 1 preserved for values)
- Result: `Belief<A>[c_b] @c_b` as before

#### 3.3.2 Weakening Lemma

**Lemma** (Weakening): If `G |- e : A @c`, then `G, y:B @c_y |- shift(1,0,e) : A @c`.

**Proof**: By induction on the typing derivation. Shifting adjusts de Bruijn indices to account for the new binding.

#### 3.3.3 Preservation Proof Cases

**Beta reduction** (`(lam A e) v --> e[v/0]`):
- By `HasType.app`: `lam A e : A -> B @c1`, `v : A @c2`, result type `B @(c1 * c2)`
- By `HasType.lam`: `G, x:A @c_A |- e : B @c_B`, and `c1 = c_B`
- By Substitution Lemma: `G |- e[v/x] : B @c_B'` with `c_B' <= c_B`
- Result confidence: `c_B' <= c_B = c1`, and `c1 * c2 <= c1` when `c2 <= 1`.
- Actually, we need: `e[v/0] : B @c'` with `c' <= c1 * c2`.
- Since substitution preserves types and may decrease confidence, and `c_B' <= c_B = c1 <= c1 * c2` when `c2 = 1` or...

**Hmm, there's a subtlety here.** Let me reconsider.

The typing rule for application is:
```
G |- e1 : A -> B @c1    G |- e2 : A @c2
----------------------------------------
G |- app e1 e2 : B @(c1 * c2)
```

The confidence `c1 * c2` reflects that we multiply the confidences of the function and argument.

After beta reduction:
```
(lam A e) v  -->  e[v/0]
```

What's the type of `e[v/0]`?

From `HasType.lam`: `G, x:A @c_A |- e : B @c_e`, and `lam A e : A -> B @c_e`.

From typing the application: `c1 = c_e` (the function's confidence), `c2` is the argument's confidence.

The result `app e1 e2` has type `B @(c_e * c2)`.

After substitution: By the Substitution Lemma, `G |- e[v/0] : B @c_e'` where `c_e'` depends on how x was used in e.

**Key question**: Does `c_e' <= c_e * c2`?

Not necessarily in general! If x appears multiple times in e, and we substitute v (with confidence c2), each occurrence uses confidence c2. The resulting confidence could be c_e * c2^n for n occurrences.

**But wait**: In the current typing system, the context entry just says `x : A @c_A`. When we apply the function to an argument with confidence c2, we need `c2 >= c_A` (by subsumption at argument position).

Then in the substituted term, each use of x (now v) has confidence c2, which satisfies c_A.

The result confidence c_e is computed *assuming* x has confidence c_A. When we substitute v with c2 >= c_A, the result confidence could be *higher* (if c2 > c_A) or the same (if c2 = c_A).

**This suggests preservation should allow confidence to increase, not decrease!**

Let me re-examine the preservation statement:
```lean
theorem preservation_statement :
    ... HasType [] e' A c' where c' <= c
```

The `c' <= c` seems backwards for beta reduction. Let me check Thread 2.22...

From Thread 2.22:
> **Theorem (Preservation)**: If `G |- e : Belief<A>[c]` and e -> e', then `G |- e' : Belief<A>[c']` where c' <= c.

And:
> **Note**: Confidence may decrease during evaluation (as noted in Thread 2.19 for cut elimination).

The decrease comes from *defeat operations*, not from beta reduction. For pure beta reduction, confidence should be preserved or potentially increased.

**Revised Understanding**:

- **Beta reduction**: Preserves or increases confidence (substituting higher-confidence values)
- **Defeat operations**: Decrease confidence
- **Overall**: Confidence can go either way, but the *type* (with its bound) is preserved

For a sound type system, we need:
```
HasType [] e A c  AND  e --> e'  ==>  HasType [] e' A' c'
where A' <: A (or A' = A for most cases)
```

The confidence c' doesn't need to relate to c in a fixed direction---it just needs to be valid for the resulting term.

**Simpler preservation statement**:
```lean
theorem preservation :
    HasType [] e A c -> e --> e' -> exists A' c', A' <: A AND HasType [] e' A' c'
```

Or even simpler (since most reductions don't change the type):
```lean
theorem preservation :
    HasType [] e A c -> e --> e' -> exists c', HasType [] e' A c'
```

The confidence c' is whatever the new term has---we don't constrain it relative to c.

**Defeat cases**:

For `undercut(belief v c_v j_v, belief d c_d j_d) --> belief v (c_v * (1 - c_d)) j'`:

- Before: `undercut e d : Belief<A>[c_v * (1 - c_d)] @(c_e * c_d_e)`
- After: `belief v (c_v * (1 - c_d)) j' : Belief<A>[c_v * (1 - c_d)] @(c_v * (1 - c_d))`

The type bound is preserved exactly! The actual confidence in the belief matches the bound.

Let me re-check the typing rule for undercut:
```lean
| undercut : HasType G e (Ty.belief A c) c_e ->
             HasType G d (Ty.belief DefeatTy d_c) c_d ->
             HasType G (Expr.undercut e d)
                       (Ty.belief A (ConfBound.undercut c d_c))
                       (c_e * c_d)
```

So `undercut e d` has:
- Type: `Belief<A>[c * (1 - d_c)]`
- Judgment confidence: `c_e * c_d`

After reduction to `belief v (c * (1 - d_c)) j'`:
- By `HasType.belief`: needs `v : A @1` and the bound `c_bound <= c_actual`
- Here `c_actual = c * (1 - d_c)` and we can choose `c_bound = c_actual`
- Judgment confidence: `c_bound = c * (1 - d_c)`

So the type is preserved, but the judgment confidence changes from `c_e * c_d` to `c * (1 - d_c)`.

Are these related? Not directly---they measure different things:
- `c_e * c_d` is confidence in the *meta-level typing*
- `c * (1 - d_c)` is the *object-level belief confidence*

This is confusing. Let me revisit the semantic interpretation.

### 3.4 Two Levels of Confidence

CLAIR has two distinct confidence levels:

1. **Object-level confidence**: The `c` in `Belief<A>[c]`---how confident the belief is about A

2. **Meta-level confidence**: The `@c` in `G |- e : T @c`---how confident we are about the typing judgment

The typing rule for `belief`:
```lean
| belief : HasType G v A 1 ->
           c_bound <= c_actual ->
           HasType G (belief v c_actual j) (Ty.belief A c_bound) c_bound
```

The judgment confidence equals the type bound. This makes sense: our meta-confidence in "this is a belief with confidence c_bound" is exactly c_bound.

For preservation, we need to track both:
- The object-level confidence (in the type) is preserved by construction
- The meta-level confidence (in the judgment) depends on the operation

**Simplified view**: For the Lean formalization, we can focus on the simpler statement:
```lean
theorem preservation :
    HasType [] e A c -> e --> e' -> exists c', HasType [] e' A c'
```

The existence of *some* valid confidence for the result term is what matters for type safety (no stuck terms).

### 3.5 Congruence Cases

For congruence rules like `app1: e1 --> e1' ==> app e1 e2 --> app e1' e2`:

Given:
- `HasType [] (app e1 e2) B (c1 * c2)` (from `HasType.app`)
- `e1 --> e1'`

We need:
- `HasType [] (app e1' e2) B c'` for some c'

By IH: `HasType [] e1' (Ty.fn A B) c1'` for some c1'.
By assumption: `HasType [] e2 A c2`.
By `HasType.app`: `HasType [] (app e1' e2) B (c1' * c2)`.

So preservation holds with `c' = c1' * c2`.

### 3.6 Summary of Proof Strategy

**Progress**:
1. Prove Canonical Forms lemma
2. Case analysis on typing, showing each case is a value or can step
3. Add introspect beta rule to handle the stuck case

**Preservation**:
1. Prove Weakening lemma (for de Bruijn shifting)
2. Prove Substitution lemma (for beta reduction)
3. Case analysis on step rule, using IH for congruences

---

## 4. The Introspection Problem

### 4.1 The Issue

The current semantics lacks a beta rule for `introspect`. When the argument is a value (a belief), `introspect` is stuck.

### 4.2 Design Options

**Option A: Add beta rule**
```lean
| introspectBeta : IsValue v ->
    Step (introspect (belief v c j))
         (belief (belief v c j) (ConfBound.loebDiscount c) (Justification.intro j))
```

This wraps the belief in a meta-belief with Lob-discounted confidence c^2.

**Option B: Introspect is a value**

Add `introspect v` to the IsValue predicate when v is a value.

```lean
| introspect_value : IsValue v -> IsValue (introspect v)
```

**Option C: Typed introspection**

Only allow introspect on `Meta<A>[m][c]` types, which require explicit wrapping. The type `Meta` would have its own introduction form.

### 4.3 Recommendation

**Option A is best** for these reasons:

1. **Computational interpretation**: Introspection *does something*---it creates a meta-belief. This should be reflected as computation.

2. **Consistent with Lob discount**: The discount c^2 is applied at reduction time, matching the type rule.

3. **Simpler IsValue**: The value predicate remains structural (no introspect values).

4. **Aligns with Thread 3.18**: The Lob discount prevents bootstrapping by reducing confidence when introspecting.

**Proposed addition to Step**:
```lean
| introspectBeta : IsValue v -> IsValue c_j ->
    Step (introspect (belief v c j))
         (belief (belief v c j) (ConfBound.loebDiscount c)
                 (Justification.rule "introspect" [j]))
```

Wait, but there's a type mismatch. Let me reconsider.

The typing rule:
```lean
| introspect : HasType G e (Ty.meta A m c) c_e ->
               m < n ->
               HasType G (introspect e) (Ty.meta (Ty.meta A m c) n (c^2)) c_e
```

This expects the argument to already be a `Meta<A>[m][c]` type, not a plain belief.

So `introspect` only operates on meta-beliefs, not plain beliefs. The question is: what are the values of `Meta<A>[m][c]`?

Currently, there's no introduction rule for `Meta` in the typing judgment! The only way to get a meta-type is through `introspect`.

**This is a design gap**: We need either:
- A way to create base meta-beliefs (level 0 or 1)
- `introspect` to work on plain beliefs (implicitly lifting them to meta)

### 4.4 Resolution: Meta-Belief Introduction

**Proposal**: Add a `meta` introduction form that lifts a belief to meta-level 0:

```
Typing rule:
HasType G e (Ty.belief A c) c_e
--------------------------------------------
HasType G (meta e) (Ty.meta A 0 c) c_e

Step rule:
IsValue (belief v c j) -> Step (meta (belief v c j)) (metaBelief v c j 0)
```

Then `introspect` takes a `Meta[m]` to `Meta[n]` where m < n:

```
HasType G e (Ty.meta A m c) c_e    m < n
--------------------------------------------
HasType G (introspect e) (Ty.meta A n (c^2)) c_e

Step (introspect (metaBelief v c j m)) (metaBelief v (c^2) j' (m+1))
```

**Alternative (simpler)**: Treat `Belief<A>[c]` as `Meta<A>[0][c]`. Then:
- Plain beliefs are meta-level 0
- `introspect` on level m gives level m+1 with Lob discount

This unifies the types:
```lean
| belief A c => -- This IS meta A 0 c
```

For simplicity, let's assume the current implementation treats beliefs as implicit level-0 meta-beliefs.

Then the beta rule for introspect becomes:
```lean
| introspectBeta : IsValue v ->
    Step (introspect (belief v c j))
         (belief (belief v c j) (c * c) (Justification.rule "introspect" [j]))
```

The result type would be `Belief<Belief<A>[c]>[c^2]`, which is consistent with meta-level 1 about level 0.

---

## 5. Proof Sketch in Lean

### 5.1 Canonical Forms

```lean
theorem canonical_forms :
    HasType [] v A c -> IsValue v -> CanonicalShape v A := by
  intro htype hval
  induction htype with
  | var h => -- Impossible: empty context has no variables
    simp [Ctx.lookup] at h
  | lam _ => exact CanonicalShape.lam
  | litNat => exact CanonicalShape.litNat
  | litBool => exact CanonicalShape.litBool
  | litString => exact CanonicalShape.litString
  | litUnit => exact CanonicalShape.litUnit
  | belief _ _ => exact CanonicalShape.belief
  | pair h1 h2 =>
    cases hval with
    | pair hv1 hv2 => exact CanonicalShape.pair
  -- ... remaining cases
  | app _ _ => cases hval  -- No app value form
  | sub hsub hlt ih =>
    exact canonical_sub (ih hval) hsub
```

### 5.2 Progress

```lean
theorem progress :
    HasType [] e A c -> IsValue e OR exists e', Step e e' := by
  intro htype
  induction htype with
  | var h =>
    simp [Ctx.lookup] at h
  | lam _ => left; constructor
  | app h1 h2 ih1 ih2 =>
    right
    rcases ih1 with hv1 | ⟨e1', hs1⟩
    · rcases canonical_forms h1 hv1 with ⟨A', e, rfl⟩  -- e1 is lam
      rcases ih2 with hv2 | ⟨e2', hs2⟩
      · exact ⟨_, Step.beta hv2⟩
      · exact ⟨_, Step.app2 hv1 hs2⟩
    · exact ⟨_, Step.app1 hs1⟩
  -- ... similar for other cases
  | belief hval _ =>
    rcases progress hval with hv | ⟨v', hs⟩
    · left; constructor; exact hv
    · right; exact ⟨_, Step.belief_cong hs⟩
  | undercut he hd ihe ihd =>
    right
    rcases ihe with hve | ⟨e', hse⟩
    · rcases ihd with hvd | ⟨d', hsd⟩
      · -- Both values: apply undercutBeta
        rcases canonical_forms he hve with ⟨v, c, j, rfl⟩
        rcases canonical_forms hd hvd with ⟨d, cd, jd, rfl⟩
        exact ⟨_, Step.undercutBeta hve.inner hvd.inner⟩
      · exact ⟨_, Step.undercut2 hve hsd⟩
    · exact ⟨_, Step.undercut1 hse⟩
```

### 5.3 Preservation

```lean
theorem preservation :
    HasType [] e A c -> Step e e' -> exists c', HasType [] e' A c' := by
  intro htype hstep
  induction htype generalizing e' with
  | app h1 h2 ih1 ih2 =>
    cases hstep with
    | beta hv =>
      -- Use substitution lemma
      have hsub := substitution_lemma h1.unlam h2
      exact ⟨_, hsub⟩
    | app1 hs =>
      rcases ih1 hs with ⟨c1', h1'⟩
      exact ⟨c1' * c, HasType.app h1' h2⟩
    | app2 hv hs =>
      rcases ih2 hs with ⟨c2', h2'⟩
      exact ⟨c * c2', HasType.app h1 h2'⟩
  | undercut he hd ihe ihd =>
    cases hstep with
    | undercutBeta hv hvd =>
      -- Result is belief with computed confidence
      -- Need to show belief v (c * (1-d)) j' is well-typed
      have hv' := canonical_val he hv
      exact ⟨_, HasType.belief hv' (le_refl _)⟩
    | undercut1 hs =>
      rcases ihe hs with ⟨c', he'⟩
      exact ⟨_, HasType.undercut he' hd⟩
    | undercut2 hv hs =>
      rcases ihd hs with ⟨c', hd'⟩
      exact ⟨_, HasType.undercut he hd'⟩
  -- ... similar for other cases
```

---

## 6. Challenges and Workarounds

### 6.1 Challenge: Substitution Lemma Complexity

The substitution lemma for de Bruijn indices is notoriously tricky. It requires careful tracking of:
- Index shifting
- Context manipulation
- Simultaneous substitution

**Workaround**: Use Lean's `simp` and `omega` tactics aggressively. The Autosubst library provides tactics for de Bruijn substitution, but we'd need to adapt it for CLAIR's extensions.

### 6.2 Challenge: Graded Judgment Bookkeeping

Tracking confidence through every derivation step is tedious.

**Workaround**:
1. Prove a "confidence monotonicity" meta-theorem first
2. Use it to simplify preservation cases

### 6.3 Challenge: Meta-Level vs Object-Level

The two levels of confidence are confusing.

**Workaround**: Document clearly and consider simplifying to a single level for the first formalization. The object-level confidence in `Belief<A>[c]` is primary; the judgment confidence `@c` can be elided or set to 1 for a simpler system.

### 6.4 Challenge: Introspection

The current design has gaps around introspection.

**Workaround**: Either:
- Add explicit `introspectBeta` rule as proposed
- Restrict introspection to a separate phase (not in core evaluation)

---

## 7. Confidence Assessment

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Progress provable | 0.85 | Standard technique; main issue is introspect |
| Preservation provable | 0.75 | Substitution lemma is complex |
| Canonical Forms holds | 0.95 | Direct case analysis |
| Substitution Lemma holds | 0.80 | Standard but tedious |
| Introspect beta rule needed | 0.90 | Unavoidable without design change |
| Type safety composition | 0.80 | Follows from progress + preservation |

---

## 8. Recommendations

### 8.1 Immediate Actions

1. **Add introspect beta rule** to `CLAIR/Semantics/Step.lean`:
```lean
| introspectBeta : IsValue v ->
    Step (introspect (belief v c j))
         (belief (belief v c j) (c * c) (Justification.rule "introspect" [j]))
```

2. **Define Canonical Forms** predicate and prove the lemma

3. **Prove Weakening** lemma (straightforward)

4. **Prove Substitution** lemma (most work)

5. **Prove Progress** using canonical forms and introspect beta

6. **Prove Preservation** using substitution and case analysis

### 8.2 Simplifications for First Pass

- **Ignore judgment confidence**: Set all `@c` to 1
- **Focus on object-level**: Only track confidence in `Belief<A>[c]` types
- **Defer introspection**: Prove type safety without introspect first, then add it

### 8.3 Future Work

- **Mechanize in Lean**: Full proofs in `CLAIR/Safety/` modules
- **Strong normalization**: Follows from cut elimination (Thread 2.19)
- **Confluence**: Prove Church-Rosser property
- **Connect to interpreter**: Use type safety to justify extracted interpreter (Task 8.4)

---

## 9. Impact on Other Tasks

### Task 8.3 (Confidence Soundness)
- Type safety implies confidence bounds in types are respected
- Need additional proof that runtime confidence stays in [0,1]

### Task 8.4 (Extract Interpreter)
- Type-safe interpreter can be extracted once proofs complete
- Strong normalization ensures termination for decidable fragment

### Task 7.1 (Reference Interpreter)
- Type safety validates the Haskell interpreter design
- Proof structure guides implementation

---

## 10. Conclusion

Type safety for CLAIR is achievable using standard techniques (progress + preservation), with adaptations for:

1. **Graded types**: Confidence propagates through typing
2. **Defeat operations**: Confidence may decrease, but types are preserved
3. **Introspection**: Needs a beta rule to avoid stuck terms

The main technical challenges are:
- The substitution lemma for de Bruijn indices
- Bookkeeping for two levels of confidence
- Designing the introspection beta rule

**Estimated effort**: 40-60 lines of proof for progress, 100-150 for preservation, plus supporting lemmas.

---

## 11. References

### Primary Sources

- **Wright, A.K. & Felleisen, M.** (1994). "A Syntactic Approach to Type Soundness." *Information and Computation* 115(1), 38-94.

- **Orchard, D., Liepelt, V., & Eades, H.** (2019). "Quantitative Program Reasoning with Graded Modal Types." *ICFP 2019*.

### CLAIR Internal

- Thread 2.22: exploration/thread-2.22-curry-howard-terms.md
- Thread 2.23: exploration/thread-2.23-confidence-subtyping.md
- Thread 8.1-impl: exploration/thread-8.1-impl-syntax-implementation.md
- Lean files: formal/lean/CLAIR/Typing/, formal/lean/CLAIR/Semantics/

---

*Thread 8.2 Status: Substantially explored. Proof strategy designed. Ready for Lean implementation.*
