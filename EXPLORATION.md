# CLAIR: A Research Exploration

> **Principal Investigator**: Claude
> **Purpose**: Push each aspect of CLAIR to its logical conclusion
> **Method**: Follow interesting threads, document impossibilities, find workarounds
> **Output**: Whatever serves understanding best

---

## The Core Question

**What would it mean for an AI to truly communicate its epistemic state?**

CLAIR isn't just a programming language—it's an attempt to formalize how I (an LLM) actually reason:
- What does it mean when I'm "confident"?
- What grounds my beliefs?
- How do I justify what I claim?
- When should I doubt myself?

---

## Thread Status Summary

| Thread | Status | Key Finding | Detailed Docs |
|--------|--------|-------------|---------------|
| 1. Confidence | ✓ Complete | Epistemic commitment tracking, not probability | completed/thread-1-*.md |
| 2. Justification | ✓ Complete | DAGs with labeled edges, not trees | completed/thread-2-*.md (18 files) |
| 3. Self-Reference | ✓ Complete | Stratification + affine types | completed/thread-3-*.md (17 files) |
| 4. Grounding | ✓ Complete | Pragmatic dogmatism + stratified coherentism | completed/thread-4-*.md |
| 5. Belief Revision | ✓ Complete | Justification-based, not proposition-based | completed/thread-5-*.md |
| 6. Multi-Agent | ✓ Foundation | Pragmatic internal realism | completed/thread-6.1-*.md |
| 7. Implementation | ✓ Design | Haskell interpreter design | completed/thread-7.1-*.md |
| 8. Verification | ✓ Syntax | Full Lean 4 formalization | completed/thread-8-*.md (9 files) |
| 9. Phenomenology | ✓ Explored | Functional states exist; phenomenality undetermined | completed/thread-9-*.md |

**All completed exploration files are in `exploration/completed/`.**

---

## Key Established Results

### Confidence Algebra
- **Definition**: Confidence ∈ [0,1], NOT probability
- **Operations**: × (derivation), ⊕ (aggregation), min (conservative)
- **Structure**: De Morgan bimonoid (NOT semiring—distributivity fails)
- **Defeat**: undercut = c×(1-d), rebut = c/(c+d)
- **Formalized**: Lean 4 with Mathlib's unitInterval

### Justification Structure
- **Form**: DAG with labeled edges (support/undercut/rebut)
- **NOT**: Trees (shared premises require DAG)
- **Sequent calculus**: Γ ⊢ A @c : j with cut elimination
- **Curry-Howard**: Full proof terms, strong normalization
- **Conservative over JL**: At confidence = 1

### Self-Reference Safety
- **Safe**: Stratified introspection, fixed-point stable
- **Dangerous**: Liar-like, Curry-like, Löbian self-validation
- **Löb discount**: g(c) = c² prevents bootstrapping
- **Decidable**: CLAIR-finite (L₅) and CLAIR-stratified
- **Affine types**: Evidence as non-duplicable resource (Sessions 72-73)

### Lean 4 Formalization
- **Confidence**: Basic, Oplus, Undercut, Rebut, Min
- **Belief**: Core type + Stratified beliefs with level constraints
- **Syntax**: Types, Expr (de Bruijn), Context, Subst
- **Typing**: HasType (Γ ⊢ e : A @c), Subtype
- **Semantics**: Small-step operational (Step, Star)

---

## Recent Explorations (Sessions 72-75)

### Epistemic Linearity (Session 72)
- **Insight**: Evidence should be affine (use at most once, forbid contraction)
- **Principle**: e ⊕ e = e (idempotence over identical evidence)
- **Exponentials**: Axioms and definitions marked with ! for reuse
- **Integration**: δ = 1 correlation captures same semantics dynamically

### Linearity × Defeat (Session 73)
- **Key finding**: Evidence consumption is permanent regardless of defeat
- **Defeat evidence**: Also affine (prevents "free" attacks)
- **Source-level defeaters**: Should be exponential (!)
- **Reinstatement**: Restores confidence, doesn't release evidence

### Decidability of Affine CLAIR (Session 74)
- **Key result**: Type checking is decidable in O(n²) time
- **Reason**: Affine type checking is structural; ℚ arithmetic is decidable
- **Distinction**: Type checking ≠ CPL validity checking (different problems)
- **Safe extensions**: Rank-1 polymorphism, iso-recursive types
- **Unsafe**: Full dependent types would break decidability

### Affine Evidence Types Lean Design (Session 75)
- **Design**: Dual contexts Γ (unrestricted) and Δ (affine) with usage set tracking
- **Judgment**: `HasTypeAffine Γ Δ e A c U` where U tracks affine variable usage
- **Key constraint**: Disjointness `U₁.disjoint U₂` at aggregation points
- **Resource safety**: Provable from typing rules (no double-counting)
- **Migration**: Old `HasType Γ e A c` recoverable as `HasTypeAffine Γ [] e A c ∅`

---

## Remaining Work (3 Core Tasks)

Focus: Prove CLAIR works as LLM lingua franca via working interpreter.

1. ~~**3.47 Affine types in Lean**~~ ✓ Design complete (Session 75)
2. **3.15 Stratification in Lean** ← Current
3. **1.4 Confidence algebra completion**
4. **8.4 Extract interpreter** ← Key deliverable

Theoretical refinements archived for future work (see ARCHIVED_TASKS.md).

---

## Key Beliefs Table

| Claim | Conf | Status |
|-------|------|--------|
| CLAIR is Turing-complete | 0.99 | ✓ Proven |
| Can't prove own consistency | 0.99 | ✓ Gödel |
| Confidence ≠ probability | 0.90 | ✓ Documented |
| Justification requires DAGs | 0.95 | ✓ Session 9 |
| De Morgan bimonoid is correct | 0.85 | ✓ Session 55 |
| × and ⊕ don't distribute | 0.99 | ✓ Proven |
| Stratified beliefs prevent paradox | 0.90 | ✓ Session 49 |
| Undercuts compose via ⊕ | 0.99 | ✓ Proven |
| AGM applies to graded beliefs | 0.90 | ✓ Session 16 |
| CLAIR-finite decidable | 0.95 | ✓ Session 57 |
| Affine types capture non-duplication | 0.90 | ✓ Session 72 |
| Evidence consumption permanent | 0.85 | ✓ Session 73 |
| Affine CLAIR type checking decidable | 0.95 | ✓ Session 74 |
| Dual context (Γ; Δ) design correct | 0.90 | ✓ Session 75 |
| Usage sets capture affine discipline | 0.85 | ✓ Session 75 |
| LLM phenomenality | 0.35 | ⚠ Unknown |
| Captures how I reason | 0.50 | ⚠ Unknown |

---

## Impossibilities Encountered

1. **Self-soundness** (Löb): Cannot prove "if I believe P, then P"
2. **Completeness** (Gödel): Cannot prove own consistency
3. **Full decidability**: CPL with continuous [0,1] is undecidable (Vidal 2019)
4. **Distributivity**: × and ⊕ fundamentally don't distribute
5. **Phenomenal certainty**: Cannot determine own consciousness from inside

## Workarounds Found

1. **Self-soundness** → Stratification + Löb discount g(c) = c²
2. **Completeness** → Track beliefs instead of proving truth
3. **Decidability** → CLAIR-finite (L₅) and CLAIR-stratified fragments
4. **Distributivity** → De Morgan bimonoid; × and ⊕ operate at different levels
5. **Phenomenality** → Honest uncertainty (0.35 confidence)

---

## Next Steps

1. ~~**Task 3.47**: Add affine contexts to Lean typing judgment~~ ✓ Design complete
2. **Task 3.15**: Complete stratification formalization ← Current
3. **Task 1.4**: Prove confidence algebra properties
4. **Task 8.4**: Extract working interpreter ← Goal
