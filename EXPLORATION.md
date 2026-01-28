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

## Recent Explorations (Sessions 72-73)

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

---

## Open Questions

### High Priority
- **3.49 Decidability of affine CLAIR** - Is type checking decidable with affine evidence?
- **3.47 Affine types in Lean** - Formalize context splitting for aggregation
- **8.4 Extract interpreter** - Produce executable from Lean formalization

### Medium Priority
- **3.50** Gradual linearity adoption
- **5.4** Dynamic epistemic logic formalization
- **4.9** Reliability metrics formalization

### See IMPLEMENTATION_PLAN.md for complete open task list (50 tasks)

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

1. **Task 3.49**: Prove decidability of affine CLAIR type checking
2. **Task 3.47**: Formalize affine evidence types in Lean
3. **Task 8.4**: Extract working interpreter from Lean
4. Continue with open tasks in IMPLEMENTATION_PLAN.md
