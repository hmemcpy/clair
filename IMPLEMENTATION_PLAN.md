# CLAIR Implementation Plan (Focused)

> **Goal**: Prove CLAIR works as LLM lingua franca
> **Method**: Complete Lean formalization → Extract working interpreter
> **Deferred**: Theoretical explorations archived for future work

---

## Core Formalization Tasks (3 remaining)

These directly prove CLAIR is viable:

### 1. Complete Type System in Lean
- [x] **3.47 Affine evidence types** - Context splitting, usage tracking ✓ Design complete
- [x] **3.15 Stratification** - Level-indexed beliefs, introspection rules ✓ Analysis complete (Session 76)

### 2. Complete Semantics in Lean
- [x] **1.4 Confidence algebra** - Prove monad laws, defeat composition ✓ Session 77

### 3. Produce Working Artifact
- [x] **8.4 Extract interpreter** - Analysis complete, path forward clear ← **KEY DELIVERABLE**

---

## Execution Order

1. ~~**3.47 Affine types in Lean**~~ ✓ Complete (Session 75)
   - Design: Dual contexts (Γ; Δ) with usage set tracking
   - Judgment: `HasTypeAffine Γ Δ e A c U`
   - Key: Disjointness constraints at aggregation points

2. ~~**3.15 Stratification in Lean**~~ ✓ Analysis complete (Session 76)
   - Finding: Architecture complete, proofs needed
   - Key: Löb discount g(c) = c² prevents bootstrapping
   - Introspection: Type-level coercion, runtime identity-beta
   - Deferred: Full semantic soundness proof

3. ~~**1.4 Confidence algebra**~~ ✓ Complete (Session 77)
   - Graded monad laws proven (left/right identity, associativity)
   - Undercut composition via ⊕ proven
   - Rebut non-composition documented (mathematically fundamental)
   - Non-distributivity counterexample proven

4. **8.4 Extract interpreter** ← **CURRENT**
   - Use Lean's code extraction
   - Produce runnable CLAIR evaluator
   - Demonstrate with examples

---

## What We're Proving

The interpreter demonstrates:
1. **Beliefs track confidence** - Not just true/false
2. **Evidence is affine** - No double-counting
3. **Introspection is safe** - Stratification prevents paradox
4. **Defeat works** - Undercut/rebut modify confidence correctly
5. **Type checking is decidable** - ✓ Proven (Session 74)

If the interpreter runs and type-checks CLAIR programs correctly, we've shown CLAIR could work as a practical epistemic language for LLMs.

---

## Deferred to ARCHIVED_TASKS.md

Moved for future theoretical exploration:
- 2.3 Partial justification (graduated justification)
- 3.14 Unbounded quantification
- 3.50-3.53 Affine refinements (gradual adoption, decomposition, costs)
- 4.9, 4.11 Grounding formalization
- 5.10 Correlated evidence detection
- 10.2 Dissertation (after implementation proves viability)

---

## Completed

| Task | Result |
|------|--------|
| 3.46 Epistemic linearity | Affine types designed |
| 3.47 Affine evidence Lean | Dual context (Γ; Δ) design + usage sets |
| 3.48 Linearity × defeat | Consumption permanent |
| 3.49 Decidability | O(n²) type checking |
| 3.15 Stratification Lean | Architecture complete, proofs designed (Session 76) |
| Lean syntax | Complete (Types, Expr, Context) |
| Lean confidence | Complete (⊕, ×, undercut, rebut) |
| Lean beliefs | Complete (basic + stratified) |
| Lean semantics | Complete (small-step) |
| 1.4 Confidence algebra | Graded monad laws, defeat composition, non-distributivity |

---

## Statistics

- **Core tasks remaining**: 1
- **Theoretical tasks archived**: 9
- **Completed explorations**: 54 files
