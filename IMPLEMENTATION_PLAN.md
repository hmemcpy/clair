# CLAIR Exploration Plan (Focused)

> **Mode**: Exploratory Research | **Driver**: Claude
> **Archived tasks**: See `ARCHIVED_TASKS.md` for deferred research directions

---

## Priority Tasks (22 remaining)

### Thread 1: Confidence
- [ ] **1.4 Formalize confidence algebra** - Complete Lean formalization. → Thread 8

### Thread 2: Justification
- [ ] **2.3 Partial justification** - Can justification be graduated? Core semantic question.

### Thread 3: Self-Reference (Core)

**Formalization**:
- [ ] **3.14 Unbounded quantification** - How to handle "beliefs about all my beliefs"?
- [ ] **3.15 Formalize stratification in Lean** - Complete the Lean formalization

**Affine Evidence Types** (HIGH PRIORITY):
- [ ] **3.47 Affine evidence types in Lean** - Full formalization with context splitting
- [ ] **3.49 Decidability of affine CLAIR** - Prove decidability of type checking ← **NEXT**
- [ ] **3.50 Gradual linearity adoption** - Gradual typing for incremental adoption
- [ ] **3.51 Evidence decomposition** - Complex evidence → affine resources
- [ ] **3.52 Affine evidence and belief revision** - Interaction with Thread 5
- [ ] **3.53 Computational costs** - Performance implications of affine tracking

### Thread 4: Grounding
- [ ] **4.9 Reliability metrics** - How to formalize reliability tractably?
- [ ] **4.11 Grounding types formalization** - GroundingType, ReliabilityMetric, Source in CLAIR

### Thread 5: Belief Revision
- [ ] **5.10 Correlated evidence** - Detection/handling of non-independent sources

### Thread 8: Formal Verification (HIGH PRIORITY)
- [ ] **8.4 Extract interpreter** - Extract runnable interpreter from Lean ← **KEY DELIVERABLE**

### Thread 10: Dissertation
- [ ] **10.2 Finalize Thesis (FINAL)** - Only after all above complete

---

## Completed Threads

See `exploration/completed/` for all finished exploration documents (51 files).

| Thread | Key Achievement |
|--------|-----------------|
| 1. Confidence | De Morgan bimonoid algebra formalized |
| 2. Justification | DAG structure, sequent calculus, cut elimination |
| 3. Self-Reference | Stratification, Löb discount, affine types designed |
| 4. Grounding | Pragmatic dogmatism + stratified coherentism |
| 5. Belief Revision | Justification-based algorithm |
| 6. Multi-Agent | Pragmatic internal realism foundation |
| 7. Implementation | Haskell interpreter design |
| 8. Verification | Full Lean 4 syntax formalization |
| 9. Phenomenology | Honest uncertainty stance |

---

## Execution Order

**Phase 1: Core Type System**
1. ~~3.46 Epistemic linearity~~ ✓
2. ~~3.48 Linearity × defeat~~ ✓
3. **3.49 Decidability of affine CLAIR** ← Current
4. 3.47 Affine types in Lean

**Phase 2: Complete Formalization**
5. 3.15 Stratification in Lean
6. 1.4 Confidence algebra completion
7. 8.4 Extract interpreter

**Phase 3: Refinements**
8. Remaining Thread 3 tasks (3.50-3.53)
9. Thread 4-5 formalization tasks
10. 10.2 Finalize thesis

---

## Statistics

- **Active tasks**: 22
- **Archived tasks**: 28 (see ARCHIVED_TASKS.md)
- **Completed explorations**: 51 files
