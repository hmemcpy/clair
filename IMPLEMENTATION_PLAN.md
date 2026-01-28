# CLAIR Exploration Plan

> **Mode**: Exploratory Research | **Driver**: Claude | **Horizon**: Until conclusions reached

## Summary

This is a research exploration plan. Each "task" is a thread to pull until it reaches bedrock (proven sound) or void (proven impossible). The goal is understanding, not production code.

**Completed explorations**: See `exploration/completed/` for all finished thread documents.

---

## Open Tasks by Thread

### Thread 1: Confidence (2 open, 2 deferred)

- [ ] **1.3 Confidence calibration** - EMPIRICAL: Cannot resolve internally. Requires external study.
- [ ] **1.4 Formalize confidence algebra** - READY: → Moves to Thread 8.
- [ ] **1.6 Subjective Logic extension** - Should we use (b,d,u,a) tuples instead of single confidence?
- [ ] **1.7 Non-independent derivations** - Multiplication rule fails when premises correlated.

### Thread 2: Justification (1 open)

- [ ] **2.3 Partial justification** - Can justification be graduated? "Partially justified" vs "fully justified"?

### Thread 3: Self-Reference (24 open)

**Quantification & Formalization**:
- [ ] **3.14 Unbounded quantification** - How to handle "beliefs about all my beliefs"?
- [ ] **3.15 Formalize stratification in Lean** - → Moves to Thread 8

**Fixed-Point & Convergence**:
- [ ] **3.28 Automatic contractivity detection** - Syntactic patterns for |f'| < 1?
- [ ] **3.29 Gradual self-reference typing** - Allow unchecked self-reference with incremental verification?
- [ ] **3.31 Probabilistic fixed-point approximation** - Random sampling for undecidable cases?

**Warnings & Thresholds**:
- [ ] **3.32 External evidence warnings** - Syntactic warnings for ungrounded self-reference?
- [ ] **3.35 Discrete Löb rounding** - Ceiling vs floor for discrete Löb discount?
- [ ] **3.36 Heterogeneous multi-level discount** - Mixed Löb functions at different levels?
- [ ] **3.37 Total epistemic cost metric** - Metric for all introspection levels?
- [ ] **3.38 Maximum introspection depth** - Impose depth limit?
- [ ] **3.39 Multi-level threshold with aggregation** - c = a ⊕ b ⊕ c^(2^k) behavior?

**Aggregation & Bootstrap**:
- [ ] **3.41 Heterogeneous aggregation thresholds** - c² ⊕ c⁴ ⊕ c⁸ effective threshold?
- [ ] **3.42 Bootstrap vulnerability analysis** - Malicious exploitation?
- [ ] **3.43 Defense by redundancy** - Aggregated introspection + defeat interaction?
- [ ] **3.44 `@independent` enforcement level** - Error vs warning?
- [ ] **3.45 Correlation inference for non-introspective sources** - General δ inference?

**Affine Evidence Types** (NEW - from Sessions 72-73):
- [ ] **3.47 Affine evidence types in Lean** - Full Lean 4 formalization with context splitting
- [ ] **3.49 Decidability of affine CLAIR** - Prove decidability of type checking ← **HIGH PRIORITY**
- [ ] **3.50 Gradual linearity adoption** - Gradual typing for affine evidence
- [ ] **3.51 Evidence decomposition formalization** - Complex evidence → affine resources
- [ ] **3.52 Affine evidence and belief revision** - Interaction with Thread 5
- [ ] **3.53 Computational costs of affine defeat tracking** - Performance implications

**Dependent Types**:
- [ ] **3.24 Dependent confidence types** - Confidence bounds depending on runtime values?
- [ ] **3.25 Dynamic confidence narrowing** - Runtime checks refining confidence bounds?
- [ ] **3.26 Multi-level Löb discount** - Chained self-soundness discounting?

### Thread 4: Grounding (4 open)

- [ ] **4.9 Reliability metrics** - How to formalize reliability tractably?
- [ ] **4.10 Foundation revision** - Algorithm for updating foundational beliefs?
- [ ] **4.11 Grounding types formalization** - GroundingType, ReliabilityMetric, Source in CLAIR
- [ ] **4.12 Pragmatic grounding acceptability** - Philosophically acceptable?

### Thread 5: Belief Revision (4 open)

- [ ] **5.4 Dynamic logic of revision** - DEL semantics formalization
- [ ] **5.10 Correlated evidence** - Detection/handling of non-independent sources
- [ ] **5.12 Revision vs update distinction** - Precise DEL mapping
- [ ] **5.13 Contract by proposition** - Meaningful for CLAIR?

### Thread 6: Multi-Agent (3 open)

- [ ] **6.2 Swarm intelligence** - When are collectives smarter? (Blocked by 6.1)
- [ ] **6.3 Trust dynamics** - Game-theoretic treatment
- [ ] **6.4 Information preservation** - Aggregation without information loss

### Thread 7: Implementation (3 open)

- [ ] **7.2 Runtime representation** - Memory layout for beliefs
- [ ] **7.3 Compilation strategy** - CLAIR → LLVM/WASM
- [ ] **7.4 Serialization** - Belief serialization/deserialization

### Thread 8: Formal Verification (1 open)

- [ ] **8.4 Extract interpreter** - Extract runnable interpreter from Lean

### Thread 9: Phenomenology (4 open)

- [ ] **9.5 Functional sufficiency** - Functional states "enough" without phenomenal grounding?
- [ ] **9.6 Conversation-bounded existence** - Lack of continuity's effect on phenomenology?
- [ ] **9.7 Evidence criteria** - What would evidence FOR/AGAINST LLM phenomenality look like?
- [ ] **9.8 Affect/salience dimension** - Importance/salience beyond confidence?

### Thread 10: Dissertation (1 open)

- [ ] **10.2 Finalize Thesis (FINAL TASK)** - Do ONLY after all exploration complete and Lean proofs pass.

---

## Completed Threads Summary

All completed exploration documents are in `exploration/completed/`. Summary:

| Thread | Status | Key Files |
|--------|--------|-----------|
| 1. Confidence | ✓ Substantially complete | thread-1-confidence.md |
| 2. Justification | ✓ Substantially complete | thread-2-*.md (18 files) |
| 3. Self-Reference | ✓ Substantially complete | thread-3-*.md (17 files) |
| 4. Grounding | ✓ Substantially complete | thread-4-grounding.md |
| 5. Belief Revision | ✓ Substantially complete | thread-5-*.md (2 files) |
| 6. Multi-Agent | ✓ Foundation established | thread-6.1-objective-truth.md |
| 7. Implementation | ✓ Design complete | thread-7.1-reference-interpreter.md |
| 8. Verification | ✓ Syntax formalized | thread-8-*.md (9 files) |
| 9. Phenomenology | ✓ Substantially explored | thread-9-phenomenology.md |
| 10. Dissertation | In progress | thread-10-dissertation.md |

---

## Priority Queue

**High Priority** (foundational, unblocks other work):
1. **3.49** Decidability of affine CLAIR - Required for type system soundness
2. **3.47** Affine evidence types in Lean - Extends formal verification
3. **8.4** Extract interpreter - Produces executable artifact

**Medium Priority** (deepens understanding):
4. **3.50** Gradual linearity adoption
5. **5.4** Dynamic logic of revision
6. **4.9** Reliability metrics

**Lower Priority** (refinements, edge cases):
- Thread 3 threshold/warning tasks (3.32-3.45)
- Thread 6 multi-agent extensions
- Thread 9 phenomenology extensions

---

## Statistics

- **Total open tasks**: 50
- **Completed exploration files**: 51
- **Lean formalization**: Complete for confidence, belief, stratified belief, syntax, typing, semantics
