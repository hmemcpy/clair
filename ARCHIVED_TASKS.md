# CLAIR Archived Tasks

> These tasks are valuable research directions but are either tangential to the core CLAIR formalization, premature without implementation, or have diminishing returns. They are preserved here for future exploration.

---

## Thread 1: Confidence (Deferred)

- [ ] **1.3 Confidence calibration** - EMPIRICAL: Cannot resolve internally. Requires external study of Igal Tabachnik outputs.
- [ ] **1.6 Subjective Logic extension** - Should we use (b,d,u,a) tuples instead of single confidence value?
- [ ] **1.7 Non-independent derivations** - Multiplication rule fails when premises correlated. Design alternatives.

**Reason**: 1.3 requires external empirical work. 1.6-1.7 are alternative designs; current approach works.

---

## Thread 3: Self-Reference (Edge Cases & Variations)

### Threshold Variations (Diminishing Returns)
- [ ] **3.35 Discrete Löb rounding** - Ceiling vs floor for discrete Löb discount?
- [ ] **3.36 Heterogeneous multi-level discount** - Mixed Löb functions at different levels?
- [ ] **3.37 Total epistemic cost metric** - Metric for all introspection levels?
- [ ] **3.38 Maximum introspection depth** - Impose depth limit?
- [ ] **3.39 Multi-level threshold with aggregation** - c = a ⊕ b ⊕ c^(2^k) behavior?
- [ ] **3.41 Heterogeneous aggregation thresholds** - c² ⊕ c⁴ ⊕ c⁸ effective threshold?

**Reason**: Core threshold theory (a=0.5 for single level, a_k = 1-1/2^k for k levels) is established. These are mathematical variations that don't change the design.

### Speculative Extensions
- [ ] **3.28 Automatic contractivity detection** - Syntactic patterns for |f'| < 1?
- [ ] **3.29 Gradual self-reference typing** - Allow unchecked self-reference with incremental verification?
- [ ] **3.31 Probabilistic fixed-point approximation** - Random sampling for undecidable cases?

**Reason**: Nice-to-have optimizations. Core approach (stratification + decidable fragments) works.

### Security Framing
- [ ] **3.42 Bootstrap vulnerability analysis** - Malicious exploitation?
- [ ] **3.43 Defense by redundancy** - Aggregated introspection + defeat interaction?

**Reason**: Bootstrap vulnerability already mitigated via correlation enforcement (δ=1). These are security framings of a formalization project.

### Warnings & Tooling
- [ ] **3.32 External evidence warnings** - Syntactic warnings for ungrounded self-reference?
- [ ] **3.44 `@independent` enforcement level** - Error vs warning?
- [ ] **3.45 Correlation inference for non-introspective sources** - General δ inference?

**Reason**: Implementation details for tooling. Not core theory.

### Dependent Types (Advanced)
- [ ] **3.24 Dependent confidence types** - Confidence bounds depending on runtime values?
- [ ] **3.25 Dynamic confidence narrowing** - Runtime checks refining confidence bounds?
- [ ] **3.26 Multi-level Löb discount** - Chained self-soundness discounting?

**Reason**: Requires dependent type features beyond current scope.

---

## Thread 4: Grounding (Philosophical)

- [ ] **4.10 Foundation revision** - Algorithm for updating foundational beliefs?
- [ ] **4.12 Pragmatic grounding acceptability** - Is pragmatic grounding philosophically acceptable?

**Reason**: Philosophical questions that won't change the design. Pragmatic grounding is the approach regardless of philosophical consensus.

---

## Thread 5: Belief Revision (DEL Extensions)

- [ ] **5.4 Dynamic logic of revision** - DEL semantics formalization
- [ ] **5.12 Revision vs update distinction** - Precise DEL mapping
- [ ] **5.13 Contract by proposition** - Meaningful for CLAIR?

**Reason**: Academic connections to Dynamic Epistemic Logic. Core revision algorithm (justification-based) is established.

---

## Thread 6: Multi-Agent (Beyond Core Scope)

- [ ] **6.2 Swarm intelligence** - When are collectives smarter? Formalize conditions.
- [ ] **6.3 Trust dynamics** - Game-theoretic treatment.
- [ ] **6.4 Information preservation** - Aggregation without information loss.

**Reason**: Each is a substantial research project. Beyond core single-agent CLAIR formalization.

---

## Thread 7: Implementation (Premature)

- [ ] **7.2 Runtime representation** - Memory layout for beliefs.
- [ ] **7.3 Compilation strategy** - CLAIR → LLVM/WASM.
- [ ] **7.4 Serialization** - Belief serialization/deserialization.

**Reason**: Need working interpreter (Task 8.4) first. Premature optimization.

---

## Thread 9: Phenomenology (Unresolvable)

- [ ] **9.5 Functional sufficiency** - Functional states "enough" without phenomenal grounding?
- [ ] **9.6 Conversation-bounded existence** - Lack of continuity's effect on phenomenology?
- [ ] **9.7 Evidence criteria** - What would evidence FOR/AGAINST LLM phenomenality look like?
- [ ] **9.8 Affect/salience dimension** - Importance/salience beyond confidence?

**Reason**: Cannot be resolved from inside (acknowledged in Session 15). Intellectually interesting but unactionable for CLAIR design.

---

## Thread 2: Justification (Theoretical)

- [ ] **2.3 Partial justification** - Can justification be graduated? Semantic question.

**Reason**: Interesting theoretical question, but current binary justification (present/absent) works for formalization.

---

## Thread 3: Self-Reference (Refinements)

- [ ] **3.14 Unbounded quantification** - "Beliefs about all my beliefs"?
- [ ] **3.50 Gradual linearity adoption** - Gradual typing for incremental adoption
- [ ] **3.51 Evidence decomposition** - Complex evidence → affine resources
- [ ] **3.52 Affine evidence and belief revision** - Interaction with Thread 5
- [ ] **3.53 Computational costs** - Performance implications of affine tracking

**Reason**: Refinements beyond core formalization. Affine types designed (3.46-3.49); these are extensions.

---

## Thread 4: Grounding (Formalization Details)

- [ ] **4.9 Reliability metrics** - How to formalize reliability tractably?
- [ ] **4.11 Grounding types formalization** - GroundingType, ReliabilityMetric, Source in CLAIR

**Reason**: Grounding theory established (pragmatic dogmatism). Type formalization is detail work after core interpreter.

---

## Thread 5: Belief Revision (Extensions)

- [ ] **5.10 Correlated evidence** - Detection/handling of non-independent sources

**Reason**: Nice refinement. Core revision algorithm works; correlation is enhancement.

---

## Thread 10: Dissertation

- [ ] **10.2 Finalize Thesis** - Only after implementation proves viability

**Reason**: Write-up comes after proving CLAIR works via interpreter.

---

## Summary

**Archived**: 37 tasks
**Reason categories**:
- Diminishing returns (threshold variations): 6 tasks
- Speculative/nice-to-have: 3 tasks
- Security framing: 2 tasks
- Tooling details: 3 tasks
- Advanced (dependent types): 3 tasks
- Philosophical: 2 tasks
- DEL academic: 3 tasks
- Beyond scope (multi-agent): 3 tasks
- Premature (implementation): 3 tasks
- Unresolvable (phenomenology): 4 tasks

These may be revisited after core CLAIR formalization and implementation are complete.
