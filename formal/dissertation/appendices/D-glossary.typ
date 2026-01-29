#import "../layout.typ": *

// Appendix D: Glossary
#heading(level: 1)[Glossary]

This appendix provides concise definitions of key terms, notation, and acronyms used throughout this dissertation. Terms are marked with their primary chapter of introduction.

#heading(level: 2)[D.1 Term Definitions]

#heading(level: 3)[Epistemic Terms]

+---
+**Term** | **Definition** | **Chapter**
+---
+**Belief** | A first-class value in CLAIR consisting of a proposition, confidence, and justification. Beliefs can be constructed, combined, defeated, and inspected through language operations. | 1
+**Confidence** | A value in the unit interval [0,1] representing degree of epistemic commitment. Confidence is #emph[not] probability: rather than quantifying frequency or subjective chance, confidence tracks how justified a belief is given available evidence. | 3
+**Commitment (Epistemic)** | The stance of endorsing a proposition as true to a specified degree. High confidence (close to 1) indicates strong commitment; low confidence (close to 0) indicates weak or no commitment. | 3
+**Justification** | A data structure tracking the derivation history of a belief. Justifications form a directed acyclic graph (DAG) where nodes represent beliefs and edges represent inference rules or evidence sources. | 4
+**Invalidation** | A condition associated with a belief specifying circumstances under which the belief should be reconsidered. Invalidation enables defeasible reasoning—beliefs can be defeated without logical contradiction. | 4
+**Provenance** | The origin or source of evidence for a belief. CLAIR tracks provenance through justification graphs, enabling audit trails for how conclusions were reached. | 4
+**Reliability** | In CLAIR's semantics, the tendency of a source to produce true beliefs. Reliability is the #emph[semantic interpretation] of confidence: a belief with confidence *c* is interpreted as coming from a source with reliability *c*. | 3
+---

#heading(level: 3)[Operations and Relations]

+---
+**Term** | **Definition** | **Chapter**
+---
+**Probabilistic OR (#sym[⊕])** | Aggregation operator for independent evidence: *a ⊕ b = a + b - ab*. This equals the probability that at least one of two independent events occurs. Satisfies commutativity, associativity, and has identity 0. | 3
+**Undercut (#sym[⊸])** | Defeat operation that reduces confidence multiplicatively: *undercut(c, d) = c × (1-d)*. A defeater with confidence *d* reduces target confidence by factor *(1-d)*. | 4
+**Rebuttal** | Defeat operation for conflicting evidence: *rebut(c₁, c₂) = c₁ / (c₁ + c₂)*. Normalizes competing confidences to [0,1]; equal confidences yield 1/2. | 4
+**Derivation** | Combining beliefs via rule application: *derive(b₁, b₂)* pairs the values and multiplies confidences *c₁ × c₂*. Tracks justification through rule application. | 4
+**Aggregation** | Combining independent evidence using #sym[⊕]: *aggregate(b₁, b₂)* produces belief with confidence *c₁ ⊕ c₂*. Tracks justification through aggregation node. | 4
+**Subtyping** | Confidence ordering: belief at confidence *c₁* can be used where belief at *c₂* is required iff *c₁ ≥ c₂*. Enables confidence weakening. | 10
+---

#heading(level: 3)[Structural Properties]

+---
+**Term** | **Definition** | **Chapter**
+---
+**Directed Acyclic Graph (DAG)** | A graph with directed edges and no cycles. CLAIR requires justification graphs to be DAGs to ensure well-foundedness and prevent circular reasoning. | 4
+**Stratification** | Layering beliefs into levels *0, 1, 2, ...* where level *n* can only refer to levels <*n*. Enforces Tarski's hierarchy to prevent self-referential paradoxes. | 6
+**Well-formedness** | Constraints on CLAIR programs: (1) justification graphs must be acyclic, (2) stratification constraints on introspection, (3) confidences in [0,1]. | 10
+---

#heading(level: 3)[Logical and Modal Terms]

+---
+**Term** | **Definition** | **Chapter**
+---
+**CPL (Confidence-Bounded Provability Logic)** | Graded extension of Gödel-Löb provability logic. Adds confidence grades to provability operator #sym[□]. Axiomatizes self-referential reasoning with confidence discounts. | 5
+**Löb's Theorem** | Modal logic theorem: #sym[□](#sym[□]#sym[φ] → #sym[φ]) → #sym[□]#sym[φ]. In provability logic, enables self-reference; in CLAIR, motivates anti-bootstrapping constraint. | 5
+**Graded Modality** | Modal operators with quantitative gradess. CLAIR's #sym[□]#sub[c] means "provable with confidence at least *c*." | 5
+**Anti-bootstrapping** | Principle that self-validating claims cannot increase confidence. Formally: *c* ≤ *g(c)* for some discount function *g*. CLAIR uses *g(c) = c²*. | 5
+**Kripke Semantics** | Possible worlds framework for modal logic. CPL uses graded Kripke models where accessibility relations track confidence thresholds. | 5
+---

#heading(level: 3)[Computational Terms]

+---
+**Term** | **Definition** | **Chapter**
+---
+**Fuel** | Bound on computation steps in the Lean evaluator: *evalFuel n e* evaluates for at most *n* steps. Prevents infinite loops while ensuring termination. | B
+**Call-by-value** | Evaluation strategy: function arguments are evaluated before application. CLAIR uses call-by-value to match intuition about belief formation. | B
+**Small-step semantics** | Reduction relation *e → e'* defining one step of computation. Composed to form multi-step evaluation *e →* *e'*. | 10
+**Bidirectional Type Checking** | Type checking algorithm with synthesis (infer type from expression) and checking (verify expression matches type). Enables practical implementation. | 10
+**De Bruijn Indices** | Variable representation using natural numbers: var 0 = most recent binder, var 1 = next recent, etc. Enables formal proofs about substitution. | A
+---

#heading(level: 3)[Argumentation and Belief Revision]

+---
+**Term** | **Definition** | **Chapter**
+---
+**Defeasible Reasoning** | Reasoning where conclusions can be defeated by new information without logical contradiction. CLAIR supports defeasibility through undercut and rebut operations. | 4
+**Underminer** | An argument that attacks the connection between evidence and conclusion (e.g., "the sensor is miscalibrated"). Reduces confidence via *undercut(c,d) = c×(1-d)*. | 4
+**Rebuttal** | An argument providing conflicting evidence for the opposite conclusion. Normalizes via *rebut(c₁,c₂) = c₁/(c₁+c₂)*. | 4
+**AGM Theory** | Classic belief revision framework (Alchourrón, Gärdenfors, Makinson). CLAIR extends AGM to graded, DAG-structured beliefs. | 7
+**Contraction** | Belief revision operation: remove a belief from a belief set. In CLAIR, achieved by setting confidence to 0. | 7
+**Revision** | Belief revision operation: add a belief while maintaining consistency. In CLAIR, achieved by aggregating with existing beliefs. | 7
+---

#heading(level: 3)[Impossibility Results]

+---
+**Term** | **Definition** | **Chapter**
+---
+**Gödel's Incompleteness** | Any consistent formal system capable of arithmetic contains true but unprovable statements. Motivates CPL's design restrictions. | 12
+**Church's Undecidability** | First-order logic validity is undecidable. CLAIR restricts to decidable fragments (CPL-finite, CPL-0). | 12
+**Tarski's Undefinability** | Truth cannot be defined within the same language. Motivates stratification: level *n* cannot quantify over level *n*. | 12
+**Löb's Paradox** | Curious proposition using Löb's theorem that leads to contradiction if not carefully restricted. Resolved via stratification. | 6
+---

#heading(level: 2)[D.2 Notation Table]

+---
+**Symbol** | **Meaning** | **Type** | **Chapter**
+---
+*c* | Confidence value in [0,1] | Confidence | 3
+#sym[⊕] | Probabilistic OR: *a ⊕ b = a + b - ab* | Binary operation | 3
+#sym[⊸] | Undercut: *c ⊸ d = c × (1-d)* | Binary operation | 4
+#sym[×] | Multiplication (conjunctive combination) | Binary operation | 3
+*g(c)* | Löb discount function; CLAIR uses *c²* | Unary function | 5
+#sym[□]#sub[c] #sym[φ] | Necessarily #sym[φ] with confidence at least *c* | Modal operator | 5
+#sym[◇]#sub[c] #sym[φ] | Possibly #sym[φ] with confidence at least *c* | Modal operator | 5
+#sym[⊢] | Typing judgment: #sym[Γ] #sym[⊢] *e* : *A* @ *c* | Relation | 10
+#sym[→] | Small-step reduction: *e → e'* | Relation | 10
+#sym[→*] | Multi-step reduction (reflexive transitive closure) | Relation | 10
+#sym[Γ] | Typing context (list of variable: type pairs) | Context | 10
+*A* ⇒ *B* | Function type from *A* to *B* | Type | 10
+Belief<*A*> | Belief type holding value of type *A* | Type constructor | 10
+*b*.value | Extract value from belief *b* | Projection | 4
+*b*.confidence | Extract confidence from belief *b* | Projection | 4
+*b*.justification | Extract justification from belief *b* | Projection | 4
+*m* <*n* | Stratification constraint: level *m* below *n* | Ordering | 6
+#sym[∀] | Universal quantifier | Quantifier | Appendix A
+#sym[∃] | Existential quantifier | Quantifier | Appendix A
+#sym[∈] | Set membership | Relation | Appendix A
+#sym[⊆] | Subset relation | Relation | Appendix A
+#sym[∪] | Set union | Binary operation | Appendix A
+#sym[∩] | Set intersection | Binary operation | Appendix A
+#sym[λ]*x*:*A*. *e* | Lambda abstraction (anonymous function) | Expression | 10
+*e*1 *e*2 | Function application | Expression | 10
+---

#heading(level: 2)[D.3 Acronyms]

+---
+**Acronym** | **Full Name** | **Definition**
+---
+**CLAIR** | Comprehensible LLM AI Intermediate Representation | The formal system presented in this dissertation
+**CPL** | Confidence-Bounded Provability Logic | Graded modal logic extending Gödel-Löb
+**CPL-finite** | CPL with finite confidence set {0, 1/n, 2/n, ..., 1} | Decidable fragment suitable for implementation
+**CPL-0** | CPL with only confidence 0 (ungraded provability) | Collapses to standard provability logic GL
+**AGM** | Alchourrón-Gärdenfors-Makinson | Classic belief revision theory
+**DAG** | Directed Acyclic Graph | Graph structure for justifications
+**LLM** | Large Language Model | AI systems CLAIR is designed to augment
+**IR** | Intermediate Representation | Compiler representation between source and machine code
+**AI** | Artificial Intelligence | Field of study
+---

#heading(level: 2)[D.4 Type System Summary]

#heading(level: 3)[Base Types]

+---
+**Type** | **Description** | **Example Values**
+---
+Nat | Natural numbers (non-negative integers) | 0, 1, 2, 42, 128
+Bool | Boolean values | true, false
+String | Text strings | "hello", "sensor-reading"
+Unit | Unit type (single value) | unit
+Pair(*A*, *B*) | Ordered pair | (1, true), ("x", 42)
+Sum(*A*, *B*) | Tagged union (either *A* or *B*) | inl(5), inr(true)
+*A* ⇒ *B* | Function type from *A* to *B* | λx:Nat. x + 1
+Belief<*A*> | Belief holding value of type *A* | belief(42, 0.9, j)
+---

#heading(level: 3)[Confidence Operations]

+---
+**Operation** | **Notation** | **Formula** | **Identity**
+---
+Probabilistic OR | *a ⊕ b* | *a + b - a×b* | 0
+Multiplication | *a × b* | *a × b* | 1
+Undercut | *undercut(c, d)* | *c × (1-d)* | N/A (d=0 gives c)
+Rebuttal | *rebut(c₁, c₂)* | *c₁ / (c₁ + c₂)* | N/A
+Minimum | *min(a, b)* | *min(a, b)* | 0 (if bounded below)
+Maximum | *max(a, b)* | *max(a, b)* | 1 (if bounded above)
+---

#v(1em)
