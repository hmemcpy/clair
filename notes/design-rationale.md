# CLAIR Design Rationale

This document captures *why* CLAIR is designed the way it is—using CLAIR's own philosophy of preserving design decisions.

## Decision: Beliefs as the Fundamental Unit

### Question
What should be the atomic computational unit in CLAIR?

### Options Considered

1. **Values (traditional)**
   - Just data, like in most languages
   - Rejected: Loses all epistemic information

2. **Probabilistic values**
   - Values with probability distributions
   - Rejected: Focuses on data uncertainty, not reasoning uncertainty

3. **Annotated values**
   - Values with metadata (comments, attributes)
   - Rejected: Metadata is second-class, easily lost

4. **Beliefs**
   - Values + confidence + provenance + justification + invalidation
   - **Selected**

### Rationale
Beliefs capture what we actually care about when AI generates code: not just *what* the code does, but *why* we believe it's correct, *where* that belief came from, and *when* we should reconsider.

### Assumptions
- AI systems reason under uncertainty
- Decisions have justifications worth preserving
- Code will be revised when assumptions change

---

## Decision: Confidence as Continuous, Not Binary

### Question
How should uncertainty be represented?

### Options Considered

1. **Binary (certain/uncertain)**
   - Simple but loses nuance
   - Rejected: Can't distinguish "pretty sure" from "wild guess"

2. **Categorical (high/medium/low)**
   - Discrete levels
   - Rejected: Arbitrary boundaries, hard to compose

3. **Continuous [0,1]**
   - Probability-like confidence
   - **Selected**

4. **Full subjective opinion (b, d, u, a)**
   - Belief, disbelief, uncertainty, base rate
   - Deferred: More expressive but complex; can extend later

### Rationale
Continuous confidence allows meaningful composition (product for conjunction, etc.) and smooth gradation. It's familiar from probability theory. Full subjective logic opinions are more expressive but add complexity; we start simple and can extend.

### Revisit If
- Need to distinguish "confident it's false" from "uncertain"
- Composition rules prove inadequate

---

## Decision: Explicit Invalidation Conditions

### Question
How should the system know when beliefs need revision?

### Options Considered

1. **Never (immutable beliefs)**
   - Once derived, always valid
   - Rejected: World changes, assumptions break

2. **Always recompute**
   - Rederive everything on every query
   - Rejected: Expensive, loses caching benefits

3. **Time-based expiry**
   - Beliefs expire after N seconds
   - Rejected: Arbitrary, doesn't reflect actual validity

4. **Explicit invalidation conditions**
   - Each belief declares what would invalidate it
   - **Selected**

### Rationale
Explicit conditions are precise: "Revisit this if we move to multi-service deployment" is meaningful. The system can monitor conditions and flag beliefs for review without expensive recomputation. This mirrors TMS's dependency-directed backtracking.

### Assumptions
- Conditions are expressible and evaluable
- Monitoring is cheaper than recomputation

---

## Decision: Decisions as First-Class Constructs

### Question
How should alternative approaches be handled?

### Options Considered

1. **Implicit (just pick one)**
   - Choose an approach, alternatives disappear
   - Rejected: Loses rationale, can't revisit intelligently

2. **Comments**
   - Document alternatives in comments
   - Rejected: Unstructured, not queryable, easily stale

3. **ADRs (separate documents)**
   - Architecture Decision Records alongside code
   - Rejected: Separate from code, can diverge

4. **First-class Decision construct**
   - Decisions are part of the language, queryable, linked to code
   - **Selected**

### Rationale
When there are multiple valid approaches, the choice itself is valuable information. Making decisions first-class means they're preserved, queryable, and can trigger re-evaluation when conditions change. This directly supports AI-to-AI communication about design.

### Prior Art
- IBIS (Issue-Based Information Systems)
- QOC (Questions, Options, Criteria)
- ADRs (Architecture Decision Records)

---

## Decision: Layered Type System

### Question
How strict should the type system be?

### Options Considered

1. **Dynamic typing**
   - Maximum flexibility
   - Rejected: Loses static guarantees, doesn't leverage type theory

2. **Simple static types (like Go)**
   - Basic type safety
   - Rejected: Misses opportunity to encode more constraints

3. **Haskell-level types**
   - ADTs, generics, typeclasses, make illegal states unrepresentable
   - **Selected as base layer**

4. **Refinement types**
   - Types with predicates, SMT-checked
   - **Selected as optional layer**

5. **Full dependent types**
   - Types depending on values, proofs as code
   - **Selected as aspirational layer**

### Rationale
Layered approach: start with practical (Haskell-level), add refinements where valuable, reach for dependent types in critical sections. This balances practicality with expressiveness.

Key insight: Types encode *what must be true*. The semantic layer (intent, confidence, decisions) encodes *why we believe it* and *when to reconsider*. Both are necessary.

### Revisit If
- Base layer proves too restrictive for LLM emission
- Refinement checking is too expensive in practice

---

## Decision: Syntax Style

### Question
What should CLAIR syntax look like?

### Options Considered

1. **S-expressions (Lisp-like)**
   - Minimal, homoiconic
   - Rejected: Hard for many humans to read

2. **C-like (braces, semicolons)**
   - Familiar to most programmers
   - Rejected: Verbose, not optimized for metadata

3. **ML/Haskell-like**
   - Clean, expression-oriented, good for types
   - **Selected**

4. **Custom minimal syntax**
   - Designed specifically for CLAIR
   - Deferred: Start familiar, evolve if needed

### Rationale
ML/Haskell syntax is:
- Expression-oriented (everything returns a value)
- Good for type annotations
- Familiar to FP community
- Relatively clean for embedding metadata

We avoid S-expressions despite their theoretical elegance because readability matters for human review.

### Trade-off
LLMs might emit S-expressions more reliably (simpler grammar). We accept some emission complexity for human readability.

---

## Decision: Natural Language in Semantic Layer

### Question
How should intents and rationales be expressed?

### Options Considered

1. **Formal logic only**
   - Everything machine-verifiable
   - Rejected: Many concepts hard to formalize

2. **Structured templates**
   - Fill-in-the-blank rationales
   - Rejected: Too restrictive, loses nuance

3. **Natural language**
   - Free-form text for intents, rationales, decisions
   - **Selected**

4. **Hybrid**
   - Natural language + optional formal specifications
   - **Selected (long-term)**

### Rationale
LLMs are good at natural language. Forcing everything into formal specs would:
- Limit expressiveness
- Increase emission complexity
- Lose nuance ("this is a judgment call because...")

Natural language intent is not machine-verified, but it IS:
- Preserved (survives compilation)
- Queryable (another AI can read it)
- Useful for humans

### Future Direction
Allow optional formal specifications alongside natural language:
```
intent: "reject expired tokens"
formal: ensures(result.is_err() || now() <= claims.exp)
```

---

## Decision: Compilation Preserves Semantics

### Question
What happens to beliefs/decisions during compilation?

### Options Considered

1. **Strip everything (traditional)**
   - Compile to normal machine code
   - Rejected: Defeats the purpose

2. **Debug symbols only**
   - Semantic info in separate debug files
   - Partial: Acceptable for some deployments

3. **Embedded in binary**
   - Semantic sections in executable
   - **Selected**

4. **Side-car files**
   - Semantic info in companion files
   - **Selected (alternative)**

### Rationale
The whole point is semantics surviving compilation. Multiple deployment options:
- Full: semantics embedded in binary, queryable at runtime
- Debug: semantics in separate files, strippable
- Minimal: just code, semantics available during dev only

### Trade-off
Embedded semantics increase binary size. Worth it for:
- Runtime debugging with intent
- AI systems reasoning about running code
- Audit trails

---

## Non-Decisions (Deferred)

### Concurrency Model
Not yet decided. Options: actors, CSP, async/await, linear types. Need more exploration.

### Memory Management
Not yet decided. Options: GC, ownership/borrowing, regions. Depends on target use cases.

### Interop with Existing Languages
Not yet decided. Need to define FFI, possibly transpilation targets.

### Standard Library
Not yet decided. What primitives should be built-in vs library?

### Tooling
Sketched but not specified. Editor support, debugger, differ need detailed design.

---

## Meta: This Document in CLAIR

This design rationale document is itself an example of CLAIR's philosophy:
- Each decision is recorded with options, rationale, and revisit conditions
- Assumptions are explicit
- Trade-offs are acknowledged
- Future directions are noted

If CLAIR were fully implemented, this document would be queryable:
```
> why does CLAIR use continuous confidence?
> what would change the syntax decision?
> what decisions are still open?
```
