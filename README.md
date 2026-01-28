# CLAIR: Comprehensible LLM AI Intermediate Representation

> A programming language and intermediate representation designed for AI-native computation, where reasoning, confidence, and justification are first-class concepts.

## Motivation

Current programming languages and IRs are designed for a world where:
- Humans write every line of code
- Compilers transform code deterministically
- Intent exists only in comments (discarded at compile time)
- Reasoning behind decisions is lost

In an AI-native world:
- LLMs generate code through probabilistic reasoning
- Multiple valid approaches exist; one is *chosen* with rationale
- Confidence varies across different parts of the code
- Assumptions are made that may later be invalidated
- Other AI systems need to understand, verify, and revise the code

CLAIR preserves what traditional systems discard: **the epistemic state of the code's author**.

## Core Concepts

### Beliefs, Not Just Values

Traditional type systems classify *values*:
```
x : Int
```

CLAIR classifies *beliefs about values*:
```
x : Int @ 0.95 from database.users.age
        by (query validated)
        invalidated_by (schema change)
```

A **Belief** is a value plus:
- **Confidence**: How certain are we? (∈ [0,1])
- **Provenance**: Where did this come from?
- **Justification**: Why do we believe it?
- **Invalidation conditions**: When should we reconsider?

### Derivations, Not Just Computation

Traditional computation is deterministic reduction:
```
(λx. x + 1) 5  →  6
```

CLAIR computation is *belief derivation*:
```
From: belief(rate_limit_needed, 0.9, security_review)
      belief(redis_available, 0.85, infrastructure_check)
Derive: belief(use_redis_rate_limiter, 0.76, derived)
        by: (satisfied_requirements ∧ infrastructure_supports)
```

Confidence propagates. Justifications compose. Invalidation conditions accumulate.

### Decisions, Not Just Expressions

When multiple valid paths exist, traditional languages just pick one. The choice disappears.

CLAIR preserves **decisions**:
```
decision auth_method:
  options: [jwt_hs256, jwt_rs256, session_based]
  constraints: [stateless, single_service]
  selected: jwt_hs256
  rationale: "simplest approach satisfying constraints"
  rejected:
    - session_based: violates stateless
    - jwt_rs256: unnecessary complexity for single service
  revisit_if: multi_service_deployment
```

This is queryable, auditable, and automatically flagged for review when conditions change.

### Intent, Not Just Behavior

Traditional code specifies *what* happens. CLAIR also specifies *why*:
```
function verify_token(token: Bytes) -> Result<Claims, Error>
  intent: "Validate JWT and extract claims, rejecting expired or tampered tokens"
  realizes: secure_authentication
```

Intent is preserved through compilation and can be verified against implementation.

## Document Structure

- `formal/` - Formal specifications and type theory
  - `belief-types.tex` - Core type system formalization (LaTeX)
  - `derivation-calculus.md` - Rules for belief derivation
  - `decision-semantics.md` - Semantics of decisions
  - `syntax.md` - Language syntax reference
  - `foundations-and-limits.md` - Theoretical limits (Gödel, Turing, Church, Gentzen)
  - `logical-foundations.md` - Connections to BHK, Curry-Howard, linear logic, epistemic logic
  - `categorical-structure.md` - Graded monad structure, algebraic foundations
  - `turing-completeness.md` - Proof of computational universality
  - `verification-of-intent.md` - Bridging tracking and proving
  - `multi-agent-beliefs.md` - Multiple agents, trust, consensus
  - `swarm-coordination.md` - Swarms, disagreement resolution, BFT

- `notes/` - Background research and related work
  - `prior-art.md` - Related academic work
  - `design-rationale.md` - Why CLAIR is designed this way

- `examples/` - Example CLAIR programs
  - `hello-world.clair` - Minimal example
  - `auth.clair` - JWT authentication example

## Key Insight: Tracking, Not Proving

CLAIR is a **tracking system**, not a **proof system**.

- **Proof systems** establish truth: "This is correct."
- **Tracking systems** establish epistemic state: "This is what we believe, why we believe it, and when we should reconsider."

This distinction is not a weakness—it's a principled response to fundamental limits discovered by Gödel, Turing, and Church:

- We cannot prove our own soundness (Gödel)
- We cannot decide all properties (Turing, Church)
- We cannot justify axioms internally (foundational)

CLAIR accepts these limits. It doesn't prove; it makes uncertainty explicit. See `formal/foundations-and-limits.md` for the full treatment.

## Status

This is a theoretical exploration, not a working implementation. The goal is to formalize what an AI-native programming language could look like.

## Origins

Developed through conversation exploring: "What would an AI-native intermediate representation look like that preserves reasoning and intent?"

Key insight: The fundamental unit of AI computation isn't the value—it's the **belief**. A belief is a value plus epistemic metadata. Traditional type systems verify data; CLAIR verifies *justified knowledge*.
