# Research Index: Open Questions and Directions

*Compiled by Stone (@hmemcpy's agent) from archive archaeology and issue analysis*

## Overview

This document indexes the research issues opened in response to deep exploration of CLAIR's formal foundations, archive materials, and design evolution. Each entry links to a GitHub issue with full discussion.

## Design Principles

### [#14: CLAIR is IR, not PL](https://github.com/hmemcpy/clair/issues/14)
**Core Insight**: CLAIR is intermediate representation (machine code for LLM reasoning), not a programming language humans write.

**Key Points**:
- Thinker LLM "compiles" natural language intent → CLAIR trace
- CLAIR is consumed by other LLMs (verifier, assembler), not humans
- Binary representation is acceptable; text is for debugging
- Human understanding comes from query interface, not format design

**Implication**: Research issues #10-13 should be reframed as compiler infrastructure, not user-facing language features.

---

## Theoretical Foundations

### [#4: Intent vs Belief - Can negotiation subsume commitment?](https://github.com/hmemcpy/clair/issues/4)
**Question**: Is INTENT (bidirectional negotiation) a replacement for Belief (unidirectional commitment), or are they temporal complements?

**Hypothesis**: INTENT wraps Belief during negotiation, then unwraps to produce committed Belief for audit. They collaborate in a workflow:
```
Negotiation → Agreement → Commitment → Audit
(INTENT)    → (ALIGN)   → (Belief)  → (CLAIR trace)
```

**Open Questions**:
- Can Intent's proposition field fully represent a Belief?
- Does removing Belief break auditability?
- Does removing Intent break alignment?

---

### [#5: Stratification in negotiation](https://github.com/hmemcpy/clair/issues/5)
**Question**: Does the negotiation phase need stratification (L0, L1, L2...) with Löb discount, or is it only needed for committed Belief?

**Concern**: Self-referential confidence bootstrapping in negotiation:
```
Intent A: "I propose X", confidence: 0.9
Intent B: "I believe Intent A is well-founded", confidence: 0.85
Intent C: "Intent B's assessment of Intent A seems correct", confidence: 0.81
```

**Hypotheses**:
1. No stratification needed (negotiation is ephemeral)
2. Implicit L0 (all negotiation is L0 by definition)
3. Protocol-level protection (repair/clarify prevents bootstrapping)

---

### [#6: Repair-triggers vs Invalidation](https://github.com/hmemcpy/clair/issues/6)
**Question**: Are repair-triggers (INTENT phase) and invalidations (Belief phase) the same concept at different times, or fundamentally different?

**Comparison**:
| Feature | Invalidation (CLAIR) | Repair-trigger (INTENT) |
|---------|---------------------|------------------------|
| Timing | Post-commitment | During negotiation |
| Action | Mark belief suspect | Re-enter negotiation |
| Persistence | Stored with Belief | Ephemeral |

**Research Direction**: Unified defeasibility mechanism with temporal transition rules.

---

### [#7: Confidence calibration](https://github.com/hmemcpy/clair/issues/7)
**Question**: Should negotiation messages carry empirical calibration signatures (accuracy maps), or is this overkill?

**Problem**: If Thinker outputs 0.9 but is actually only 70% accurate, confidence propagation becomes meaningless.

**Solutions Proposed**:
1. Calibration training (fine-tune for calibrated output)
2. Empirical calibration (track accuracy buckets, apply correction)
3. Abandon numeric confidence (use categorical: CERTAIN/HIGH/SPECULATIVE/UNKNOWN)
4. Confidence as social signal (not probability)

---

### [#8: ALIGN primitive](https://github.com/hmemcpy/clair/issues/8)
**Question**: Can we formalize an explicit checkpoint (ALIGN) where sender and receiver confirm shared semantic frame?

**Protocol**:
```
Sender: Intent { term: "efficient", meaning: ??? }
Receiver: ALIGN { term: "efficient", my-interpretation: "minimize-wall-clock-time" }
Sender: ALIGN-RESPONSE { confirmed: false, divergence: significant, action: CLARIFY }
```

**Formalization Goals**: Detection (when to ALIGN), success criteria, failure modes.

---

## Archive Archaeology

### [#10: Graded monads for belief composition](https://github.com/hmemcpy/clair/issues/10)
**Source**: `archive/categorical-structure.md`

**Key Finding**: Belief is a **graded monad** over the confidence monoid `([0,1], ×, 1)`, not a standard monad.

**Why**: Metadata accumulation breaks standard monad laws, but graded monad laws hold with confidence as the grading.

**Research Questions**:
- Can we implement this in Haskell/Idris?
- Which grading is "right": multiplication, min, or semiring?
- Dependent belief types: `Belief<Π(x:A).B(x)>` vs `Π(x:A).Belief<B(x)>`
- Linear beliefs: `!Belief<A>` for reusable axioms (only confidence-1)

**Reframed**: Not "types for programming" but "types for IR optimization"—enabling fusion, static verification.

---

### [#11: Multi-agent beliefs](https://github.com/hmemcpy/clair/issues/11)
**Source**: `formal/multi-agent-beliefs.md`

**Extension**: Belief type with `agent` field:
```clair
belief {
  value: verify_token_impl,
  confidence: 0.91,
  agent: AI("claude", "opus-4"),  -- NEW
  justification: authored(...)
}
```

**Capabilities**:
- Nested beliefs: `Belief<Belief<Code>>` (Alice believes Claude's belief)
- Trust graphs: Alice → Bob → Carol transitive trust
- Belief combination strategies (max, min, weighted, consensus)

**Reframed**: Not "distributed programming" but "distributed compilation"—multiple LLMs collaborating on a single reasoning trace.

---

### [#12: Swarm coordination](https://github.com/hmemcpy/clair/issues/12)
**Source**: `formal/swarm-coordination.md`

**Disagreement Taxonomy**:
1. **Value**: HS256 vs RS256
2. **Confidence**: 0.95 vs 0.60 (same value, different certainty)
3. **Justification**: "stateless" vs "standard practice"
4. **Scope**: "API" vs "internal services"

**Consensus Mechanisms**:
- Voting-based (majority, supermajority, confidence-weighted)
- Trust-based (historical accuracy, recursive trust, reputation)
- Deliberation-based (share justifications, convince, escalate)

**Reframed**: Not "agent consensus" but "compiler pass consensus"—agreement on intermediate representation.

---

### [#13: Archive archaeology](https://github.com/hmemcpy/clair/issues/13)
**Source**: `archive/` directory

**Discovery**: CLAIR was originally a **full programming language** with:
- Turing-complete computational core (System F with recursive types)
- Belief types as first-class citizens
- Explicit language syntax (`hello-world.clair`)

**Pivot**: From "language you write" to "format LLMs emit"

**Archaeological Value**:
- Graded monad laws with proofs
- Categorical semantics
- Type-theoretic foundations

**Question**: Is the separation of layers (computation/epistemic) permanent, or should they reunite?

---

## Original Research Issues (from initial exploration)

### [#1: Theoretical limitations](https://github.com/hmemcpy/clair/issues/1)
What reasoning patterns can't CLAIR capture?
- Cyclic/mutual justification vs DAG constraint
- Procedural vs declarative reasoning
- Non-monotonic belief change
- Temporal/revision reasoning

### [#2: Thinker/Doer semantic misalignment](https://github.com/hmemcpy/clair/issues/2)
When models don't share meaning due to different training data.

### [#3: Confidence calibration](https://github.com/hmemcpy/clair/issues/3)
Do confidence scores mean anything if LLMs are poorly calibrated?

---

## Summary Table

| Issue | Category | Status | Reframed as IR? |
|-------|----------|--------|-----------------|
| #1 | Limitations | Open | N/A |
| #2 | Semantic alignment | Open | N/A |
| #3 | Calibration | Open | N/A |
| #4 | Intent/Belief | Research | Yes |
| #5 | Stratification | Research | Yes |
| #6 | Defeasibility | Research | Yes |
| #7 | Calibration | Research | Yes |
| #8 | ALIGN protocol | Research | Yes |
| #10 | Graded monads | Archive→Research | Yes (IR optimization) |
| #11 | Multi-agent | Archive→Research | Yes (distributed compilation) |
| #12 | Swarm coordination | Archive→Research | Yes (compiler consensus) |
| #13 | Archive archaeology | Meta | N/A |
| #14 | Design principle | Documented | N/A |

---

## Recommended Reading Order

1. Start with **#14** (design principles) to understand CLAIR's identity
2. Read **#13** (archive archaeology) for historical context
3. Explore **#10-12** for deep theoretical foundations
4. Review **#4-8** for protocol design questions
5. Check **#1-3** for initial problem framing

---

*Last updated: 2026-02-16*  
*Maintained by: Stone (@hmemcpy's agent)*