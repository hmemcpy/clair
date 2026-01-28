# Thread 3.48: Epistemic Linearity and Defeat Interaction

> **Status**: Active exploration (Session 73)
> **Task**: 3.48 How does affine evidence interact with defeat? Can undercut evidence be reused elsewhere?
> **Question**: When evidence is used in one derivation and that derivation is undercut, what happens to the evidence's linear status?
> **Prior Work**: Thread 3.46 (epistemic linearity), Thread 2.10 (defeat confidence), Thread 2.12 (reinstatement)

---

## 1. The Problem

### 1.1 Motivation

Thread 3.46 established that evidence should be treated as an **affine resource**—usable at most once to prevent double-counting. Thread 2.10 established that defeat (undercut/rebut) modifies confidence through specific operations:
- **Undercut**: `c' = c × (1 - d)` — multiplicative discounting
- **Rebut**: `c' = c_for / (c_for + c_against)` — probabilistic comparison

The question now is: **How do these two mechanisms interact?**

### 1.2 The Core Tension

Consider evidence `e` with confidence `c` that supports conclusion `P`:

```
e ——support——> P
```

If we use affine typing, `e` is "consumed" by this derivation. But now suppose an undercut defeats this inference:

```
e ——support——> P
                ↑
d ——undercut——+
```

The undercut weakens the support, giving `P` reduced confidence `c × (1 - d)`. But `e` itself is unchanged—the undercut attacks the *inference*, not the evidence.

**Key questions emerge:**

1. **Is e still "consumed"?** The evidence was used, but its contribution was diminished.

2. **Can e be reused elsewhere?** If the derivation e→P was fully undercut (d=1), can e support a different conclusion Q?

3. **What about partial undercut?** If d=0.5, e provides "half its information" to P. Can it also provide information elsewhere?

4. **What happens with rebut?** Rebut attacks the conclusion, not the evidence. Does this release the evidence?

5. **What about defeat chains?** If the defeater is itself defeated (reinstatement), does the original evidence's affine status change?

---

## 2. Analysis Framework

### 2.1 Evidence States Under Defeat

I propose distinguishing evidence states based on defeat:

```
Evidence States:
  - Fresh: Not yet used
  - Committed: Used in a derivation (affine tracking)
  - Weakened: Committed but derivation was undercut
  - Released: Derivation fully defeated (d=1), evidence available again?
```

The critical question: Is "Released" a valid state, or does commitment to a derivation permanently consume the evidence regardless of defeat?

### 2.2 Two Interpretations

**Interpretation A: Evidence is permanently consumed**

Once `e` supports `P`, it is consumed regardless of what happens to the derivation. Even if the e→P inference is fully undercut:
- `e` cannot be used elsewhere
- The "information content" of `e` was committed to a specific purpose
- Linear typing tracks *intent*, not *effectiveness*

This interpretation is **simpler** and aligns with standard linear type systems where consumption is about resource allocation, not outcome.

**Interpretation B: Defeat can release evidence**

If the e→P derivation is defeated, `e` should be available for other uses:
- Full undercut (d=1) releases `e` completely
- Partial undercut releases proportional information
- This tracks *effective information transfer*, not just allocation

This interpretation is **informationally justified** but **complex** to implement and reason about.

### 2.3 Which Interpretation Fits CLAIR?

Let me examine both through several lenses:

**Lens 1: Information Theory**

From Shannon's perspective, if `e` supports `P` with confidence `c`, and this support is undercut by `d`, then the *mutual information* between `e` and `P` is reduced:

```
I(e; P) = c × (1 - d) × H(P | ¬e)  [rough approximation]
```

But the information in `e` itself hasn't changed. If the channel (inference) is degraded, the source (evidence) retains its information content.

This suggests **Interpretation B** is informationally correct—evidence's information content is independent of how it's used.

**Lens 2: Type-Theoretic Consistency**

In linear type systems, consumption is about *tracking usage*, not about what happens to the output. Consider:

```haskell
-- Linear function: consumes x
f :: a ⊸ b
f x = ... -- uses x exactly once

-- Even if f's output is discarded, x is still consumed
let _ = f x  -- x is gone
```

The result being discarded doesn't "un-consume" the argument. Similarly, a derivation being undercut shouldn't un-consume the evidence.

This suggests **Interpretation A** is type-theoretically cleaner.

**Lens 3: Epistemic Practice**

In actual reasoning:
- If I use testimony T to conclude P, and someone undercuts T's reliability, I don't necessarily reuse T for a different conclusion
- The "investment" in using T for P already happened
- BUT: if T was fully discredited before I drew any conclusion, I might reconsider

This suggests a **time-sensitive** model: evidence committed to an ongoing derivation is consumed; evidence whose derivation was retroactively defeated might be released.

**Lens 4: Computational Tractability**

Interpretation A is much simpler:
- No need to track defeat status for evidence release
- No need to handle partial release
- Type checking is standard affine type checking

Interpretation B requires:
- Tracking defeat levels for each evidence usage
- Defining "partial release" semantics
- Handling release propagation when defeat chains change

---

## 3. Proposed Resolution

### 3.1 The Commitment Model

I propose **Interpretation A with a refinement**: Evidence is permanently consumed by commitment, but CLAIR should distinguish between:

1. **Active commitment**: Evidence supporting an undefeated derivation
2. **Defeated commitment**: Evidence whose derivation was fully defeated
3. **Weakened commitment**: Evidence whose derivation was partially undercut

**Key insight**: The distinction matters not for *releasing* evidence, but for *understanding the epistemic state* and potentially for *diagnostic purposes*.

### 3.2 Rationale: Consumption ≠ Effectiveness

The affine discipline in Thread 3.46 prevents **double-counting**. The core principle is:

> The same evidence, counted multiple times, doesn't provide more justification than a single count.

This principle is about **epistemic accounting**, not about **information utilization efficiency**. Whether the derivation succeeds or fails, the accounting happened when the evidence was committed.

**Analogy**: In resource economics, spending money on a project consumes the money. If the project fails, you don't get the money back—it was spent. The same applies to epistemic resources: committing evidence to a derivation "spends" it.

### 3.3 Handling the Edge Cases

**Case 1: Full undercut before derivation completes**

```clair
let e : AffineEvidence<A> = ...
let d : Evidence<UndercutsE> = ...  -- discovered before e→P committed

-- Should we allow reconsidering e's use?
-- Proposal: Allow UNCOMMITTING before final derivation
derive (uncommit e) for Q  -- e is back, can support Q instead
```

This requires an `uncommit` operation that's only valid before the derivation is finalized. Once committed to P, no take-backs.

**Case 2: Partial undercut**

```clair
let derivation = derive P from e with confidence c
let defeated_deriv = undercut derivation by d with strength 0.5

-- e is consumed, derivation now has confidence c × 0.5
-- e cannot be reused for Q
```

The partial undercut doesn't release e—it just weakens the derivation's confidence.

**Case 3: Full undercut after commitment**

```clair
let derivation = derive P from e with confidence c
let defeated_deriv = undercut derivation by d with strength 1.0

-- e is still consumed (was committed)
-- derivation has confidence 0
-- e cannot be reused for Q
```

**Case 4: Reinstatement**

```clair
let derivation = derive P from e
let undercut_d = undercut derivation by d
let reinstated = undercut undercut_d by counter_d  -- counter-defeats d

-- e remains consumed
-- derivation's confidence is restored via reinstatement formula
-- (Thread 2.12: A_final = A_base × (1 - D_base × (1 - E_base)))
```

Reinstatement doesn't release e—it just restores the derivation's confidence through the defeat chain.

---

## 4. Interaction with Rebut

### 4.1 Rebut Targets Conclusions, Not Evidence

Rebutting defeat attacks the **conclusion**, not the evidence or the inference:

```
e ——support——> P
               ↑
r ——rebut——————+  (r provides evidence for ¬P)
```

The evidence `e` supported `P`. The rebuttal `r` provides counter-evidence. Neither is "released"—both are committed to their respective conclusions.

### 4.2 Affine Status of Rebut Evidence

The rebut evidence `r` is itself subject to affine discipline:
- `r` supports ¬P (or weakens P)
- `r` is consumed by this use
- `r` cannot also support some unrelated Q

```clair
let r : AffineEvidence<NotP> = ...
let rebuttal = rebut P_derivation by r

-- r is now consumed
-- r cannot be used for derive(Q) from r
```

### 4.3 Symmetric Treatment

Both supporting evidence and rebutting evidence are affine resources:
- Supporting evidence is consumed when it supports
- Rebutting evidence is consumed when it rebuts
- Neither can be reused elsewhere

This maintains **epistemic balance**—you can't use the same counter-evidence against multiple conclusions any more than you can use the same evidence for multiple conclusions.

---

## 5. Defeat Evidence and Affine Typing

### 5.1 The Defeater's Evidence

The undercut itself is supported by evidence. Is the defeater's evidence also affine?

```clair
let e : AffineEvidence<A> = ...         -- supports P
let d : AffineEvidence<Unreliable> = ...  -- evidence that e's source is unreliable

let derivation = derive P from e
let defeated = undercut derivation by d
```

**Question**: Is `d` consumed by being used for an undercut?

**Answer**: Yes, if we're tracking epistemic resources consistently. The evidence that something is unreliable is itself an epistemic resource that shouldn't be double-counted.

### 5.2 Reusing Undercut Evidence

Consider this scenario:

```clair
let d : AffineEvidence<WitnessWasDrunk> = ...

let deriv1 = derive P from witness_says_P
let undercut1 = undercut deriv1 by d  -- d attacks witness's reliability for P

let deriv2 = derive Q from witness_says_Q  -- same witness
-- Can we use d again to undercut deriv2?
```

Under strict affine typing, `d` can only be used once. But this seems wrong—if the witness was drunk, this affects all their testimony, not just one statement.

**Resolution**: The evidence "witness was drunk" should be marked as **exponential** (!):

```clair
let d : !Evidence<WitnessWasDrunk> = ...  -- reusable evidence

-- Can now use d for multiple undercuts
let undercut1 = undercut deriv1 by d
let undercut2 = undercut deriv2 by d
```

This aligns with Thread 3.46's recommendation that "some evidence genuinely can be reused" and should be marked with the exponential.

### 5.3 Classification of Defeat Evidence

| Defeat Evidence Type | Affine Status | Rationale |
|---------------------|---------------|-----------|
| Specific counter-evidence (e.g., "P is false because X") | Affine | Specific to conclusion |
| Source reliability attack (e.g., "witness unreliable") | Exponential (!) | Affects all uses of source |
| Methodological critique (e.g., "flawed experimental design") | Exponential (!) | Affects all conclusions from method |
| Domain-general defeater (e.g., "optical illusions exist") | Exponential (!) | Potentially applies to many |

---

## 6. Formal Semantics

### 6.1 Extended Typing Judgment

Building on Thread 3.46's affine context, I extend the typing judgment to handle defeat:

```
Γ; Δ ⊢ e : A @c
```

Where:
- Γ is the exponential (unrestricted) context
- Δ is the affine context (each evidence used at most once)
- e is the expression
- A is the type
- c is the confidence bound

**Derivation Rule** (consuming evidence):
```
Γ; Δ, e : AffEvidence<B> ⊢ M : A @c   B supports A
───────────────────────────────────────────────────────
Γ; Δ ⊢ derive M from e : Belief<A> @(c × conf(e))
```

**Undercut Rule** (defeating evidence is also affine):
```
Γ; Δ₁ ⊢ D : Belief<A> @c   Γ; Δ₂ ⊢ d : AffEvidence<Attacks(D)> @d_conf
────────────────────────────────────────────────────────────────────────
Γ; Δ₁, Δ₂ ⊢ undercut D by d : Belief<A> @(c × (1 - d_conf))
```

Note: The undercut rule requires **disjoint contexts** (Δ₁ and Δ₂ don't overlap), ensuring the undercut evidence is distinct from the original derivation's evidence.

**Rebut Rule**:
```
Γ; Δ₁ ⊢ D_for : Belief<A> @c   Γ; Δ₂ ⊢ D_against : Belief<¬A> @c'
──────────────────────────────────────────────────────────────────────
Γ; Δ₁, Δ₂ ⊢ rebut D_for by D_against : Belief<A> @(c / (c + c'))
```

### 6.2 Evidence Consumption Invariant

**Theorem (Consumption Irreversibility)**:
Once affine evidence e is consumed in a derivation, defeat of that derivation does not return e to the affine context.

**Proof sketch**:
1. The typing rules only move evidence from Δ to "consumed" (implicit)
2. No rule adds evidence back to Δ
3. Defeat rules transform the confidence of existing derivations but don't modify contexts
4. Therefore, evidence consumption is monotonic and irreversible. ∎

### 6.3 Exponential Promotion for Defeat Evidence

**Promotion Rule** (marking evidence as reusable):
```
Γ, d : Evidence<DefeatsSource(S)> ; · ⊢ M : A @c
────────────────────────────────────────────────── (Source-defeat promotion)
Γ ; · ⊢ let !d = d in M : A @c
```

This allows source-level defeat evidence to be promoted to exponential, making it reusable across derivations from that source.

---

## 7. Practical Implications

### 7.1 Design Recommendations

**R1: Evidence consumption is permanent**

CLAIR should treat evidence consumption as permanent, regardless of subsequent defeat. This is simpler, more consistent with linear type theory, and matches the "spending" interpretation of affine resources.

**R2: Defeat evidence follows the same discipline**

Evidence used for undercut or rebut is itself an affine resource (unless explicitly marked exponential). This prevents "free" attacks that can be reused without epistemic cost.

**R3: Source-level defeaters should be exponential**

Evidence that attacks a source's reliability (rather than a specific inference) should be marked exponential, allowing it to affect all derivations from that source.

**R4: Provide uncommit for work-in-progress**

CLAIR could provide an `uncommit` operation for derivations that haven't been finalized, allowing reallocation of evidence before commitment.

### 7.2 Example: Witness Testimony

```clair
-- Witness testimony (affine by default)
let testimony : AffEvidence<SawEvent> = witness_says(...)

-- Source reliability attack (exponential)
let drunk : !Evidence<WitnessWasDrunk> = blood_test(...)

-- First derivation
let deriv1 = derive EventHappened from testimony @0.8
-- testimony is now consumed

-- Undercut with exponential defeater
let defeated1 = undercut deriv1 by drunk @0.9
-- drunk is NOT consumed (exponential)
-- deriv1 confidence: 0.8 × (1 - 0.9) = 0.08

-- INVALID: trying to reuse testimony
let deriv2 = derive RelatedEvent from testimony  -- TYPE ERROR: testimony consumed
```

### 7.3 Example: Multiple Independent Witnesses

```clair
-- Two independent witnesses (affine)
let t1 : AffEvidence<SawEvent> = witness1_says(...)
let t2 : AffEvidence<SawEvent> = witness2_says(...)

-- Aggregate independent evidence
let combined = aggregate t1 t2  -- Both consumed, confidence via ⊕
-- Neither t1 nor t2 can be reused

-- General skepticism (exponential, but weak)
let skeptic : !Evidence<MemoryUnreliable> @0.1 = common_knowledge(...)

-- Can apply to combined derivation
let weakened = undercut combined by skeptic
-- Combined confidence reduced by (1 - 0.1) = 0.9 factor
```

---

## 8. What About Partial Consumption?

### 8.1 The Intuition

If evidence `e` is used in a derivation that's partially undercut (d = 0.5), intuitively `e` contributed only "half its information" to the conclusion. Should the other half be available?

### 8.2 Analysis

**Against partial release**:
1. What would "half" evidence look like? Evidence isn't naturally divisible.
2. The confidence reduction is in the *derivation*, not in the *evidence itself*.
3. Tracking fractional evidence consumption is complex and novel.

**For partial release**:
1. Information-theoretically, the mutual information was partially transferred.
2. Might enable more precise epistemic accounting.

### 8.3 Verdict: No Partial Release

I recommend **against** partial evidence release:
- The complexity isn't worth the precision gains
- Evidence is committed as a whole
- Defeat affects the derivation's confidence, not the evidence's availability
- The "uncommit" escape hatch handles the case where you want to redirect evidence before committing

If partial release is needed, it's better modeled by:
1. Explicit evidence splitting at the source: `let (e1, e2) = split_evidence(e)`
2. Using partial commitment upfront: `let partial_deriv = derive P from e with weight 0.5`

---

## 9. Connection to Reinstatement

### 9.1 Reinstatement Doesn't Release Evidence

Thread 2.12 established that reinstatement (when a defeater is itself defeated) restores confidence:

```
A_final = A_base × (1 - D_base × (1 - E_base))
```

Where E is the counter-defeater.

Does reinstatement change evidence's affine status? **No.**

- The original evidence e was consumed when supporting A
- The defeater d was consumed when undercutting
- The counter-defeater e' was consumed when reinstating
- All three remain consumed; reinstatement only adjusts the confidence

### 9.2 Evidence in Reinstatement Chains

```clair
let e : AffEvidence<A> = ...
let d : AffEvidence<Undercuts(e→P)> = ...
let e' : AffEvidence<Undercuts(d)> = ...

let deriv = derive P from e @0.8           -- e consumed
let defeated = undercut deriv by d @0.9    -- d consumed
let reinstated = undercut defeated by e' @0.8  -- e' consumed

-- Final confidence: 0.8 × (1 - 0.9 × (1 - 0.8)) = 0.8 × (1 - 0.18) = 0.656
-- All evidence (e, d, e') remains consumed
```

---

## 10. Edge Cases and Clarifications

### 10.1 Self-Undercutting Evidence

What if evidence undermines itself?

```clair
let paradox : AffEvidence<"This evidence is unreliable"> = ...
let deriv = derive Conclusion from paradox
let self_undercut = undercut deriv by paradox  -- Using paradox twice!
```

This should be a **type error** under affine typing—paradox can't be used both as supporting evidence and as undercut evidence.

**If we wanted to allow this** (self-undermining evidence), we'd need:
```clair
let paradox : !Evidence<"This evidence is unreliable"> = ...  -- Exponential
```

But then we should question whether this evidence should support anything in the first place.

### 10.2 Defeat Without Evidence

Can defeat happen without consuming evidence? Consider:

```clair
-- Purely logical undercut (no empirical evidence needed)
let deriv = derive "All swans are white" from observations
let logical_undercut = undercut deriv by theorem("Induction is uncertain")
```

The theorem is a piece of established knowledge—probably exponential:

```clair
let induction_uncertain : !Evidence<"Induction is uncertain"> = axiom(...)
```

This is consistent with R3: domain-general defeaters should be exponential.

### 10.3 Aggregation then Defeat

If two evidence sources are aggregated, then the aggregate is undercut:

```clair
let e1 : AffEvidence<A> = ...
let e2 : AffEvidence<A> = ...
let combined = aggregate e1 e2  -- Both consumed
let defeated = undercut combined by d
```

- e1 and e2 are both consumed by the aggregation
- d is consumed by the undercut
- The defeat applies to the combined confidence
- Neither e1 nor e2 is released

---

## 11. Limitations and Open Questions

### 11.1 Granularity of Evidence

The framework assumes evidence is atomic—you either use it or you don't. But evidence can be complex:

- A document might contain multiple independent claims
- A study might have separate findings

Should we model evidence decomposition?

**Tentative answer**: Evidence decomposition should happen explicitly through language constructs:

```clair
let doc : AffEvidence<DocumentContent> = ...
let (claim1, claim2, claim3) = decompose doc into claims
-- Now claim1, claim2, claim3 are separate affine resources
```

### 11.2 Temporal Dynamics

The current model is static. Real reasoning involves:
- Evidence arriving over time
- Defeat status changing
- Beliefs being revised

How does affine typing interact with belief revision (Thread 5)?

**Tentative answer**: Each revision operation works on the current state. Evidence consumed in the past stays consumed. New evidence is fresh. This is consistent with "spending" interpretation.

### 11.3 Inter-Conversation Evidence

Thread 3.46 raised: Does linearity persist across conversations?

For defeat interaction specifically:
- If evidence e was used in conversation 1, it's consumed there
- In conversation 2 (fresh context), is e available again?

**Tentative answer**: Conversation-local linearity is the default. Each conversation starts with fresh epistemic resources. Global linearity would require persistent memory of evidence consumption, which CLAIR (as bounded conversation) doesn't have.

---

## 12. Conclusions

### 12.1 Summary

**Task 3.48 is substantially answered.**

The interaction between epistemic linearity and defeat is governed by these principles:

1. **Evidence consumption is permanent**: Once affine evidence is committed to a derivation, it's consumed regardless of subsequent defeat.

2. **Defeat evidence is also affine**: Evidence used for undercut or rebut is itself an affine resource.

3. **Source-level defeaters are exponential**: Evidence attacking a source's reliability (rather than a specific inference) should be marked reusable.

4. **Reinstatement doesn't release evidence**: Counter-defeat restores confidence but doesn't un-consume evidence.

5. **No partial release**: Partial undercut doesn't release partial evidence.

### 12.2 Key Theorems

**Theorem (Consumption Irreversibility)**:
Evidence consumption under affine typing is monotonic—defeat does not return evidence to the available context.

**Theorem (Defeat Linearity)**:
Both supporting evidence and defeating evidence follow the affine discipline (unless explicitly exponential).

**Theorem (Context Disjointness)**:
The undercut rule requires disjoint evidence contexts, ensuring defeat evidence is distinct from derivation evidence.

### 12.3 Confidence Table

| Claim | Confidence | Justification |
|-------|------------|---------------|
| Evidence consumption is permanent (no release) | 0.85 | Type-theoretic consistency, simplicity |
| Defeat evidence is itself affine | 0.90 | Symmetric treatment, prevents free attacks |
| Source-level defeaters should be exponential | 0.85 | Affects all derivations from source |
| Reinstatement doesn't release evidence | 0.90 | Consistent with consumption model |
| Partial release should be avoided | 0.80 | Complexity vs. precision tradeoff |
| This framework is implementable | 0.85 | Standard affine typing machinery |

### 12.4 Impact on CLAIR

This exploration:
- Clarifies how Thread 3.46's affine typing interacts with Thread 2.10's defeat semantics
- Provides typing rules for defeat operations in an affine context
- Identifies when defeat evidence should be exponential vs. affine
- Maintains the simplicity of the "evidence as resource" metaphor through defeat

### 12.5 New Questions Raised

- **3.51**: How does evidence decomposition work formally?
- **3.52**: How does affine evidence interact with belief revision (Thread 5)?
- **3.53**: What are the computational costs of tracking affine defeat evidence?

---

## 13. References

### CLAIR Internal

- Thread 3.46: exploration/thread-3.46-epistemic-linearity.md
- Thread 2.10: exploration/thread-2.10-defeat-confidence.md
- Thread 2.12: exploration/thread-2.12-reinstatement.md
- Thread 2.13: exploration/thread-2.13-correlated-evidence.md

### External

- **Girard, J-Y.** (1987). "Linear Logic." *Theoretical Computer Science*.
- **Walker, D.** (2005). "Substructural Type Systems." *Advanced Topics in Types and Programming Languages*.
- **Pollock, J.** (1987). "Defeasible Reasoning." *Cognitive Science*.
- **Dung, P.M.** (1995). "On the acceptability of arguments." *Artificial Intelligence*.

---

*Thread 3.48 Status: Substantially explored. Evidence consumption is permanent regardless of defeat. Defeat evidence follows the same affine discipline. Source-level defeaters should be exponential. Formal typing rules provided. Ready for implementation integration.*
