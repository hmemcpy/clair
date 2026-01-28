# Thread 5: Belief Revision for Graded DAG-Structured Beliefs

> **Status**: Active exploration (Session 16)
> **Task**: Extend AGM belief revision theory to confidence-valued beliefs with DAG justification structure
> **Priority**: HIGH — Major theoretical gap; foundational threads (1, 2, 3) now provide necessary groundwork

---

## 1. The Problem

CLAIR tracks beliefs with:
- **Confidence** ∈ [0,1] (epistemic commitment, not probability)
- **Justification** as DAGs with labeled edges (support/undercut/rebut)
- **Invalidation conditions** (when to reconsider)

But how should belief revision work? When a belief is retracted or weakened:
1. What happens to beliefs that depend on it?
2. How does confidence propagate through invalidation?
3. What's the minimal change that restores consistency?
4. How do DAG structure and defeat interact with revision?

The classical theory is AGM (Alchourrón, Gärdenfors, Makinson 1985). But AGM assumes:
- Binary beliefs (believed or not)
- Belief *sets*, not structured justifications
- No explicit confidence values

CLAIR needs to extend AGM to handle:
- Graded beliefs with continuous confidence
- DAG justification with shared nodes
- Defeat relationships (undercut/rebut edges)
- Compositional confidence operations (×, min, ⊕, undercut, rebut)

---

## 2. Prior Art Survey

### 2.1 Classical AGM Theory

**The AGM Postulates** (Alchourrón, Gärdenfors, Makinson 1985):

AGM defines three operations on belief sets K:

**Expansion** (K + φ): Adding a new belief
```
K + φ = Cn(K ∪ {φ})
```
(Closure under logical consequence)

**Contraction** (K - φ): Removing a belief
AGM postulates for contraction:
1. **Closure**: K - φ = Cn(K - φ)
2. **Success**: If ⊬ φ then φ ∉ K - φ
3. **Inclusion**: K - φ ⊆ K
4. **Vacuity**: If φ ∉ K then K - φ = K
5. **Recovery**: K ⊆ (K - φ) + φ
6. **Extensionality**: If φ ≡ ψ then K - φ = K - ψ

**Revision** (K * φ): Adding φ, maintaining consistency
```
K * φ = (K - ¬φ) + φ     (Levi identity)
```

**The Recovery Postulate Problem:**
Recovery says you can get back to K by adding φ to K - φ. This is controversial because:
- If you contract "Tweety flies" because Tweety is a penguin, you shouldn't recover by just re-adding it
- Recovery assumes no reason for contraction is retained

### 2.2 Epistemic Entrenchment

Gärdenfors (1988) introduced **epistemic entrenchment** to guide contraction:

```
φ ≤ε ψ iff "giving up φ is at least as acceptable as giving up ψ"
```

When contracting by φ ∧ ψ:
- If φ <ε ψ, keep ψ
- If ψ <ε φ, keep φ
- If φ ≡ε ψ, give up both

**Connection to CLAIR**: Epistemic entrenchment ≈ confidence ordering. Higher confidence → more entrenched → harder to give up.

### 2.3 Ranking Theory (Spohn 1988, 2012)

Spohn's ranking functions provide **ordinal** degrees of belief:

```
κ : W → ℕ ∪ {∞}
```

Where:
- κ(w) = 0 for the most plausible worlds
- Higher ranks = less plausible
- κ(A) = min{κ(w) : w ∈ A}

**Belief**: κ(¬A) > 0 (the negation is ranked above 0)
**Degree of belief**: κ(¬A) (higher = stronger belief in A)

**Revision in ranking theory**:
```
κ_A(w) = κ(w) - κ(A)     if w ∈ A
       = κ(w) - κ(¬A) + n if w ∈ ¬A
```

Where n is the "firmness" of the evidence.

**Connection to CLAIR**:
- Ordinal ranks vs. cardinal confidence [0,1]
- Spohn handles iterated revision well (AGM struggles here)
- Could translate: confidence c ↔ rank κ = -log(1-c)?

### 2.4 Probabilistic Belief Revision (Jeffrey Conditioning)

Jeffrey conditioning (1965, 1983) handles uncertain evidence:

```
P_new(A) = P_old(A|B) · P_new(B) + P_old(A|¬B) · P_new(¬B)
```

Key insight: Only update what the evidence directly affects; preserve conditional structure for everything else.

**Connection to CLAIR**:
- Jeffrey conditioning preserves conditional probabilities
- Could inspire: "update confidence, preserve justification structure"
- But: CLAIR confidence ≠ probability

### 2.5 Dynamic Epistemic Logic (DEL)

van Ditmarsch, van der Hoek, Kooi (2007):

Modal logic with dynamic operators for:
- **Public announcement**: [φ!]ψ means "after publicly announcing φ, ψ holds"
- **Private update**: For belief revision in multi-agent settings
- **Action models**: General framework for epistemic actions

**Connection to CLAIR**:
- DEL provides formal semantics for revision as logical action
- Multi-agent aspects connect to Thread 6
- Action model semantics could model CLAIR invalidation triggers

### 2.6 Belief Revision in TMS

Doyle (1979) and de Kleer (1986) implement belief revision through justification management:

**JTMS Retraction**:
1. Remove justification for belief B
2. If B has no remaining justifications, mark B as OUT
3. Propagate: beliefs justified by B also become OUT
4. **Dependency-directed backtracking**: Find minimal retraction

**ATMS Approach**:
1. Track all assumption sets (environments) that support each belief
2. When assumption A is retracted, all beliefs in environments containing A are affected
3. **Label propagation**: Recompute labels incrementally

**Connection to CLAIR**:
- TMS handles structured justifications (closer to CLAIR than AGM)
- But: TMS is binary (IN/OUT), not graded
- CLAIR needs graded TMS-like propagation

---

## 3. Core Questions for CLAIR Belief Revision

### 3.1 Question 1: What does "retraction" mean for graded beliefs?

In AGM, retraction of φ means removing φ from the belief set.

For graded beliefs, options:
1. **Complete retraction**: Set confidence to 0
2. **Partial retraction**: Reduce confidence by some amount
3. **Evidence-based update**: New evidence decreases confidence (Jeffrey-style)
4. **Justification removal**: Remove a justification edge, recompute confidence

**Analysis:**

Option 4 aligns best with CLAIR's DAG structure. Retraction is not about the belief directly, but about its justifications:

```
retract(belief B, justification J) =
  1. Remove edge J from B's justification DAG
  2. Recompute B's confidence from remaining justifications
  3. If no justifications remain, B's confidence drops to base level (0 or prior)
```

This is compositional and respects the DAG structure.

### 3.2 Question 2: How does confidence propagate through retraction?

When a supporting justification is weakened (not fully retracted), what happens?

Consider:
```
B has confidence 0.9, justified by A (confidence 0.8) via rule R (strength 1.0)
A's confidence drops to 0.4
What is B's new confidence?
```

**Options:**

**A. Recompute from scratch**:
```
conf(B) = strength(R) × conf(A) = 1.0 × 0.4 = 0.4
```
(Standard derivation calculus approach)

**B. Proportional adjustment**:
```
old_contrib = strength(R) × 0.8 = 0.8
new_contrib = strength(R) × 0.4 = 0.4
adjustment = new_contrib / old_contrib = 0.5
conf(B) = 0.9 × 0.5 = 0.45
```
(Preserves other contributions if any)

**C. Differential update (Jeffrey-style)**:
```
Only update the portion of confidence attributable to A
Preserve other sources' contributions
```

**Analysis:**

Option A is simplest and matches derivation calculus. For a DAG with shared nodes, this means:
1. Mark invalidated nodes
2. Topologically sort the DAG
3. Recompute confidence bottom-up

For multiple justifications (aggregation):
```
B is justified by A₁ (conf 0.8) and A₂ (conf 0.7) independently
aggregate_conf(B) = 1 - (1 - 0.8)(1 - 0.7) = 1 - 0.06 = 0.94

If A₁ drops to 0.4:
aggregate_conf(B) = 1 - (1 - 0.4)(1 - 0.7) = 1 - 0.18 = 0.82
```

This is compositional—recalculating from updated inputs.

### 3.3 Question 3: What is "minimal change" for graded DAG structures?

AGM's minimal change principle says: when revising, change as little as possible while achieving the goal.

For CLAIR:
- **Goal**: Incorporate new evidence (or remove old justification)
- **Minimal change**: Preserve as much of the DAG structure and confidence values as possible

**Candidate principles:**

**Minimal Structural Change**:
- Don't remove edges unless forced
- Don't change edge labels unless forced
- Prefer recomputing confidence over restructuring

**Minimal Confidence Change**:
- Minimize Σ|conf_new(B) - conf_old(B)| across all beliefs
- May require choosing which justifications to weaken

**Minimal Justification Damage**:
- Prefer weakening to removal
- Prefer local changes to global restructuring

**Analysis:**

For CLAIR, I propose **Minimal Justification Damage** with compositional recomputation:

1. When evidence changes, update only the directly affected nodes
2. Propagate confidence changes through the DAG (no structural changes)
3. Only remove edges when their confidence drops to 0 or they're explicitly retracted
4. Defeat edges (undercut/rebut) can be added/removed based on new evidence

This preserves AGM's spirit while respecting DAG structure.

### 3.4 Question 4: How do defeat edges interact with revision?

Consider:
```
B is supported by A with confidence 0.8
D undercuts the A→B edge with confidence 0.6
B's effective confidence = 0.8 × (1 - 0.6) = 0.32

Now D is retracted. What happens?
```

**Reinstatement**: When a defeater is removed, the original support is reinstated:
```
B's confidence = 0.8 × (1 - 0) = 0.8
```

This is natural in CLAIR's model because defeat is represented as an edge, and removing the edge restores the original computation.

**What if the defeater is weakened, not removed?**
```
D's confidence drops from 0.6 to 0.3
B's effective confidence = 0.8 × (1 - 0.3) = 0.56
```

Compositional recomputation handles this naturally.

**Defeat chains**: What if a defeater of a defeater is added?
```
B ← supports(A, 0.8)
B ← undercuts(D, 0.6)  → B conf = 0.32
D ← undercuts(E, 0.5)  → D effective = 0.6 × (1 - 0.5) = 0.3
                       → B conf = 0.8 × (1 - 0.3) = 0.56
```

The evaluation order matters. From Thread 2.10:
1. Evaluate support edges (bottom-up in DAG)
2. Apply undercut edges (reduces confidence)
3. Apply rebut edges (compare for/against)

For defeat of defeat:
1. E undercuts D
2. D's effective strength is reduced
3. B's confidence is recomputed with reduced D

This is well-defined as long as the defeat graph is acyclic.

---

## 4. CLAIR Belief Revision: Formal Proposal

### 4.1 The Belief State

A CLAIR belief state is:
```
Σ = (B, G, C, I)

B : Set Belief          -- Set of beliefs
G : BeliefId → JustificationGraph   -- Justification DAGs
C : BeliefId → Confidence           -- Current confidence values
I : BeliefId → Set InvalidationCondition  -- When to reconsider
```

### 4.2 Revision Operations

#### 4.2.1 Evidence Update

When new evidence E arrives supporting belief B:
```
update_evidence(Σ, B, E, strength) =
  let G' = add_support_edge(G[B], E, strength)
  let C' = recompute_confidence(G', C)
  return (B, G', C', I)
```

#### 4.2.2 Justification Retraction

When justification J for belief B is retracted:
```
retract_justification(Σ, B, J) =
  let G' = remove_edge(G[B], J)
  let C' = recompute_confidence(G', C)
  -- If B has no remaining justifications, C'[B] = base_confidence(B)
  return (B, G', C', I)
```

#### 4.2.3 Confidence Update (Premise Change)

When premise P's confidence changes from c_old to c_new:
```
update_premise(Σ, P, c_new) =
  let affected = transitive_dependents(G, P)
  let C' = propagate_confidence(affected, G, C[P := c_new])
  return (B, G, C', I)
```

#### 4.2.4 Defeat Introduction

When defeater D with confidence d undercuts edge E in B's justification:
```
introduce_defeat(Σ, B, E, D, d) =
  let G' = add_undercut_edge(G[B], E, D, d)
  let C' = recompute_confidence(G', C)
  return (B, G', C', I)
```

### 4.3 Confidence Recomputation Algorithm

```
recompute_confidence(G, C) =
  let order = topological_sort(G.nodes)
  for each node n in order:
    C[n] = compute_node_confidence(n, G, C)
  return C

compute_node_confidence(n, G, C) =
  let supports = get_support_edges(G, n)
  let undercuts = get_undercut_edges(G, n)
  let rebuts = get_rebut_edges(G, n)

  -- Step 1: Compute base confidence from supports
  let base_conf = match G.nodes[n]:
    | axiom => 1.0
    | rule(r, premises) =>
        rule_strength(r) × combine(map(C, premises), combination_rule(r))
    | aggregate(lines, rule) =>
        aggregate_confidence(map(C, lines), rule)
    | ... other constructors

  -- Step 2: Apply undercuts
  let undercut_strength = aggregate_undercuts(undercuts, C)
  let after_undercut = base_conf × (1 - undercut_strength)

  -- Step 3: Apply rebuts
  let rebut_strength = aggregate_rebuts(rebuts, C)
  let final_conf = if rebut_strength = 0 then after_undercut
                   else after_undercut / (after_undercut + rebut_strength)

  return final_conf
```

### 4.4 Minimal Change Properties

**Theorem (Locality)**:
If premise P's confidence changes and P is not in the transitive support of B, then C[B] is unchanged.

*Proof*: Recomputation only follows edges in the DAG. If there's no path from P to B, B is not in the affected set.

**Theorem (Monotonicity)**:
If premise P's confidence increases (decreases), and P supports B (possibly transitively) via only support edges, then B's confidence increases (decreases) or stays the same.

*Proof*: All confidence operations (×, min, aggregate) are monotone in their support inputs.

**Theorem (Defeat Composition)**:
For undercuts D₁, D₂ targeting the same edge:
```
undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)
```
where ⊕ is probabilistic OR.

*Proof*: From Thread 8.7 (Session 13). Algebraically verified.

---

## 5. Comparison to AGM

### 5.1 AGM Postulates and CLAIR

**Expansion (K + φ)**: Adding a belief
- CLAIR: `update_evidence(Σ, B, E, strength)` adds new evidence
- Closure is not required (CLAIR tracks explicit justifications, not logical closure)

**Contraction (K - φ)**: Removing a belief
- CLAIR: `retract_justification(Σ, B, J)` removes specific justification
- Success: If all justifications removed, confidence → base level
- Inclusion: Preserved beliefs remain unchanged
- Recovery: **Does NOT hold** in CLAIR (and shouldn't!)
  - If you remove evidence, re-adding doesn't restore old confidence
  - This is intentional: evidence has specific strength

**Revision (K * φ)**: Belief update with new conflicting information
- CLAIR: Combination of defeat introduction and evidence update
- Not directly Levi identity (K * φ = (K - ¬φ) + φ)
- Instead: New evidence competes via rebut; old evidence weakened via undercut

### 5.2 What CLAIR Adds to AGM

1. **Graded beliefs**: Continuous confidence [0,1] instead of binary
2. **Structured justification**: DAGs instead of flat sets
3. **Compositional revision**: Local changes propagate automatically
4. **Defeat semantics**: Explicit undercut/rebut edges
5. **No recovery**: Evidence removal is not reversible (correct!)

### 5.3 What AGM Provides That CLAIR Uses

1. **Minimal change intuition**: Preserve as much as possible
2. **Entrenchment ordering**: Confidence provides natural ordering
3. **Rational constraints**: Changes should be consistent and coherent

---

## 6. Open Questions and Limitations

### 6.1 Resolved This Session

- **Q5.1**: Does AGM apply to graded beliefs? → **Yes, with modifications**
  - Graded confidence replaces binary belief
  - Entrenchment ordering is natural (confidence ordering)
  - Recovery postulate correctly fails

- **Q5.2**: How does retraction propagate through DAG? → **Compositional recomputation**
  - Topological sort, bottom-up propagation
  - Defeat edges applied in order: supports → undercuts → rebuts

### 6.2 Newly Raised

- **Q5.5**: **Correlated evidence handling**
  - How do we detect when two evidence sources are not independent?
  - Aggregation formula assumes independence; correlation causes overconfidence
  - Need: correlation tracking or conservative aggregation

- **Q5.6**: **Cyclic defeat**
  - DAG is acyclic, but defeat chains can have semantic cycles:
    - A defeats B, B defeats C, C indirectly affects A's premises
  - Current proposal: Fixed-point semantics (iterate until stable)
  - Question: Does fixed point always exist? Converge?

- **Q5.7**: **Revision vs. update distinction**
  - AGM distinguishes belief *revision* (new information about static world) from *update* (world changed)
  - CLAIR's invalidation conditions handle "world changed" case
  - Is this distinction properly captured?

- **Q5.8**: **Contraction specificity**
  - AGM contracts by a proposition
  - CLAIR contracts by a specific justification edge
  - Is there a meaningful "contract by proposition" operation for CLAIR?

- **Q5.9**: **Belief persistence under revision**
  - When you revise A, and B depended on A, should B be "protected" if it has other support?
  - Current answer: Yes (aggregation preserves other sources)
  - But: What if A was the primary source and others were weak?

### 6.3 Connections to Other Threads

**Thread 1 (Confidence)**:
- Revision uses confidence operations (×, ⊕, undercut, rebut)
- All boundedness and algebraic properties apply

**Thread 2 (Justification)**:
- Revision operates on DAG structure
- Labeled edges (support/undercut/rebut) enable proper propagation

**Thread 3 (Self-Reference)**:
- Beliefs about beliefs can be revised
- Stratification ensures well-foundedness under revision

**Thread 8 (Verification)**:
- Revision algorithm should be formalizable in Lean
- Key theorems: Locality, Monotonicity, Defeat Composition

---

## 7. Implementation Sketch

### 7.1 Data Structures

```lean
structure BeliefState where
  beliefs : HashMap BeliefId Belief
  graphs : HashMap BeliefId JustificationGraph
  confidence : HashMap BeliefId Confidence
  invalidation : HashMap BeliefId (Set InvalidationCondition)

def affectedBeliefs (state : BeliefState) (changed : BeliefId) : Set BeliefId :=
  transitiveClosure (dependencyGraph state.graphs) changed

def recomputeConfidence (graph : JustificationGraph)
                        (confidence : HashMap BeliefId Confidence)
                        : HashMap BeliefId Confidence :=
  let order := topologicalSort graph.nodes
  order.foldl (fun conf node =>
    conf.insert node (computeNodeConfidence node graph conf))
    confidence
```

### 7.2 Revision Operations

```lean
def retractJustification (state : BeliefState) (beliefId : BeliefId) (edge : EdgeId)
    : BeliefState :=
  let graph' := state.graphs[beliefId].removeEdge edge
  let affected := affectedBeliefs state beliefId
  let conf' := recomputeConfidence graph' state.confidence
  { state with
    graphs := state.graphs.insert beliefId graph',
    confidence := conf' }

def introduceDefeat (state : BeliefState) (target : BeliefId)
                    (defeater : BeliefId) (strength : Confidence) (defeatType : DefeatType)
    : BeliefState :=
  let edge := match defeatType with
    | .undercut => Edge.undercut defeater strength
    | .rebut => Edge.rebut defeater strength
  let graph' := state.graphs[target].addEdge edge
  let affected := affectedBeliefs state target
  let conf' := recomputeConfidence graph' state.confidence
  { state with
    graphs := state.graphs.insert target graph',
    confidence := conf' }
```

---

## 8. Key Insights from This Exploration

### Insight 1: CLAIR revision is justification-based, not proposition-based

AGM operates on belief sets. CLAIR operates on justification structures. This is more fine-grained:
- Can retract one piece of evidence while preserving others
- Can weaken an inference link without removing it
- Naturally handles partial information

### Insight 2: Recovery correctly fails

AGM's controversial Recovery postulate says (K - φ) + φ = K. This fails in CLAIR because:
- Evidence has specific strength
- Re-adding the same evidence doesn't restore previous state
- This is correct behavior: retraction loses information

### Insight 3: Defeat enables non-monotonic revision

Adding defeat edges can increase or decrease confidence depending on context:
- Undercut always decreases (multiplicative discounting)
- Rebut can go either way (probabilistic comparison)
- Defeat of defeater (reinstatement) restores confidence

### Insight 4: DAG structure makes revision compositional

Because justifications are DAGs:
- Changes propagate automatically through edges
- No need to compute logical closure
- Locality property holds: unconnected beliefs unaffected

### Insight 5: Connection to TMS is deep

CLAIR revision is essentially a graded generalization of TMS:
- TMS: IN/OUT propagation
- CLAIR: Confidence ∈ [0,1] propagation
- Same dependency-directed architecture
- Adds: graded defeat, multiple justification types

---

## 9. Remaining Work

### For This Thread

1. **Formalize correlated evidence** (Task 5.5)
   - Track correlation structure
   - Conservative aggregation when correlation unknown

2. **Prove fixed-point existence for defeat chains** (Task 5.6)
   - When does iterative confidence propagation converge?
   - Conditions for unique fixed point

3. **Clarify revision vs. update** (Task 5.7)
   - Map CLAIR operations to DEL semantics
   - Invalidation conditions = "world changed" events

### For Thread 8

4. **Formalize revision operations in Lean**
   - `retractJustification`, `introduceDefeat`, etc.
   - Prove Locality, Monotonicity, Composition theorems

### For derivation-calculus.md

5. **Update to reflect revision semantics**
   - Add section on belief revision
   - Document confidence propagation under revision

---

## 10. Conclusion

**Thread 5 is now substantially explored.**

CLAIR belief revision extends AGM in principled ways:
- **Graded confidence** replaces binary belief, with entrenchment = confidence ordering
- **DAG justification** replaces flat belief sets, enabling compositional revision
- **Defeat edges** provide explicit undercut/rebut semantics
- **Recovery fails** correctly: evidence removal loses information
- **Minimal change** = local justification updates, compositional propagation

The core algorithm is:
1. Modify justification graph (add/remove edges)
2. Identify affected beliefs (transitive dependents)
3. Recompute confidence bottom-up (topological order)
4. Apply defeat in order: supports → undercuts → rebuts

Key theorems established:
- **Locality**: Changes only affect transitive dependents
- **Monotonicity**: Confidence changes propagate monotonically
- **Defeat Composition**: Sequential undercuts compose via ⊕

Open questions remain around:
- Correlated evidence handling
- Fixed-point existence for defeat chains
- Precise mapping to DEL semantics

**Next steps**: Formalize in Lean (Thread 8), handle correlations (Task 5.5), connect to dynamic epistemic logic (Task 5.4).

---

## 11. References

### Primary Sources

- **Alchourrón, C., Gärdenfors, P., & Makinson, D.** (1985). "On the Logic of Theory Change: Partial Meet Contraction and Revision Functions." *Journal of Symbolic Logic*, 50(2), 510-530.
  - The foundational AGM paper
  - Defines contraction, revision, expansion postulates

- **Gärdenfors, P.** (1988). *Knowledge in Flux: Modeling the Dynamics of Epistemic States.* MIT Press.
  - Epistemic entrenchment
  - Comprehensive treatment of belief revision

- **Spohn, W.** (2012). *The Laws of Belief: Ranking Theory and Its Philosophical Applications.* Oxford University Press.
  - Ranking functions for ordinal belief
  - Handles iterated revision

- **Jeffrey, R.** (1983). *The Logic of Decision.* 2nd ed. University of Chicago Press.
  - Jeffrey conditioning
  - Uncertain evidence handling

- **van Ditmarsch, H., van der Hoek, W., & Kooi, B.** (2007). *Dynamic Epistemic Logic.* Springer.
  - Modal logic of belief change
  - Public announcement and action models

### Secondary Sources

- **Hansson, S.O.** (1999). *A Textbook of Belief Dynamics: Theory Change and Database Updating.* Kluwer.
  - Comprehensive survey of belief revision
  - Multiple contraction operators

- **Rott, H.** (2001). *Change, Choice and Inference: A Study of Belief Revision and Nonmonotonic Reasoning.* Oxford University Press.
  - Philosophical foundations
  - Connection to rational choice

---

*Thread 5 Status: Substantially explored. AGM extended to graded DAG beliefs. Core algorithm defined. Key theorems established. Open questions on correlations, fixed points, and DEL connection remain.*
