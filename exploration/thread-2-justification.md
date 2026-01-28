# Thread 2: Justification Structure

> **Status**: Active exploration (Session 9)
> **Question**: Are trees adequate for representing justification, or do we need DAGs, cycles, or other structures?
> **Priority**: HIGH — Crisp question with clear answer emerging

---

## 2.1 The Problem

CLAIR's `derivation-calculus.md` defines justifications as trees:

```
j ::= axiom                    -- primitive justification
    | rule(r, j₁, ..., jₙ)     -- derived by rule
    | assumption(a)            -- depends on assumption
    | choice(opts, c, reason)  -- result of decision
```

This is a tree structure: each justification node has exactly one "parent" in the derivation (the rule that created it) and zero or more "children" (the sub-justifications).

**Central question:** Is this structure adequate for all forms of reasoning?

This exploration systematically examines cases where trees might fail.

---

## 2.2 Case Analysis

### 2.2.1 Case 1: Shared Premises (DAGs)

Consider a computation that uses the same belief twice:

```clair
let population = belief(1000000, 0.95, source: census)
let sample_size = belief(1000, 0.90, source: survey)
let ratio = derive population, sample_size by divide
let inverse_ratio = derive sample_size, population by divide
let product = derive ratio, inverse_ratio by multiply
  -- product should be 1.0
```

In a tree representation:
```
             product
              /   \
         ratio    inverse_ratio
          / \        /    \
   population sample_size sample_size population
```

Here `population` and `sample_size` appear twice—as separate subtrees. But logically, they're the **same** beliefs. If `population` is invalidated, both `ratio` and `inverse_ratio` should be invalidated—but in a tree with copies, we'd need to track that these are the same node.

**This demonstrates justification is naturally a DAG (Directed Acyclic Graph):**

```
              product
              /     \
         ratio      inverse_ratio
           |  \    /    |
           |   \  /     |
           |    \/      |
           |    /\      |
           |   /  \     |
        population  sample_size
```

Now each premise appears once, with multiple edges pointing to it.

**Implications for CLAIR:**
- Justification must use explicit sharing (hash-consing or node references)
- Invalidation propagation must handle shared nodes correctly
- The "tree" optimization in derivation-calculus.md (§10) already mentions hash-consing, but the fundamental DAG nature should be acknowledged in the core model

**Verdict: Trees inadequate. DAGs required.**

---

### 2.2.2 Case 2: Mutual Support (Cycles?)

A more challenging case: **coherentism** in epistemology suggests beliefs can mutually support each other.

**Example (Theory-observation interdependence):**
```clair
let theory_T = belief(
  "General relativity is correct",
  0.95,
  supported_by: [observation_O, measurement_M]
)

let observation_O = belief(
  "Mercury's perihelion precesses 43 arcsec/century",
  0.99,
  interpreted_via: theory_T  -- we interpret the data through the theory!
)
```

Here:
- `theory_T` is justified partly by `observation_O`
- `observation_O` is meaningful/interpreted through `theory_T`

This is circular. In a strict tree (or even DAG), this is impossible.

**Three perspectives on cycles:**

**1. Hard foundationalism:** Cycles are a mistake. Observation should be theory-independent. The circularity above is an error in analysis—raw observation data doesn't depend on theory, only our interpretation does. Force acyclic structure.

**2. Coherentism:** Cycles are fine. Beliefs can mutually support each other. What matters is the overall coherence of the web, not its shape. Justification is inherently holistic.

**3. Pragmatic separation:** Distinguish *evidential support* from *interpretive framework*.
   - `observation_O` provides *evidence* for `theory_T` (acyclic, tracked in justification)
   - `theory_T` provides *interpretive framework* for `observation_O` (different relation, not part of evidential justification)
   - Keep support DAGs separate from interpretation graphs

**Analysis:**

True cycles in evidential support are problematic because:
1. **Bootstrap problem:** Belief A supports B which supports A allows confidence inflation with no external grounding
2. **Invalidation ambiguity:** If A loses support, does B lose support too? If B loses support, does A? Infinite regress.
3. **Well-foundedness violation:** No base case for the recursion

The prior art confirms this concern:

- **TMS (JTMS/ATMS):** Justifications must be well-founded. JTMS uses IN-lists and OUT-lists but cycles are forbidden (the belief network must be grounded).

- **Artemov's Justification Logic:** Justification terms are inductively defined. You can compose justifications (`t · s`) but cannot create loops.

- **AGM Belief Revision:** Operates on belief *sets*, not justification structures. Doesn't directly address the issue.

**Recommendation for CLAIR:**

Maintain acyclicity in the justification graph. Cyclic reasoning can be modeled as:
1. An initial non-circular justification that establishes the belief
2. Subsequent revision that may incorporate now-established beliefs

This matches how scientific theories actually develop: initial evidence → tentative theory → revised interpretation using theory → strengthened belief.

**Verdict: Cycles should remain forbidden. Well-foundedness is required.**

---

### 2.2.3 Case 3: Non-Deductive Justification

The derivation calculus focuses on *derivation*—applying rules to premises. But much reasoning is not purely deductive.

#### Abduction (Inference to Best Explanation)

```
Observation: The lawn is wet.
Best explanation: It rained last night.
Conclusion: belief("it rained last night", 0.7, ...)
```

This isn't "derive rain from wet_lawn by rule." There's no deductive rule that says "wet lawn implies rain." Instead, we're *selecting* the best hypothesis from alternatives.

**Structure needed:**
```
justification(rain) = abduction(
  observation: wet_lawn,
  hypotheses: [rain, sprinkler, flood],
  selected: rain,
  selection_reason: "most probable given no sprinkler, no flood news"
)
```

This is tree-like (observation → abduction → conclusion), but with additional structure:
- The `hypotheses` field references beliefs that are *alternatives*, not premises
- The `selection_reason` is a meta-justification for the choice

#### Analogy

```
Known: A has property P (with confidence 0.95)
Known: B is similar to A (with confidence 0.80)
Inferred: B has property P (with confidence ???)
```

Structure:
```
justification(B_has_P) = analogy(
  source: A_has_P,
  similarity: A_similar_B,
  transfer_principle: "P is a transferable property"
)
```

Still tree-like. The confidence calculation is less clear (not simple multiplication—similarity might cap or discount rather than multiply).

#### Induction

```
Observed: swan_1 is white, swan_2 is white, ..., swan_100 is white
Inferred: All swans are white (with confidence 0.8)
```

Structure:
```
justification(all_swans_white) = induction(
  instances: [swan_1_white, swan_2_white, ...],
  sample_size: 100,
  inductive_rule: "universal generalization from sample"
)
```

Tree-like: many instances → inductive conclusion.

**Assessment:** Non-deductive reasoning doesn't break the DAG structure, but it requires:
1. New justification constructors (`abduction`, `analogy`, `induction`)
2. Associated confidence propagation rules (not just multiplication)
3. Tracking of alternatives (for abduction) and similarity measures (for analogy)

**Verdict: Trees/DAGs adequate, but new constructors needed.**

---

### 2.2.4 Case 4: Defeat and Undercutting

A crucial case not addressed in the current derivation calculus: **defeaters**.

```clair
let testimony = belief("X occurred", 0.85, source: witness_A)
let underminer = belief("witness A was drunk", 0.70, source: investigation)
let updated = defeat(testimony, by: underminer)
-- updated confidence should be lower than 0.85
```

Here, `underminer` doesn't *refute* the testimony directly—it *undercuts* the justification by attacking the source's reliability.

**Pollock's (1987) classification of defeaters:**

1. **Rebutting defeater:** Evidence against the conclusion itself
   - Example: "Here's video showing X didn't occur"
   - Attacks the *belief content*

2. **Undercutting defeater:** Evidence against the justification (not the conclusion)
   - Example: "The witness was drunk and unreliable"
   - Attacks the *justification* without providing evidence for ¬P

**Tree structure problem:**

In a tree, justification flows from premises to conclusion. All edges are positive (supportive). Defeaters introduce *negative* edges—information that *removes* support rather than *adding* it.

```
        conclusion
            |
      ------+------
      |           |
  [supports]   [undercuts]
      |           |
  premise     defeater
```

This is no longer a simple tree of "derives from." It's a **labeled graph** with:
- Positive edges (supports)
- Negative edges (defeats/undercuts)

**How TMS handles defeat:**

JTMS uses OUT-lists: a justification is valid if all IN-list nodes are believed AND all OUT-list nodes are NOT believed.

```
Node: use-hs256
Justification: IN={stateless-req, secret-available}, OUT={multi-service}

"Believe use-hs256 if stateless-req and secret-available are believed,
 and multi-service is NOT believed"
```

This elegantly handles one form of defeat (negation-as-failure).

**Proposal for CLAIR:**

Option A: Extend justification algebra with `defeated` constructor:
```
j ::= axiom
    | rule(r, j₁, ..., jₙ)
    | ...
    | defeated(j, defeater, type)  -- NEW
```

Option B: Use labeled edges in the DAG:
```
edges: List (JustificationRef, EdgeType)
where EdgeType = Support | Undercut | Rebut
```

Option B is more general and aligns with how TMS works.

**Verdict: Labeled edges needed for defeat. Pure trees inadequate.**

---

### 2.2.5 Case 5: Justification Aggregation

When a belief has multiple *independent* justifications:

```clair
let conclusion = belief("climate change is real", 0.99, justified_by: [
  line1: justify(observation: temperature_records),
  line2: justify(observation: ice_core_data),
  line3: justify(observation: sea_level_rise),
  line4: justify(theory: greenhouse_physics)
])
```

These aren't premises combined by a single rule. They're independent lines of evidence that **reinforce** each other.

**Structure:**
```
           conclusion
               |
          aggregate
         /  |  |  \
       j1  j2 j3  j4
```

This is tree-like, but the semantics differ from `rule`:
- `rule(∧, j1, j2)` means "j1 AND j2 together justify"
- `aggregate(j1, j2)` means "j1 OR j2 would each suffice, and together they're stronger"

**Confidence calculation for aggregation:**

If j1 gives confidence 0.7 and j2 gives confidence 0.7 (independently):
- Multiplication would give 0.49 (wrong—should be stronger!)
- Dempster-Shafer combination: more complex formula
- Subjective Logic: has operators for fusing independent opinions

The exact formula depends on whether the lines of evidence are:
- Truly independent (multiply uncertainties, not beliefs)
- Partially correlated (need correlation model)
- Different aspects of same underlying evidence (need care not to double-count)

**Verdict: Aggregation constructor needed with special confidence rules.**

---

## 2.3 Synthesis: What Structure Does Justification Require?

| Case | Tree adequate? | What's needed? |
|------|----------------|----------------|
| Shared premises | **No** | DAG with explicit sharing |
| Mutual support (cycles) | N/A | Should remain **forbidden** (well-foundedness) |
| Non-deductive reasoning | Yes | New constructors (abduction, analogy, induction) |
| Defeat | **No** | Labeled edges (support vs. undercut vs. rebut) |
| Aggregation | Marginal | New constructor with non-multiplicative confidence |

### Conclusion

**Trees are NOT adequate for CLAIR's justification structure.**

Justification is fundamentally a **DAG with labeled edges**, where:
1. **Nodes** represent justification units (axiom, rule application, etc.)
2. **Edges** can be:
   - Support (positive contribution to confidence)
   - Undercut (attacks justification without refuting content)
   - Rebut (attacks content directly)
3. **Sharing** is explicit (same premise used in multiple derivations)
4. **Cycles** are forbidden (well-foundedness requirement)
5. **New constructors** handle abduction, analogy, induction, aggregation

---

## 2.4 Formal Proposal

### 2.4.1 Justification Node Types

```lean
inductive JustificationNode where
  -- Existing (from derivation-calculus.md)
  | axiom : JustificationNode
  | rule : (r : Rule) → List JustificationRef → JustificationNode
  | assumption : Assumption → JustificationNode
  | choice : Options → Criteria → Reason → JustificationNode

  -- New: Non-deductive reasoning
  | abduction :
      (observation : JustificationRef) →
      (hypotheses : List JustificationRef) →
      (selected : Nat) →  -- index of selected hypothesis
      (reason : SelectionReason) →
      JustificationNode
  | analogy :
      (source : JustificationRef) →
      (similarity : JustificationRef) →
      (transfer : TransferPrinciple) →
      JustificationNode
  | induction :
      (instances : List JustificationRef) →
      (inductiveRule : InductiveRule) →
      JustificationNode

  -- New: Aggregation
  | aggregate :
      (lines : List JustificationRef) →
      (combinationRule : CombinationRule) →
      JustificationNode
```

### 2.4.2 Edge Types (for Defeat)

```lean
inductive EdgeType where
  | support : EdgeType     -- positive evidential contribution
  | undercut : EdgeType    -- attacks the justification
  | rebut : EdgeType       -- attacks the content

structure JustificationRef where
  id : JustificationId
  edgeType : EdgeType
  deriving Repr, DecidableEq
```

### 2.4.3 The Full Justification Graph

```lean
structure JustificationGraph where
  nodes : HashMap JustificationId JustificationNode
  root : JustificationId
  -- Key invariant: no cycles
  acyclic : AcyclicProof nodes root

-- Acyclicity can be defined via well-founded relation
def AcyclicProof (nodes : HashMap JustificationId JustificationNode) (root : JustificationId) : Prop :=
  WellFounded (fun a b => a ∈ references(nodes.get! b))
```

### 2.4.4 Confidence Propagation

Different constructors need different propagation rules:

```lean
def propagateConfidence : JustificationNode → List Confidence → Confidence
  | .axiom, [] => 1.0
  | .rule r refs, confs => ruleStrength r * confs.minimum  -- or product
  | .abduction obs hyps sel reason, confs => abductiveConfidence obs hyps sel confs
  | .analogy src sim transfer, [srcConf, simConf] => analogicalConfidence src sim transfer srcConf simConf
  | .induction instances rule, confs => inductiveConfidence rule confs.length confs
  | .aggregate lines combRule, confs => aggregateConfidence combRule confs
  | _, _ => 0.0  -- ill-formed

-- Aggregation: independent lines of evidence combine non-multiplicatively
def aggregateConfidence (rule : CombinationRule) (confs : List Confidence) : Confidence :=
  match rule with
  | .independent =>
      -- If each line gives confidence c_i, combined uncertainty is product of uncertainties
      -- P(¬conclusion) = ∏ P(¬conclusion | line_i)
      -- So P(conclusion) = 1 - ∏(1 - c_i)
      1.0 - confs.foldl (fun acc c => acc * (1.0 - c)) 1.0
  | .correlated correlation =>
      -- Need correlation model
      sorry
```

---

## 2.5 Connection to Prior Art

### 2.5.1 Artemov's Justification Logic

Uses `t : P` where t is a justification term. The term algebra includes:
- `t + s` (sum: if t justifies P, then t+s justifies P)
- `t · s` (application: if s justifies P→Q and t justifies P, then s·t justifies Q)
- `!t` (verification: if t justifies P, then !t justifies (t : P))

This is tree-like by construction and doesn't handle:
- Defeat (no negative justifications)
- Aggregation (+ is for weakening, not strengthening)
- Sharing (terms are syntactic, not DAGs)

**CLAIR contribution:** Extend Artemov with DAG structure, labeled edges, and new constructors.

### 2.5.2 Truth Maintenance Systems

JTMS (Doyle 1979):
- Nodes are beliefs
- Justifications have IN-lists and OUT-lists
- OUT-list elements must be NOT believed for justification to hold

ATMS (de Kleer 1986):
- Tracks all consistent assumption sets
- Labels each belief with minimal environments
- Inherently DAG-like (shared assumptions)

**CLAIR contribution:** Incorporate OUT-list concept as `EdgeType.undercut`/`EdgeType.rebut`.

### 2.5.3 Subjective Logic (Jøsang)

Has explicit operators for combining independent opinions:
- Cumulative fusion: for multiple sources about same proposition
- Averaging fusion: for averaging opinions
- Constraint fusion: for combining with constraints

**CLAIR contribution:** Use Subjective Logic insights for `aggregate` confidence propagation.

### 2.5.4 Toulmin's Argument Model

Components:
- Claim (conclusion)
- Data (evidence)
- Warrant (rule connecting data to claim)
- Backing (support for warrant)
- Qualifier (confidence level)
- Rebuttal (exceptions/defeaters)

**CLAIR contribution:** Rebuttal concept aligns with `EdgeType.rebut`/`EdgeType.undercut`.

---

## 2.6 Impact on Other Threads

### Thread 1 (Confidence)
- Need new confidence propagation rules for:
  - Aggregation (non-multiplicative)
  - Defeat (subtractive/discounting)
  - Non-deductive inference (abduction, analogy, induction)

### Thread 5 (Belief Revision)
- Revision now must handle:
  - DAG invalidation (when shared node changes)
  - Defeat retraction (what happens when a defeater is retracted?)

### Thread 8 (Formal Verification)
- Need to formalize:
  - DAG structure with acyclicity invariant
  - Edge label semantics
  - Confidence propagation for new constructors

### derivation-calculus.md
- Needs update to:
  - Acknowledge DAG rather than tree structure
  - Add new constructors
  - Define labeled edges
  - Specify confidence propagation for each constructor

---

## 2.7 Open Questions

### Resolved This Session

- **Q2.1:** Are trees adequate? → **No, DAGs with labeled edges required**
- **Q2.2:** Are cycles ever acceptable? → **No, well-foundedness must be maintained**
- **Q2.3:** What about non-deductive reasoning? → **New constructors handle these within DAG structure**

### Newly Raised

- **Q2.4:** How exactly does defeat propagate confidence? Is it:
  - Multiplicative: `conf' = conf * (1 - defeater_conf)`
  - Subtractive: `conf' = max(0, conf - defeater_strength)`
  - Discounting: Subjective Logic's discounting operator

- **Q2.5:** How should aggregation handle correlated evidence? Need correlation model.

- **Q2.6:** What happens when a defeater is itself defeated? ("reinstatement" in defeasible reasoning)

- **Q2.7:** Can we prove that the new confidence propagation rules maintain [0,1] bounds?

- **Q2.8:** Performance implications of DAG structure? Hash-consing strategies?

---

## 2.8 Conclusion

**The central question is answered: Trees are NOT adequate for CLAIR's justification structure.**

The required structure is a **DAG with labeled edges**:
- DAG because premises can be shared
- Labeled because we need to distinguish support from defeat
- Acyclic because well-foundedness is required

Additional findings:
- Non-deductive reasoning (abduction, analogy, induction) requires new constructors but fits DAG structure
- Aggregation of independent evidence requires non-multiplicative confidence combination
- Prior art (TMS, Subjective Logic, Toulmin) provides resources for these extensions

**Next steps:**
1. Update derivation-calculus.md with DAG structure and new constructors
2. Define confidence propagation rules for defeat and aggregation
3. Formalize acyclicity invariant (Thread 8)
4. Connect to AGM belief revision with DAG structure (Thread 5)

---

## 2.9 References

### Primary Sources for This Thread

- **Pollock, J.** (1987). "Defeasible Reasoning." *Cognitive Science*, 11(4), 481-518.
  - Taxonomy of defeaters (rebutting vs undercutting)
  - Foundational for defeasible logic

- **Artemov, S.** (2001). "Explicit Provability and Constructive Semantics." *Bulletin of Symbolic Logic*, 7(1), 1-36.
  - Justification Logic foundations
  - Term algebra for justifications

- **Doyle, J.** (1979). "A Truth Maintenance System." *Artificial Intelligence*, 12(3), 231-272.
  - IN-lists and OUT-lists
  - Justification-based truth maintenance

- **de Kleer, J.** (1986). "An Assumption-based TMS." *Artificial Intelligence*, 28(2), 127-162.
  - Environment tracking
  - DAG structure for assumption dependencies

- **Jøsang, A.** (2016). *Subjective Logic: A Formalism for Reasoning Under Uncertainty.* Springer.
  - Opinion combination operators
  - Cumulative and averaging fusion

- **Toulmin, S.** (1958/2003). *The Uses of Argument.* Cambridge University Press.
  - Argument structure including rebuttals
  - Non-deductive argument patterns

### Secondary Sources

- **Prakken, H. & Vreeswijk, G.** (2002). "Logics for Defeasible Argumentation." In *Handbook of Philosophical Logic*, Vol. 4.
  - Comprehensive survey of defeasible reasoning

- **Besnard, P. & Hunter, A.** (2008). *Elements of Argumentation.* MIT Press.
  - Formal argumentation theory

---

*Thread 2 Status: Core question answered. Trees inadequate; DAGs with labeled edges required. Design proposal ready. New questions raised about confidence propagation for defeat and aggregation.*
