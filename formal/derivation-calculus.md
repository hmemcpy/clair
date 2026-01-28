# Derivation Calculus

This document formalizes how beliefs are derived from other beliefs in CLAIR.

## 1. Derivation as Structured Inference

Traditional computation:
```
f(x, y) = z
```

CLAIR derivation:
```
derive z from x, y by f
  where z inherits:
    - confidence from x, y
    - provenance linking to x, y
    - justification recording f
    - invalidation conditions from x, y
```

## 2. Justification Structure: DAGs, Not Trees

> **Key Finding (Thread 2, Session 9)**: Trees are NOT adequate for CLAIR's justification structure. Justification is fundamentally a **DAG (Directed Acyclic Graph) with labeled edges**.

### 2.1 Why DAGs?

**Problem with trees**: In a tree, each node has exactly one parent. But premises can be shared across multiple derivations:

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

In this example, `population` and `sample_size` are used in both `ratio` and `inverse_ratio`. A tree would require duplicating these nodes, breaking proper invalidation tracking.

**DAG properties**:
- **Explicit sharing**: Same premise can support multiple conclusions
- **Acyclicity**: Cycles remain forbidden (well-foundedness required)
- **Hash-consing**: Identical justification subtrees share the same node ID

### 2.2 Why Labeled Edges?

Not all edges represent the same relationship. CLAIR distinguishes:

```
         conclusion
             |
       ------+------
       |     |     |
  [support] [undercut] [rebut]
       |     |     |
   premise  defeater  counter-evidence
```

**Edge types**:
- **Support**: Positive contribution to confidence
- **Undercut**: Attacks the justification link (not the conclusion)
- **Rebut**: Attacks the conclusion with counter-evidence

## 3. Formal Definition

### 3.1 Derivation Judgment

```
b₁, b₂, ..., bₙ ⊢[r] b

"From beliefs b₁ through bₙ, by rule r, derive belief b"
```

### 3.2 Components of Derived Belief

Given:
- Input beliefs: `bᵢ = ⟨vᵢ, cᵢ, pᵢ, jᵢ, Iᵢ⟩` for i ∈ 1..n
- Rule: `r : (τ₁, ..., τₙ) ⇒ τ` with confidence factor `strength(r) ∈ [0,1]`

The derived belief `b = ⟨v, c, p, j, I⟩` has:

```
v = r(v₁, ..., vₙ)                           -- value: apply rule to values
c = combine(c₁, ..., cₙ, strength(r))        -- confidence: propagate
p = derived(b₁, ..., bₙ, r)                  -- provenance: record inputs
j = rule(r, j₁, ..., jₙ)                     -- justification: combine
I = ⋃ᵢ Iᵢ ∪ invalidation(r)                  -- invalidation: accumulate
```

### 3.3 The Justification Graph

```lean
structure JustificationGraph where
  nodes : HashMap JustificationId JustificationNode
  root : JustificationId
  -- Key invariant: no cycles
  acyclic : WellFounded (fun a b => a ∈ references(nodes.get! b))
```

## 4. Justification Node Types

### 4.1 Core Constructors

```lean
inductive JustificationNode where
  -- Primitive justifications
  | axiom : JustificationNode
  | assumption : Assumption → JustificationNode

  -- Deductive derivation
  | rule : (r : Rule) → List JustificationEdge → JustificationNode

  -- Decision/choice
  | choice : Options → Criteria → Reason → JustificationNode

  -- Non-deductive reasoning (Section 9)
  | abduction : AbductionData → JustificationNode
  | analogy : AnalogyData → JustificationNode
  | induction : InductionData → JustificationNode

  -- Evidence aggregation (Section 7)
  | aggregate : List JustificationEdge → CombinationRule → JustificationNode
```

### 4.2 Labeled Edges

```lean
inductive EdgeType where
  | support : EdgeType     -- positive evidential contribution
  | undercut : EdgeType    -- attacks the justification
  | rebut : EdgeType       -- attacks the conclusion

structure JustificationEdge where
  target : JustificationId
  edgeType : EdgeType
  deriving Repr, DecidableEq
```

## 5. Confidence Propagation: Support Edges

For support edges, confidence propagates according to the derivation type.

### 5.1 Conservative (Default)
```
combine(c₁, ..., cₙ, s) = s · min(c₁, ..., cₙ)
```

The conclusion is no more confident than the least confident premise, scaled by rule strength.

### 5.2 Conjunctive (Multiplication)
```
combine(c₁, ..., cₙ, s) = s · ∏ᵢ cᵢ
```

For rules where all premises must be true (logical AND). Each premise is an independent point of potential failure.

### 5.3 Disjunctive (Probabilistic OR)
```
combine(c₁, ..., cₙ, s) = s · (1 - ∏ᵢ (1 - cᵢ))
```

For rules where any premise suffices (logical OR).

### 5.4 Custom
Rules can specify custom propagation:
```
rule division:
  inputs: (x: Belief<Num>, y: Belief<Num>)
  output: Belief<Num>
  value: x.val / y.val
  confidence: min(x.conf, y.conf) · (1 - P(y.val ≈ 0))
  -- confidence decreases if y might be near zero
```

## 6. Defeat: Undercut and Rebut Edges

> **Key Finding (Thread 2.10, Session 12)**: Undercut and rebut require different mathematical treatment.

### 6.1 Undercutting Defeat

Undercut attacks the *inference link*, not the conclusion. Example: "The witness was drunk" undercuts testimony without providing evidence for any particular conclusion.

**Formula**: Multiplicative discounting
```
c' = c × (1 - defeat_strength)
```

**Properties**:
- Preserves [0,1] bounds without clamping
- Compositional: `undercut(undercut(c, d₁), d₂) = undercut(c, d₁ ⊕ d₂)`
- Aligns with Subjective Logic discounting
- Probabilistic interpretation: (1-d) is "survival probability" of the inference

**Lean formalization**:
```lean
def undercut (c d : Confidence) : Confidence :=
  ⟨c.val * (1 - d.val), by
    constructor
    · exact mul_nonneg c.property.1 (by linarith [d.property.2])
    · nlinarith [c.property.1, c.property.2, d.property.1, d.property.2]⟩

theorem undercut_zero (c : Confidence) : undercut c 0 = c
theorem undercut_one (c : Confidence) : (undercut c 1).val = 0
```

### 6.2 Rebutting Defeat

Rebut attacks the *conclusion* directly with counter-evidence. Example: Evidence for "X is guilty" vs evidence for "X is innocent".

**Formula**: Probabilistic comparison (normalized)
```
c' = c_for / (c_for + c_against)
```

**Properties**:
- Treats for/against symmetrically
- Result is naturally in [0,1]
- Equal arguments → 0.5 (maximal uncertainty)
- Overwhelming argument → approaches 1 or 0
- Intuitive "market share" interpretation

**Lean formalization**:
```lean
def rebut (c_for c_against : Confidence) : Confidence :=
  if h : c_for.val + c_against.val = 0
  then ⟨0.5, by norm_num, by norm_num⟩  -- maximal uncertainty when no evidence
  else ⟨c_for.val / (c_for.val + c_against.val), ⟨
    div_nonneg c_for.property.1 (by linarith),
    div_le_one_of_le (by linarith) (by linarith)⟩⟩
```

### 6.3 Multiple Defeaters

**Multiple undercuts**: Aggregate defeater strengths using ⊕, then apply once:
```
d_combined = d₁ ⊕ d₂ ⊕ ... ⊕ dₙ
c' = c × (1 - d_combined)
```

**Multiple rebuts**: Use weighted pool:
```
c' = Σ(pro_arguments) / Σ(all_arguments)
```

### 6.4 Mixed Defeat: Evaluation Order

When both undercuts and rebuts are present:
1. First, apply undercuts to weaken the base inference
2. Then, compare weakened belief against rebuts

```
c_weakened = c × ∏ᵢ (1 - undercut_i)
c_final = rebut(c_weakened, c_against)
```

This order is principled: undercuts weaken the inference itself, then the weakened claim competes against counter-evidence.

## 7. Aggregation: Independent Evidence

> **Key Finding (Thread 2.11, Session 19)**: Independent lines of evidence combine via probabilistic OR (⊕).

### 7.1 When to Aggregate

**Aggregation** (use ⊕) when:
- Multiple independent sources
- Each source alone supports the conclusion
- Sources don't depend on each other

**Derivation** (use ×) when:
- Sequential inference chain
- Each step depends on the previous
- Modus ponens, transitive closure, etc.

### 7.2 Independent Aggregation Formula

```
aggregate(c₁, c₂, ..., cₙ) = 1 - ∏ᵢ(1 - cᵢ)
                           = c₁ ⊕ c₂ ⊕ ... ⊕ cₙ
```

**Interpretation**: Combined confidence is the probability that at least one piece of evidence successfully establishes the conclusion ("survival of doubt").

**Properties**:
- Boundedness: aggregate ∈ [0,1]
- Monotonicity: Adding evidence never decreases confidence
- Commutativity and associativity
- Diminishing returns: Each additional piece contributes less
- Convergence: Approaches 1 as evidence accumulates

### 7.3 Correlated Evidence

> **Key Finding (Thread 2.13, Session 20)**: Naively applying ⊕ to correlated evidence overcounts.

When evidence sources share common causes, methodologies, or information sources, they are **correlated** and should not be treated as independent.

**Dependency-adjusted aggregation**:
```
aggregate_δ(c₁, c₂) = (1-δ)(c₁ ⊕ c₂) + δ(c₁ + c₂)/2
```

where δ ∈ [0,1] is the dependency parameter:
- δ = 0: fully independent → use ⊕
- δ = 1: fully dependent → use average
- 0 < δ < 1: interpolate

**Dependency estimation from provenance**:
```lean
def estimateDependency (j1 j2 : JustificationRef) (graph : JustificationGraph) : Float :=
  let ancestors1 := graph.ancestors j1
  let ancestors2 := graph.ancestors j2
  let shared := ancestors1 ∩ ancestors2
  let total := ancestors1 ∪ ancestors2
  if total.isEmpty then 0.0  -- No shared ancestry → independent
  else (shared.size.toFloat / total.size.toFloat)  -- Jaccard-like similarity
```

**Conservative default**: When dependency is unknown, assume δ ≈ 0.3 rather than 0.

### 7.4 The Aggregate Node

```lean
inductive CombinationRule where
  | independent              -- Use ⊕
  | dependent                -- Use average
  | correlated : Float → CombinationRule  -- Interpolate with given δ

def aggregateConfidence (confs : List Confidence) (rule : CombinationRule) : Confidence :=
  match rule with
  | .independent => probOr confs  -- 1 - ∏(1-cᵢ)
  | .dependent => average confs   -- (Σcᵢ)/n
  | .correlated δ => interpolate (probOr confs) (average confs) δ
```

## 8. DAG Evaluation Algorithm

To evaluate a belief's final confidence in the DAG:

```
function evaluateConfidence(node):
  if node is axiom:
    return node.base_confidence

  # Gather all edges by type
  supports = [e for e in node.edges if e.type == Support]
  undercuts = [e for e in node.edges if e.type == Undercut]
  rebuts = [e for e in node.edges if e.type == Rebut]

  # Step 1: Combine supports (multiplicative, aggregative, etc.)
  c_base = combineSupports(supports, node.combineRule)

  # Step 2: Apply undercuts (multiplicative discounting)
  for u in undercuts:
    defeat_strength = evaluateConfidence(u.target)
    c_base = c_base × (1 - defeat_strength)

  # Step 3: Apply rebuts (probabilistic comparison)
  if rebuts:
    c_against = aggregate([evaluateConfidence(r.target) for r in rebuts])
    return c_base / (c_base + c_against)
  else:
    return c_base
```

## 9. Non-Deductive Justification

> **Key Finding (Thread 2, Session 9)**: Non-deductive reasoning doesn't break the DAG structure, but requires new constructors with specific confidence propagation rules.

### 9.1 Abduction (Inference to Best Explanation)

```
Observation: The lawn is wet.
Best explanation: It rained last night.
Conclusion: belief("it rained last night", 0.7, ...)
```

**Structure**:
```lean
structure AbductionData where
  observation : JustificationEdge       -- What we're explaining
  hypotheses : List JustificationEdge   -- Candidate explanations
  selected : Nat                         -- Index of chosen hypothesis
  selectionReason : SelectionReason      -- Why this hypothesis is best
```

**Confidence propagation**: Based on:
- Confidence in observation
- How well hypothesis explains observation
- Prior plausibility of hypothesis
- Lack of better alternatives

```
c_abduction = c_observation × explanatory_strength × prior_plausibility
```

### 9.2 Analogy

```
Known: A has property P (confidence 0.95)
Known: B is similar to A (confidence 0.80)
Inferred: B has property P (confidence ???)
```

**Structure**:
```lean
structure AnalogyData where
  source : JustificationEdge        -- Known case
  similarity : JustificationEdge    -- Similarity measure
  transferPrinciple : TransferPrinciple  -- Why property transfers
```

**Confidence propagation**: Similarity typically caps rather than multiplies:
```
c_analogy = min(c_source, c_similarity) × transfer_factor
```

### 9.3 Induction

```
Observed: swan_1 is white, swan_2 is white, ..., swan_100 is white
Inferred: All swans are white (confidence 0.8)
```

**Structure**:
```lean
structure InductionData where
  instances : List JustificationEdge  -- Observed cases
  inductiveRule : InductiveRule       -- Type of generalization
  sampleSize : Nat                     -- Number of observations
```

**Confidence propagation**: Based on:
- Number of observations
- Diversity of observations
- Prior knowledge of exceptions

```
c_induction = f(sample_size, diversity, avg_instance_confidence)
```

where f is typically sublinear (many observations needed for high confidence).

## 10. Derivation Rules

### 10.1 Primitive Operations

```
───────────────────────────────────────────────── [D-Add]
b₁: Belief<Num>, b₂: Belief<Num> ⊢[+] Belief<Num>


───────────────────────────────────────────────── [D-Eq]
b₁: Belief<τ>, b₂: Belief<τ> ⊢[=] Belief<Bool>


b: Belief<List<τ>>
──────────────────────────────────────────────── [D-Head]
b ⊢[head] Belief<Option<τ>>
-- confidence may decrease if list might be empty
```

### 10.2 Logical Operations

```
b₁: Belief<Bool>, b₂: Belief<Bool>
─────────────────────────────────────────────── [D-And]
b₁, b₂ ⊢[∧] Belief<Bool>
  conf = c₁ · c₂

b₁: Belief<Bool>, b₂: Belief<Bool>
─────────────────────────────────────────────── [D-Or]
b₁, b₂ ⊢[∨] Belief<Bool>
  conf = c₁ + c₂ - c₁ · c₂
```

### 10.3 Conditional Derivation

```
b_cond: Belief<Bool>, b_then: Belief<τ>, b_else: Belief<τ>
──────────────────────────────────────────────────────────── [D-If]
b_cond, b_then, b_else ⊢[if] Belief<τ>
  value = if val(b_cond) then val(b_then) else val(b_else)
  conf = conf(b_cond) · conf(selected branch)
```

### 10.4 Function Application

```
b_f: Belief<τ₁ → τ₂>, b_x: Belief<τ₁>
──────────────────────────────────────────────────────────── [D-App]
b_f, b_x ⊢[apply] Belief<τ₂>
  value = (val(b_f))(val(b_x))
  conf = min(conf(b_f), conf(b_x))
```

## 11. Justification Algebra

Justifications form a term algebra with the extended constructors:

```
j ::= axiom                         -- primitive justification
    | rule(r, [e₁, ..., eₙ])        -- derived by rule with labeled edges
    | assumption(a)                 -- depends on assumption
    | choice(opts, c, reason)       -- result of decision
    | abduction(obs, hyps, sel, r)  -- inference to best explanation
    | analogy(src, sim, trans)      -- analogical reasoning
    | induction(instances, rule)    -- inductive generalization
    | aggregate(lines, combRule)    -- combined independent evidence
```

### 11.1 Operations

**Combination** (used in derivation):
```
j₁ ⊗ j₂ = rule(∧, [support(j₁), support(j₂)])
```

**Weakening** (when confidence drops):
```
weaken(j, reason) = weakened(j, reason)
```

**Querying** (extract assumptions):
```
assumptions(axiom) = ∅
assumptions(rule(r, edges)) = ⋃_{e ∈ edges} assumptions(target(e))
assumptions(assumption(a)) = {a}
assumptions(choice(opts, c, r)) = assumptions_from_criteria(c)
assumptions(aggregate(lines, _)) = ⋃_{l ∈ lines} assumptions(target(l))
```

## 12. Invalidation Propagation

### 12.1 Accumulation Rule
```
invalidation(derive b₁, ..., bₙ by r) = ⋃ᵢ inv(bᵢ) ∪ inv(r)
```

Derived beliefs inherit all invalidation conditions from premises, plus any rule-specific conditions.

### 12.2 Common Invalidation Conditions

```
inv_input_changed(source)       -- external input changed
inv_assumption_false(a)         -- assumption no longer holds
inv_confidence_below(c, thresh) -- confidence dropped too low
inv_constraint_violated(φ)      -- constraint no longer satisfied
inv_time_elapsed(duration)      -- time-based expiry
inv_defeat_added(defeater)      -- new defeating evidence arrived
```

### 12.3 Checking Invalidation

```
is_invalid(b, world_state) =
  ∃φ ∈ inv(b). evaluate(φ, world_state) = true
```

When a belief is invalid, it should be rederived or flagged for review.

### 12.4 DAG Invalidation

> **Key Finding (Thread 5, Session 16)**: Invalidation must handle shared nodes correctly.

When a node is invalidated:
1. **Identify affected nodes**: All transitive dependents in the DAG
2. **Topologically sort**: Process in dependency order
3. **Recompute**: Recalculate confidence bottom-up
4. **Reinstatement**: If a defeater is invalidated, the defeated belief may be reinstated

**Locality theorem**: Changes only affect transitive dependents; unrelated parts of the DAG remain unchanged.

## 13. Derivation vs. Computation

| Aspect | Traditional | CLAIR Derivation |
|--------|-------------|------------------|
| Input | Values | Beliefs |
| Output | Value | Belief |
| Trace | Discarded | Preserved (DAG) |
| Confidence | N/A | Propagated |
| Defeat | N/A | Supported |
| Invalidation | N/A | Accumulated |
| Reversibility | One-way | Queryable |
| Sharing | Implicit | Explicit (hash-consed) |

## 14. Example: Full DAG Derivation

```
-- Input beliefs
let testimony: Belief<String> =
  ⟨"suspect seen at 10pm", 0.85, source: witness, axiom, {}⟩

let alibi: Belief<String> =
  ⟨"suspect was elsewhere", 0.60, source: friend, axiom, {}⟩

let witness_drunk: Belief<Bool> =
  ⟨true, 0.70, source: bartender, axiom, {}⟩

-- Derivation with defeat
let testimony_weakened =
  undercut(testimony, by: witness_drunk)
  -- confidence: 0.85 × (1 - 0.70) = 0.255

let guilty_probability =
  rebut(testimony_weakened, against: alibi)
  -- confidence: 0.255 / (0.255 + 0.60) = 0.298
```

The DAG:
```
        guilty_probability
              |
          [rebut]
         /       \
        /         \
testimony_weakened  alibi
        |
    [undercut]
    /         \
testimony  witness_drunk
```

## 15. Optimization: Lazy DAG Evaluation

Full evaluation can be expensive. Optimizations:

1. **Hash-consing**: Share identical subtrees by content
2. **Memoization**: Cache confidence values at nodes
3. **Lazy evaluation**: Only compute when queried
4. **Incremental update**: On local change, only recompute affected subgraph
5. **Checkpointing**: Periodically snapshot, reconstruct from checkpoints

```
-- Compact representation with references
guilty.justification =
  rebut(
    undercut(ref("j:testimony"), ref("j:witness_drunk")),
    ref("j:alibi"))
```

## 16. Summary of Confidence Operations

| Context | Operation | Formula | When to Use |
|---------|-----------|---------|-------------|
| Sequential derivation | × (multiply) | c₁ × c₂ | Both premises needed |
| Conservative bound | min | min(c₁, c₂) | Pessimistic estimate |
| Independent evidence | ⊕ (prob OR) | c₁ + c₂ - c₁c₂ | Multiple supports |
| Correlated evidence | aggregate_δ | (1-δ)(c₁⊕c₂) + δ·avg | Shared provenance |
| Undercutting defeat | undercut | c × (1-d) | Attack on inference |
| Rebutting defeat | rebut | c/(c+d) | Counter-evidence |

## 17. References

### Prior Art Surveyed

- **Pollock (1987)**: Defeaters (rebutting vs undercutting)
- **Doyle (1979)**: JTMS with IN/OUT-lists
- **de Kleer (1986)**: ATMS with assumption environments
- **Artemov (2001)**: Justification Logic
- **Jøsang (2016)**: Subjective Logic fusion operators
- **Toulmin (1958)**: Argument model with rebuttals
- **Dung (1995)**: Abstract argumentation frameworks

### CLAIR Exploration Threads

- Thread 2: Justification Structure (Session 9)
- Thread 2.10: Defeat Confidence (Session 12)
- Thread 2.11: Aggregation (Session 19)
- Thread 2.12: Reinstatement (Session 18)
- Thread 2.13: Correlated Evidence (Session 20)
- Thread 5: Belief Revision (Session 16)
- Thread 8: Formal Verification (Sessions 10-31)
