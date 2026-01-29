#import "../layout.typ": *

// Chapter 4: Justification as Labeled DAGs
#heading(level: 1)[Justification as Labeled DAGs]

#align(center)[
  #set text(font: "Georgia", size: 10pt, style: "italic", fill: rgb("#666"))
  "An argument is not a proof. It is a reason for a belief---and reasons can be defeated."
  #h(0.3em)
  #align(right)[--- John L. Pollock, #emph[Defeasible Reasoning]]
]

This chapter develops the structural foundation of CLAIR: how beliefs connect through
justification. We show that trees are inadequate for justification structure and that
the correct model is a #emph[directed acyclic graph with labeled edges]. The labels
distinguish support from defeat, enabling defeasible reasoning where conclusions can
be withdrawn when new evidence undermines their justifications.

#heading(level: 2)[The Inadequacy of Trees]

#heading(level: 3)[The Shared Premise Problem]

Traditional approaches represent justification as trees: each conclusion has premises,
which themselves have premises, forming an inverted tree structure. This model is
elegant but insufficient.

Consider a simple computation that uses the same belief twice:

#block(fill: rgb("#f5f5f5"), inset: 8pt, radius: 4pt)[
  #set text(font: "Monaco", size: 9pt)
  let population = belief(1000000, 0.95, source: census)\n
  let sample_size = belief(1000, 0.90, source: survey)\n
  let ratio = derive population, sample_size by divide\n
  let inverse = derive sample_size, population by divide\n
  let product = derive ratio, inverse by multiply
]

In a tree representation, each belief appears multiple times as separate subtrees.
This creates three problems:

+ #strong[Space inefficiency]: Beliefs are copied rather than shared.
+ #strong[Invalidation complexity]: If a belief is invalidated, we must find and invalidate all copies.
+ #strong[Semantic confusion]: Are these the #emph[same] belief or #emph[different] beliefs that happen to be equal?

The correct representation is a DAG with explicit sharing, where each belief appears exactly once with multiple parents.

#theorem[
  #strong[DAG Necessity.]

  Any justification system that:
  1. Allows a belief to be used as a premise in multiple derivations
  2. Propagates invalidation correctly (removing a premise invalidates all conclusions)
  3. Maintains identity (the "same" belief is the same node)

  must represent justification as a DAG, not a tree.

  #proof[
    In a tree, each node has exactly one parent. If a belief is used in derivations of two different conclusions, it must appear as a child of both. But in a tree, a node cannot have two parents. Therefore, the belief must be duplicated, violating identity. A DAG allows multiple parents, resolving the contradiction.
  ]
]

#heading(level: 3)[Why Not Cycles?]

If we allow sharing, why not allow cycles? Coherentist epistemology suggests beliefs can mutually support each other. We reject cycles in justification for three reasons:

+ #strong[Bootstrap problem]: Circular justification allows confidence inflation with no external grounding.
+ #strong[Invalidation ambiguity]: If beliefs support each other circularly, invalidation semantics become ill-defined.
+ #strong[Well-foundedness]: The justification relation should be well-founded, with no infinite descending chains.

#block(fill: rgb("#fff8e7"), inset: 8pt, radius: 4pt)[
  #set text(size: 10pt)
  #strong[Note:] The theory/observation circularity example is better analyzed as two separate relations:
  + #strong[Evidential support] (tracked in justification): Observation provides evidence for theory.
  + #strong[Interpretive framework] (not part of justification): Theory provides framework for interpreting observation.
]

#heading(level: 2)[Labeled Edges for Defeat]

The DAG structure addresses sharing but not defeat. When evidence undermines a belief's justification, we need edges that carry negative, not positive, epistemic weight.

#heading(level: 3)[The Defeat Problem]

A #emph[defeater] is a belief that undermines confidence in another belief. Following Pollock (2001), we distinguish:

+ #strong[Undercutters]: Attack the inferential link, not the conclusion directly.
+ #strong[Rebutters]: Provide direct counter-evidence against the conclusion.

#definition[
  #strong[Edge Types.]

  A justification edge has one of three types:
  1. #strong[Support]: Positive evidence for the target.
  2. #strong[Undercut]: Attacks the inferential link to the target.
  3. #strong[Rebut]: Direct counter-evidence against the target.
]

#heading(level: 3)[Formal Definition]

#definition[
  #strong[Justification Graph.]

  A #strong[justification graph] is a tuple #emph[G = (N, E, r)] where:
  + #emph[N] is a finite set of #emph[justification nodes]
  + #emph[E subset.eq N times N times set("support", "undercut", "rebut")] is a set of labeled edges
  + #emph[r in N] is the root node

  subject to the constraint that the underlying unlabeled graph is acyclic.
]

#definition[
  #strong[Justification Node Types.]

  Each node has one of the following types:
  + #text[axiom]: Foundational belief (confidence = 1)
  + #text[rule] \ `(r, premises)`: Deductive rule application
  + #text[assumption] \ `(a)`: Temporary assumption for reasoning
  + #text[choice] \ `(options, criteria)`: Decision point
  + #text[abduction] \ `(obs, hypotheses, selected)`: Abductive inference
  + #text[analogy] \ `(source, similarity)`: Analogical reasoning
  + #text[induction] \ `(cases, rule)`: Inductive generalization
  + #text[aggregate] \ `(sources, combRule)`: Evidence aggregation
]

#heading(level: 3)[Well-Formedness Constraints]

A well-formed justification graph must satisfy explicit constraints to ensure
semantic coherence and computational tractability.

#definition[
  #strong[Acyclicity Constraint.]

  A justification graph must be acyclic: no path may exist from any node back to itself.
  This constraint applies specifically to support edges. Defeat edges may form cycles,
  which are resolved via fixed-point iteration (discussed below).
]

#definition[
  #strong[Well-Formed Justification Graph.]

  A justification graph is well-formed iff:
  1. The support structure is acyclic (no support cycles)
  2. Every non-axiom node has at least one incoming support edge
  3. Every node is reachable from the root in the underlying undirected graph

  Condition 1 ensures the support structure is well-founded. Condition 2 ensures
  no "floating" beliefs without justification. Condition 3 ensures the graph is connected.
]

#heading(level: 3)[DAG-Only vs Cyclic Choice]

CLAIR adopts a hybrid approach to cycles:

+ #strong[Support edges: DAG-only]. Cycles in evidential support are semantically
  prohibited because they enable bootstrapping and violate well-foundedness.
  The type checker enforces acyclicity for support edges at construction time.

+ #strong[Defeat edges: Fixed-point semantics]. Defeat cycles are permitted and
  resolved via fixed-point iteration. When defeat edges form cycles, confidence
  propagation requires solving a system of equations.

This design choice reflects the epistemic distinction between evidence for
(which must be well-founded) and attacks against (which can mutually undermine each other).

#heading(level: 3)[Fixed-Point Semantics for Cyclic Defeat]

When defeat edges form cycles, we compute confidences via iterative fixed-point finding.

#theorem[
  #strong[Fixed-Point Existence.]

  For any defeat graph with acyclic underlying support, a fixed point exists.

  #proof[
    The confidence update function maps the unit interval to itself and is continuous.
    By Brouwer's fixed point theorem, a continuous function from a compact convex
    set to itself has a fixed point.
  ]
]

#theorem[
  #strong[Fixed-Point Uniqueness.]

  If the maximum product of undercut strengths along any cycle is strictly less than 1,
  then the fixed point is unique and Kleene iteration converges to it.

  #proof[
    Under this condition, the update function is a contraction mapping.
    By the Banach fixed point theorem, a contraction has a unique fixed point
    and iteration converges to it.
  ]
]

#definition[
  #strong[Kleene Iteration.]

  Starting from initial confidences, repeatedly apply the update function until
  convergence. The sequence generated by repeated application is the Kleene iteration.
]

#example[
  #strong[Convergence for Typical Defeat Cycles.]

  Suppose two nodes mutually undercut with strength 0.5 each. The Lipschitz constant
  is 0.5 times 0.5 equals 0.25. Starting from initial confidence (1, 1):

  + After 1 iteration: error is at most 0.25 times initial error
  + After 5 iterations: error is at most 0.25^5 approximately 0.001 (0.1%)
  + After 10 iterations: error is at most 0.25^10 approximately 10^-6 (0.0001%)

  Rapid convergence is typical for well-formed defeat graphs.
]

#block[
  #emph[Practical Implication.]

  For CLAIR implementations, we recommend:
  + Enforce DAG structure for support edges via static type checking
  + Allow defeat cycles but limit undercut strengths to ensure contraction
  + Use Kleene iteration with convergence threshold 10^-6
  + Cache fixed-point solutions to avoid recomputation during updates
]

#heading(level: 2)[Confidence Propagation]

Given a justification graph, we compute the confidence of each node bottom-up.

#definition[
  #strong[Support Propagation.]

  For a node with children having confidences #emph[c_1, ..., c_k]:
  + + conf(axiom) = 1
  + conf(rule(r, children)) = s_r times product over children
  + conf(aggregate(children, independent)) = oplus over children

  where #emph[s_r] is the rule strength and #emph[oplus] is probabilistic OR.
]

#definition[
  #strong[Defeat Propagation.]

  Let #emph[c] be confidence from support edges, #emph[d_1, ..., d_m] be undercut strengths, and #emph[r_1, ..., r_n] be rebut strengths. Then:
  #emph[c' = rebut(undercut(c, oplus d_i), oplus r_j)]
]

#theorem[
  #strong[Propagation Termination.]

  The propagation algorithm terminates for any acyclic justification graph.

  #proof[
    The graph is acyclic by definition. Each recursive call moves to a node strictly earlier in topological order. Since the graph is finite, recursion terminates.
  ]
]

#heading(level: 2)[Reinstatement]

A fundamental phenomenon in defeasible reasoning is #emph[reinstatement]: when a defeater is itself defeated, the original belief recovers some confidence.

#theorem[
  #strong[Compositional Reinstatement.]

  Let #emph[A] have base confidence #emph[a], undercut by #emph[D] with confidence #emph[d], which is itself undercut by #emph[E] with confidence #emph[e]. Then:
  #emph[conf(A) = a times (1 - d times (1 - e))]

  The #emph[reinstatement boost] is #emph[Delta = a times d times e].

  #proof[
    Bottom-up evaluation gives: #emph[conf_eff(D) = d times (1 - e)], then #emph[conf(A) = a times (1 - conf_eff(D)) = a times (1 - d(1-e))].
  ]
]

#heading(level: 2)[Mutual Defeat]

When two arguments defeat each other, we have a defeat cycle. The fixed point analysis yields:

#theorem[
  #strong[Mutual Defeat Fixed Point.]

  If #emph[A] and #emph[B] mutually undercut with base confidences #emph[a] and #emph[b], the fixed point is:
  #emph[a_star = a(1-b) / (1 - ab)] and #emph[b_star = b(1-a) / (1 - ab)]

  #proof[
    At fixed point: #emph[a_star = a(1 - b_star)] and #emph[b_star = b(1 - a_star)].
    Solving gives the stated formulas.
  ]
]

#theorem[
  #strong[Fixed Point Existence.]

  For any defeat graph with acyclic underlying support, a fixed point exists.

  #proof[
    The confidence update function maps #emph[[0,1]^n] to itself and is continuous. By Brouwer's fixed point theorem, a fixed point exists.
  ]
]

#theorem[
  #strong[Uniqueness Condition.]

  If #emph[b_max times d_max < 1], the fixed point is unique and iteration converges.

  #proof[
    Under this condition, the update function is a contraction mapping. By the Banach fixed point theorem, there is a unique fixed point and iteration converges.
  ]
]

#heading(level: 2)[Correlated Evidence]

The aggregation formula #emph[c_1 oplus c_2] assumes independence. When evidence sources are correlated, this overcounts.

#definition[
  #strong[Dependency-Adjusted Aggregation.]

  For evidence with confidences #emph[c_1, c_2] and dependency #emph[delta in [0,1]]:
  #emph[aggregate_delta(c_1, c_2) = (1-delta)(c_1 oplus c_2) + delta times (c_1 + c_2) / 2]

  where #emph[delta = 0] means independent and #emph[delta = 1] means fully dependent.
]

#heading(level: 2)[Connection to Prior Art]

#heading(level: 3)[Truth Maintenance Systems]

JTMS (Doyle 1979) uses IN/OUT lists for dependency-directed backtracking. ATMS (de Kleer 1986) tracks multiple assumption sets.

#strong[CLAIR contribution]: Generalize TMS to graded confidence with the same dependency-directed architecture.

#heading(level: 3)[Argumentation Frameworks]

Dung's argumentation (Dung 1995) defines acceptance semantics. Gradual semantics (Amgoud et al. 2017) add numeric degrees.

#strong[CLAIR contribution]: Integrate argumentation's defeat semantics with type-theoretic justification.

#heading(level: 3)[Justification Logic]

Artemov's Justification Logic (Artemov 2001) adds explicit justification terms to modal logic.

#strong[CLAIR contribution]: Extend from tree-like justification terms to DAGs with labeled edges, supporting defeasible reasoning.

#heading(level: 2)[Conclusion]

This chapter established the structural foundation of CLAIR:

+ #strong[DAGs, not trees]: Shared premises require graph structure; explicit sharing enables correct invalidation.
+ #strong[Acyclic]: Cycles in evidential support violate well-foundedness; defeat cycles handled via fixed-point semantics.
+ #strong[Labeled edges]: Support, undercut, and rebut serve different epistemic roles.
+ #strong[Compositional reinstatement]: Defeaters being defeated automatically recovers confidence.
+ #strong[Correlated evidence]: Independence assumptions must be explicit; dependency adjustment prevents overcounting.

The justification DAG provides the structural substrate for CLAIR's beliefs.
The next chapter addresses a subtler challenge: how beliefs can safely refer to themselves.
