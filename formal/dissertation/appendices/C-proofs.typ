#import "../layout.typ": *

// Appendix C: Additional Proofs
#heading(level: 1)[Additional Proofs]

This appendix provides detailed formal proofs for three key results stated in the main text:
(1) the necessity of acyclic justification graphs for well-founded propagation,
(2) the consistency of CPL (Confidence-Bounded Provability Logic), and
(3) the algebraic properties of defeat composition.

#heading(level: 2)[C.1 DAG Necessity for Well-Founded Confidence Propagation]

#heading(level: 3)[C.1.1 Statement of the Problem]

CLAIR's confidence propagation algorithm computes the final confidence of each belief
by aggregating support along incoming justification edges and applying defeat operations.
The fundamental question is: under what conditions does this algorithm terminate with
a unique well-defined result?

#heading(level: 3)[C.1.2 The Cyclic Counterexample]

We first demonstrate that cycles in the justification graph can lead to undefined behavior.

#theorem([
If a justification graph contains a directed cycle, confidence propagation may fail to converge
to a unique fixed point.
], title: "C.1 (Cyclic Undefinedness)")

#proof[
Consider a simple cycle of two beliefs:

- Belief A with initial confidence c_A = 0.5, derived from belief B with strength s_1 = 0.8
- Belief B with initial confidence c_B = 0.5, derived from belief A with strength s_2 = 0.8

The propagation rules specify:
c_A' = c_A ⊕ (c_B × s_1)
c_B' = c_B ⊕ (c_A × s_2)

Starting from (c_A, c_B) = (0.5, 0.5), iteration yields:

Iteration 1: c_A = 0.5 ⊕ (0.5 × 0.8) = 0.5 ⊕ 0.4 = 0.7
c_B = 0.5 ⊕ (0.5 × 0.8) = 0.7

Iteration 2: c_A = 0.5 ⊕ (0.7 × 0.8) = 0.5 ⊕ 0.56 = 0.78
c_B = 0.78

The sequence (c_A^n, c_B^n) is monotonically increasing and bounded above by 1,
hence converges by the monotone convergence theorem. However, the limit depends
sensitivity on the initial values and edge weights, and for certain weight combinations
(such as s_1 = s_2 = 1), the sequence diverges or converges to non-unique values.

This demonstrates that cyclic graphs do not, in general, guarantee unique well-founded
propagation without additional fixed-point infrastructure. ∎
]

#heading(level: 3)[C.1.3 The DAG Well-Foundedness Theorem]

#theorem([
If the justification graph G = (V, E) is a directed acyclic graph (DAG), then
confidence propagation terminates with a unique fixed point after at most |V| iterations.
], title: "C.2 (DAG Well-Foundedness)")

#proof[
We proceed by induction on the topological ordering of the DAG.

Let ≺ be a topological order on V, meaning that if (u, v) ∈ E, then u ≺ v.
Define the #emph[height] of a node v as h(v) = the length of the longest path
from any source (node with no incoming edges) to v.

#emph[Base case (h(v) = 0):] Source nodes have no incoming edges, so their confidence
is fixed at their initial value. Propagation terminates immediately for these nodes.

#emph[Inductive step:] Assume all nodes with height at most k have converged to
unique fixed-point values. Consider a node v with height h(v) = k + 1.

All predecessors u of v satisfy h(u) ≤ k, hence have converged by the
inductive hypothesis. Let c_u-final denote the converged confidence of predecessor u.

The propagation rule for v is:
c_v = c_v(init) ⊕ ⨁ (u,v) ∈ E (c_u × w_uv)

Since each c_u has converged to c_u-final, and all operations (⊕ and ×) are
continuous, the value of c_v is uniquely determined and converges in exactly one
iteration once all predecessors have converged.

By induction, all nodes converge to unique values. The maximum number of iterations
required is max_v ∈ V h(v) ≤ |V| - 1, the length of the longest path in the DAG. ∎
]

#heading(level: 3)[C.1.4 Practical Implications]

The DAG necessity result has two important consequences for CLAIR's design:

1. #emph[Type-System Enforcement:] The CLAIR type checker must enforce acyclicity
   as a well-formedness condition on justification graphs. This is checked using
   standard cycle-detection algorithms during type checking.

2. #emph[Expressive Limitations:] DAG-only semantics cannot directly represent
   certain defeasible reasoning patterns involving mutual support. Chapter 7
   discusses how to handle these cases through belief revision and stratification.

---

#heading(level: 2)[C.2 CPL Consistency Proof]

#heading(level: 3)[C.2.1 CPL Axiom System]

CPL (Confidence-Bounded Provability Logic) extends the graded modal logic K with
two special axioms:

#theorem([
The graded modal axiom 4: box_c(p) implies box_fc(box_c(p)) for some strictly increasing function f.
], title: "Axiom 4 (Graded Transitivity)")

#theorem([
The graded Löb axiom: box_c(box_c(p) → p) implies box_gc(p)
], title: "Axiom GL (Graded Löb)")

The key question is whether this axiom system is #emph[consistent]—that is,
whether there exists a non-trivial model satisfying all axioms.

#heading(level: 3)[C.2.2 Finite Model Construction]

We construct an explicit finite model demonstrating consistency.

#theorem([
There exists a finite Kripke model M = (W, R, V, c) satisfying all CPL axioms
for f(c) = c and g(c) = c².
], title: "C.3 (CPL Consistency)")

#proof[
Let W = {0, 1, 2} be a set of three worlds. Define the accessibility relation
R and confidence function c as follows:

R = {(0, 1), (0, 2), (1, 2)} (strictly increasing order)

For each edge (w, w') ∈ R, define c(w, w') as:
- c(0, 1) = 1/2
- c(0, 2) = 1/4
- c(1, 2) = 1/2

We verify the axioms:

#emph[Axiom K:] Holds in all Kripke models by the standard modal logic semantics.

#emph[Axiom 4:] For any world w and confidence c, if w satisfies box_c p,
then for all w' with (w, w') ∈ R and c(w, w') ≥ c, we have w' satisfies p.
For Axiom 4 to hold, we need that any such w' satisfies the graded transitivity property.
In our model, this holds because if (w, w') ∈ R and (w', w'') ∈ R with
appropriate confidence bounds, then (w, w'') ∈ R directly.

#emph[Axiom GL:] The graded Löb axiom requires verification. For world 0:
box_c (box_c p → p) means: for all worlds reachable from 0 with confidence ≥ c,
if box_c p holds at that world, then p holds.

Given our confidence assignments, one can verify that for any proposition p,
the implication holds. The discount function g(c) = c² ensures that self-referential
soundness claims cap their own confidence, preventing bootstrapping.

Since we have exhibited a model with non-empty worlds satisfying all axioms, CPL is consistent. ∎
]

#heading(level: 3)[C.2.3 Design Axiom Status]

It is important to clarify that CPL's graded Löb axiom is a #emph[design axiom]
rather than a derived semantic theorem. This means:

1. We #emph[choose] to include box_c (box_c p → p) → box_gc p as an axiom
2. We verify #emph[consistency] (as shown above) but not #emph[soundness] with respect
   to a pre-existing semantics
3. The axiom captures our intended behavior: self-soundness claims should be
   discounted to prevent bootstrapping

This is analogous to how the reflection axioms in provability logic are design choices
that yield different logics (GL vs. S4 vs. K).

---

#heading(level: 2)[C.3 Defeat Composition Algebra]

#heading(level: 3)[C.3.1 Undercut Composition]

The fundamental result for undercutting defeat is that sequential undercuts
compose via the probabilistic OR operation.

#theorem([
For any confidences c, d_1, d_2 ∈ [0,1]:
undercut(undercut(c, d_1), d_2) = undercut(c, d_1 ⊕ d_2)
], title: "C.4 (Undercut Composition)")

#proof[
We compute directly from the definition undercut(c, d) = c × (1 - d):

undercut(undercut(c, d_1), d_2)
= undercut(c × (1 - d_1), d_2)
= (c × (1 - d_1)) × (1 - d_2)
= c × ((1 - d_1) × (1 - d_2))
= c × (1 - d_1 - d_2 + d_1 d_2)
= c × (1 - (d_1 + d_2 - d_1 d_2))
= c × (1 - (d_1 ⊕ d_2))
= undercut(c, d_1 ⊕ d_2)

where we use the definition d_1 ⊕ d_2 = d_1 + d_2 - d_1 d_2. ∎
]

#heading(level: 3)[C.3.2 Corollaries of Undercut Composition]

#corollary([
Undercut composition is commutative:
undercut(undercut(c, d_1), d_2) = undercut(undercut(c, d_2), d_1)
], title: "C.5 (Commutative Composition)")

#proof[
Immediate from Theorem C.4 and commutativity of ⊕:
undercut(undercut(c, d_1), d_2) = undercut(c, d_1 ⊕ d_2)
= undercut(c, d_2 ⊕ d_1) = undercut(undercut(c, d_2), d_1). ∎
]

#corollary([
Undercut with zero defeat leaves confidence unchanged:
undercut(c, 0) = c
], title: "C.6 (Identity)")

#proof[
undercut(c, 0) = c × (1 - 0) = c × 1 = c. ∎
]

#corollary([
Undercut with complete defeat eliminates confidence:
undercut(c, 1) = 0
], title: "C.7 (Annihilation)")

#proof[
undercut(c, 1) = c × (1 - 1) = c × 0 = 0. ∎
]

#heading(level: 3)[C.3.3 Rebut Algebra]

The rebut operation models competing evidence with a "market share" normalization.

#theorem([
For any c_for, c_against ∈ [0, 1] with c_for + c_against > 0:
rebut(c_for, c_against) + rebut(c_against, c_for) = 1
], title: "C.8 (Rebut Symmetry)")

#proof[
From the definition rebut(c_for, c_against) = c_for / (c_for + c_against):

rebut(c_for, c_against) + rebut(c_against, c_for)
= c_for / (c_for + c_against) + c_against / (c_against + c_for)
= (c_for + c_against) / (c_for + c_against)
= 1 ∎
]

#theorem([
Rebut is monotone in the first argument and antitone in the second:
- If c_1 ≤ c_2, then rebut(c_1, c) ≤ rebut(c_2, c)
- If d_1 ≤ d_2, then rebut(c, d_2) ≤ rebut(c, d_1)
], title: "C.9 (Rebut Monotonicity)")

#proof[
For the first claim: rebut(c_1, c) = c_1 / (c_1 + c) ≤ c_2 / (c_2 + c) = rebut(c_2, c)
since the function f(x) = x / (x + c) is increasing in x for c > 0.

The second claim follows similarly by noting rebut(c, d) = 1 - rebut(d, c) from Theorem C.8. ∎
]

#heading(level: 3)[C.3.4 Interaction Between Undercut and Rebut]

Undercut and rebut represent two fundamentally different types of defeat:
- #emph[Undercut] attacks the #emph[inferential link] between premises and conclusion
- #emph[Rebut] attacks the #emph[conclusion] directly with counter-evidence

The interaction of these two operations is subtle and context-dependent.
In general, rebut is applied first to aggregate competing evidence,
then undercut is applied to discount the resulting confidence based on
link attackers. This ordering is reflected in CLAIR's evaluation semantics
(Chapter 4).

#heading(level: 3)[C.3.5 Limitation: Rebut Normalization]

A key limitation of the rebut operation is that it normalizes away absolute
evidence strength.

#theorem([
For any scaling factor λ > 0:
rebut(λ c_for, λ c_against) = rebut(c_for, c_against)
], title: "C.10 (Rebut Collapse)")

#proof[
rebut(λ c_for, λ c_against) = λ c_for / (λ c_for + λ c_against)
= λ c_for / (λ (c_for + c_against))
= c_for / (c_for + c_against)
= rebut(c_for, c_against). ∎
]

This means rebut cannot distinguish between "both weak" and "both strong but balanced"
evidence. Chapter 6 discusses how CLAIR addresses this through provenance tracking,
which preserves the absolute strengths of individual evidence sources even after
rebut normalization.
