// Chapter 7: Belief Revision
// Extends AGM theory to graded, DAG-structured beliefs

#import "../layout.typ": *

#chapter(7, "Belief Revision")

#h(0.2em)
#align(right)[--- #emph[Carlos Alchourrón], #emph[Peter Gärdenfors], #emph[David Makinson]]

#heading(level: 2)[The Challenge of Revising Structured Beliefs]

Classical belief revision theory, formalized in the AGM (Alchourrón-Gärdenfors-Makinson)
framework, assumes beliefs are unstructured propositions in a deductively closed
belief set. CLAIR's richer structure---graded confidence, DAG-justification,
and invalidation conditions---requires a substantial extension of this theory.

This chapter presents #emph[Graded DAG Belief Revision] (GDBR), a framework
that extends AGM postulates to handle CLAIR's structured beliefs while preserving
the core rationality constraints.

#heading(level: 2)[Background: The AGM Framework]

The AGM framework characterizes rational belief change through three
operations:

+ #strong[Expansion]: Adding a new belief $P$ to the belief set $K$, denoted
  $K + P$
+ #strong[Contraction]: Removing a belief $P$ from the belief set $K$, denoted
  $K - P$
+ #strong[Revision]: Adding $P$ while maintaining consistency, denoted
  $K * P$

The AGM postulates impose rationality constraints on these operations. For
example, the #emph[success postulate] for revision requires that $P$ is in
$K * P$, while the #emph[consistency postulate] requires that $K * P$ is
consistent if $P$ is consistent with $K$.

#heading(level: 2)[Why AGM Doesn't Directly Apply]

CLAIR's beliefs differ from AGM's in three critical ways:

#heading(level: 3)[Graded confidence.]

In AGM, beliefs are either held or not held---a binary distinction. In CLAIR,
beliefs have graded confidence. This raises new questions: Should revision
affect only beliefs with confidence above a threshold? How should conflicting
beliefs at different confidence levels be resolved?

#heading(level: 3)[DAG-structured justification.]

In AGM, beliefs are related only through logical consequence. In CLAIR, beliefs
are connected through justification DAGs. Revising one belief may require
recomputing the status of beliefs that depend on it, potentially cascading
through large portions of the graph.

#heading(level: 3)[Invalidation conditions.]

In AGM, beliefs are only retracted through explicit contraction operations. In
CLAIR, beliefs have #emph[invalidation conditions] that specify circumstances
under which they should be reconsidered. When these conditions are triggered,
revision happens automatically---a form of #emph[epistemic reflex].

#heading(level: 2)[GDBR: Graded DAG Belief Revision]

Our framework extends AGM with three core postulates specific to CLAIR's
structure:

#heading(level: 3)[Confidence preservation.]

When a belief is revised, its new confidence should be a function of:
- The confidence assigned to the new evidence
- The confidence of the defeated belief (if any)
- The strength of the justification links

Formally:

$$ conf(b*e) = f(conf(e), conf(b), strength(justification(b))) $$

where $f$ is a monotonic function satisfying $f(1.0, c, s) = min(1.0, c + s)$.

#heading(level: 3)[Justification propagation.]

When belief $b$ is revised, all beliefs that justify $b$ must be reconsidered:

$$ forall b' . (b' justifies b) implies reconsider(b') $$

This propagation continues transitively through the justification graph,
creating a #emph[revision cascade]. To prevent unbounded cascades, CLAIR
implements #emph[revision bounds] that limit propagation depth.

#heading(level: 3)[Invalidation responsiveness.]

When a belief's invalidation condition is triggered, the belief enters a
#emph[quarantine state] with reduced confidence. The belief must be explicitly
revalidated before its confidence can be restored.

$$ triggered(invalidation(b)) implies conf(b) := conf(b) times penalty(b) $$

The penalty factor depends on the severity of the invalidation trigger and
the belief's historical reliability.

#heading(level: 2)[The GDBR Algorithm]

The revision algorithm proceeds in three phases:

#heading(level: 3)[Phase 1: Conflict detection.]

When new evidence $e$ arrives, identify all beliefs that conflict with $e$:

$$ conflicts(e) = \{b in beliefs mid b contradicts e\} $$

Conflicting beliefs are marked for potential retraction.

#heading(level: 3)[Phase 2: Confidence comparison.]

For each conflicting belief $b$, compare confidences:

+ If conf$(e)$ > conf$(b)$, schedule $b$ for retraction
+ If conf$(e)$ < conf$(b)$, reject $e$ (with confidence downgrade)
+ If conf$(e)$ approx conf$(b)$, enter #emph[arbitration state]

Arbitration invokes additional heuristics: source reliability, justification
depth, and recency of evidence.

#heading(level: 3)[Phase 3: Graph restructuring.]

After resolving conflicts, restructure the justification DAG:

+ Remove justification links to retracted beliefs
+ Recompute confidence for affected beliefs
+ Trigger invalidation conditions for beliefs affected by retraction

This phase continues until the graph reaches a #emph[revision-fixed point].

#heading(level: 2)[The Revision Fixed Point Theorem]

#theorem[
  The GDBR algorithm always terminates in a revision-fixed point---a state
  where no further revisions are triggered---provided that:
  1. The justification graph is finite
  2. Confidence values are drawn from a finite set
  3. Invalidation conditions are monotonic (cannot trigger repeatedly)
]

#proof[
  Termination follows from the well-foundedness of the revision ordering.
  Each revision either (a) reduces the confidence of some belief, (b) removes
  a justification link, or (c) invalidates a belief. Since there are finitely
  many beliefs, finitely many justification links, and confidence can only
  decrease finitely many times, the process must terminate. ∎
]

#heading(level: 2)[Special Cases and Extensions]

#heading(level: 3)[Defeater revision.]

Sometimes revision involves not contradicting a belief directly, but
defeating its justification. CLAIR handles this through #emph[link revision]:
the justification link itself is marked as defeated, and confidence propagates
accordingly.

#heading(level: 3)[Package revision.]

When a set of beliefs form a tightly connected cluster, it's often more
appropriate to revise them as a unit rather than individually. CLAIR supports
#emph[package revision] through the revise-group primitive:

```
revise-group({b1, b2, b3}, evidence_e)
```

This performs simultaneous revision while maintaining coherence constraints.

#heading(level: 3)[Iterated revision.]

In long-running systems, beliefs may be revised multiple times. CLAIR tracks
revision history to prevent #emph[revision oscillation]---cycles where beliefs
alternate between states. When oscillation is detected, the system enters a
#emph[reflective state] and requests external guidance.

#heading(level: 2)[Connection to Argumentation Theory]

The GDBR framework connects naturally to formal argumentation theory. Justification
DAGs can be viewed as argumentation frameworks, where beliefs are arguments and
justification links represent attack/support relationships.

Revision in CLAIR corresponds to #emph[argument change] in argumentation theory:
adding new arguments (evidence), removing arguments (retraction), and changing
argument strengths (confidence adjustment). Our framework extends Dung's
argumentation semantics to handle graded confidence and dynamic restructuring.

#heading(level: 2)[Summary]

Belief revision in CLAIR extends the classical AGM framework to handle graded
confidence, DAG-structured justification, and invalidation conditions. The
GDBR framework preserves AGM's core rationality constraints while providing
principled algorithms for revising complex belief structures.

The key innovations are:
- #strong[Confidence-preserving revision]: New evidence doesn't simply
  override old beliefs; it integrates with existing confidence structures
- #strong[Cascade-limited propagation]: Justification changes propagate but
  with bounded depth to prevent unbounded revision
- #strong[Invalidation-driven reflex]: Beliefs automatically enter quarantine
  when their invalidation conditions trigger

This approach enables CLAIR systems to maintain coherent belief states even
under dynamic, uncertain conditions while preserving the explanatory power
of explicit justification tracking.
