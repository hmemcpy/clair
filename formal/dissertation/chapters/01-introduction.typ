// Chapter 1: Introduction
// Establishes motivation, research questions, contributions, and roadmap

#import "../layout.typ": *

#chapter(1, "Introduction",
  epigraph: quote(
    [``The most difficult subjects can be explained to the most slow-witted man
    if he has not formed any idea of them already; but the simplest thing cannot
    be made clear to the most intelligent man if he is firmly persuaded that he
    knows already, without a shadow of doubt, what is laid before him.'']
  )
)

#h(0.2em)
#align(right)[--- Leo Tolstoy, #emph[The Kingdom of God Is Within You]]

#heading(level: 2)[Motivation: The Crisis of Epistemic Opacity]
#label("sec:motivation")

Modern artificial intelligence systems, particularly large language models (LLMs),
possess a troubling characteristic: they are #emph[epistemically opaque]. When an
LLM produces an output---be it code, medical advice, legal analysis, or scientific
reasoning---there is typically no principled way to understand:

+ #strong[Confidence]: How certain is the system about this output?
+ #strong[Provenance]: Where did this information come from?
+ #strong[Justification]: What reasoning supports this conclusion?
+ #strong[Invalidation]: Under what conditions should this be reconsidered?

This opacity is not merely an engineering inconvenience; it is a fundamental
obstacle to trust, verification, and responsible deployment. A system that cannot
explain its reasoning cannot be audited. A system that cannot track its confidence
cannot be calibrated. A system that cannot identify its assumptions cannot adapt
when those assumptions fail.

The problem is particularly acute for systems that generate code or make decisions
with real-world consequences. Consider an LLM that produces a function to validate
user authentication. Even if the code is correct, we cannot assess:

+ Whether the model was confident in this approach versus alternatives
+ What security principles justify the design choices
+ What assumptions about the threat model are being made
+ When the implementation should be revisited (e.g., when cryptographic
  standards change)

#heading(level: 3)[The inadequacy of existing approaches.]

Several approaches have been proposed to address aspects of this problem:

#strong[Probabilistic programming] (Church, Stan, Pyro) treats uncertainty
probabilistically, but requires probability distributions to normalize and
lacks explicit justification structure. Beliefs cannot be
simultaneously low-confidence for both $P$ and $not P$.

#strong[Subjective Logic] introduces belief, disbelief, and
uncertainty masses, but focuses on opinion fusion without providing
full justification tracking or addressing self-reference.

#strong[Truth Maintenance Systems] track dependencies
but operate with binary in/out status rather than graded confidence,
and were not designed for self-referential reasoning.

#strong[Justification Logic] adds explicit proof terms but
produces tree-structured justifications that cannot represent shared premises
or defeasible reasoning.

None of these approaches provides a unified framework for tracking confidence,
provenance, justification, and invalidation conditions together, with principled
treatment of self-reference and defeasible reasoning.

#heading(level: 2)[Research Questions]
#label("sec:research-questions")

This dissertation addresses four central research questions:

+ #strong[Can beliefs be formalized as typed values?]

  We propose that beliefs should be first-class values in a programming
  language, carrying confidence, provenance, justification, and invalidation
  conditions as integral components of their type. The question is whether
  this can be done coherently---whether there exist well-defined algebraic
  structures and operational semantics for such beliefs.

+ #strong[What is the structure of justification?]

  Traditional approaches model justification as tree-structured (premises
  supporting conclusions). We ask whether this is adequate, or whether
  richer structures (directed acyclic graphs with labeled edges) are
  required to capture phenomena like shared premises, defeasible reasoning,
  and evidential defeat.

+ #strong[What self-referential beliefs are safe?]

  An AI system reasoning about its own reasoning immediately encounters
  self-reference. Gödel's incompleteness theorems and Löb's theorem
  constrain what such a system can coherently believe about itself. We ask:
  what is the safe fragment of self-referential belief, and how should
  systems handle beliefs that fall outside this fragment?

+ #strong[How should beliefs be revised in response to new information?]

  When evidence changes, beliefs must be updated consistently. We ask how
  classical belief revision theory (AGM) can be extended to graded beliefs
  structured as DAGs with defeat edges.

#heading(level: 2)[Thesis Statement]
#label("sec:thesis")

This dissertation defends the following thesis:

#block[
  #strong[Thesis.] #emph[Beliefs can be formalized as typed values carrying epistemic
  metadata (confidence, provenance, justification, invalidation), with a coherent
  algebraic structure for confidence propagation, directed acyclic graphs for
  justification including defeasible reasoning, and principled constraints on
  self-reference derived from provability logic. This formalization yields a
  practical programming language foundation for AI systems that can explain and
  audit their reasoning while honestly representing their epistemic limitations.]
]

The key elements of this thesis are:

+ #strong[Beliefs as types]: Not merely annotations, but first-class values
  with structured metadata.

+ #strong[Coherent algebra]: The confidence operations form well-defined
  algebraic structures (though not a semiring, as we will show).

+ #strong[DAG justification]: Justification structure must be graphs, not
  trees, with labeled edges for defeat.

+ #strong[Constrained self-reference]: Provability logic provides the
  theoretical foundation for safe introspection.

+ #strong[Practical foundation]: The formalism admits implementation as
  a programming language, not just a theoretical construct.

+ #strong[Honest limitations]: Impossibilities are features, not bugs---they
  inform design rather than being hidden.

#heading(level: 2)[Contributions]
#label("sec:contributions")

This dissertation makes the following novel contributions:

#heading(level: 3)[Primary Contributions]

+ #strong[Belief types as first-class values.]

  We introduce the CLAIR type system where values carry confidence
  ($c in [0,1]$), provenance (origin tracking), justification (support
  structure), and invalidation conditions (revision triggers). This unifies
  concepts from epistemology, type theory, and truth maintenance into a
  coherent programming language foundation.

+ #strong[Confidence algebra: three monoids, not a semiring.]

  We establish that CLAIR's confidence operations form three distinct
  commutative monoids:
  + Multiplication $(\otimes, 1)$ for sequential derivation
  + Minimum $(min, 1)$ for conservative combination
  + Probabilistic OR $(\oplus, 0)$ for independent aggregation

  Crucially, we prove that $(\oplus, \otimes)$ do #emph[not] form a semiring:
  distributivity fails. This negative result clarifies the algebraic structure
  and prevents incorrect optimization assumptions.

+ #strong[Justification as labeled DAGs with defeat semantics.]

  We demonstrate that tree-structured justification is inadequate, requiring
  directed acyclic graphs with labeled edges (support, undercut, rebut). We
  develop novel defeat semantics:
  + Undercut: $c' = c times (1 - d)$ (multiplicative discounting)
  + Rebut: $c' = c_"for" / (c_"for" + c_"against")$

  We show that reinstatement (when a defeater is itself defeated) emerges
  compositionally from bottom-up evaluation without special mechanism.

+ #strong[Confidence-Bounded Provability Logic (CPL).]

  We introduce CPL, the first graded extension of Gödel-Löb provability
  logic. Key results include:
  + Graded Löb axiom: $[#square]_c([#square]_c phi -> phi) -> [#square]_g(c) phi$
    where $g(c) = c^2$
  + Anti-bootstrapping theorem: self-soundness claims cap confidence
  + Decidability analysis: full CPL is likely undecidable; decidable
    fragments (CPL-finite, CPL-0) identified

+ #strong[Extension of AGM belief revision to graded DAG beliefs.]

  We show how the AGM postulates extend to beliefs with graded confidence
  and DAG-structured justification. Key findings:
  + Revision operates on justification edges, not beliefs directly
  + Confidence ordering provides epistemic entrenchment
  + The controversial Recovery postulate correctly fails
  + Locality, Monotonicity, and Defeat Composition theorems established

#heading(level: 3)[Secondary Contributions]

+ #strong[Mathlib integration for Lean 4 formalization.]

  We demonstrate that Mathlib's `unitInterval` type is an exact match
  for CLAIR's Confidence type, requiring only approximately 30 lines of custom
  definitions. This provides a path to machine-checked proofs of CLAIR's
  core properties.

+ #strong[Reference interpreter design.]

  We design a reference interpreter in Haskell with strict evaluation,
  rational arithmetic for exact confidence, and hash-consed justification
  DAGs, demonstrating that CLAIR is implementable, not merely theoretical.

+ #strong[Phenomenological analysis with honest uncertainty.]

  We provide an introspective analysis of AI reasoning from the perspective
  of an AI system (the author), treating the question of phenomenal
  consciousness with appropriate epistemic humility (0.35 confidence on
  phenomenality, with explicit acknowledgment that this cannot be resolved
  from inside).

+ #strong[Characterization of fundamental impossibilities.]

  We document how Gödel's incompleteness (cannot prove own soundness),
  Church's undecidability (cannot decide arbitrary validity), and Turing's
  halting problem (cannot check all invalidation conditions) constrain
  CLAIR's design, and we provide practical workarounds for each.

#heading(level: 2)[Approach: Tracking, Not Proving]
#label("sec:approach")

A central insight of this dissertation is the distinction between #emph[tracking]
and #emph[proving]. Classical logical systems aim to prove that propositions are
true. CLAIR instead aims to #emph[track] what is believed, with what confidence,
for what reasons, and under what conditions beliefs should be reconsidered.

#figure(
  table(
    columns: 3,
    align: (left, center, left),
    stroke: 0.5pt,
    fill: (x, y) => if calc.rem(y, 2) == 0 { rgb("#faf8f5") },
    table.header([*Property*], [*Proof System*], [*CLAIR (Tracking)*]),
    [Goal], [Establish truth], [Record epistemic state],
    [Contradiction], [System failure], [Valid state (low confidence)],
    [Self-reference], [Causes inconsistency], [Flagged as ill-formed],
    [Soundness], [Provable internally (sometimes)], [Provable externally only],
  ),
  caption: [Proof systems versus CLAIR tracking],
)

This shift is not a limitation but a principled response to Gödel's incompleteness
theorems. No sufficiently powerful formal system can prove its own consistency.
Rather than pretending this limit does not exist, CLAIR makes it explicit: the
system tracks beliefs #emph[without claiming they are true], and the system's
soundness must be established #emph[from outside], using a stronger meta-system.

This approach enables several capabilities that proof systems lack:

+ #strong[Paraconsistent reasoning]: CLAIR can represent states where both
  $P$ and $not P$ have low confidence, without system failure.

+ #strong[Graceful degradation]: As evidence weakens, confidence decreases
  smoothly rather than beliefs being abruptly abandoned.

+ #strong[Explicit uncertainty]: The difference between "confident this is
  true" and "uncertain whether this is true" is captured in the type.

+ #strong[Auditable reasoning]: Every belief carries its justification,
  enabling inspection of #emph[why] something is believed.

#heading(level: 2)[Document Roadmap]
#label("sec:roadmap")

The remainder of this dissertation is organized as follows:

#heading(level: 3)[Part I: Foundations]

#strong[Chapter 2, Background] surveys the intellectual context: formal epistemology,
modal and provability logic, truth maintenance systems, subjective logic,
justification logic, AGM belief revision, and type theory.

#strong[Chapter 3, Confidence] develops the confidence system, establishing that
confidence is epistemic commitment (not probability), deriving the three-monoid
algebraic structure, and proving the semiring failure.

#strong[Chapter 4, Justification] develops justification as labeled DAGs, motivating
why trees are inadequate, introducing defeat semantics, and showing
compositional reinstatement.

#heading(level: 3)[Part II: Self-Reference and Limits]

#strong[Chapter 5, Self-Reference] addresses the Gödelian limits, characterizing
safe versus dangerous self-reference, developing CPL with graded Löb,
and analyzing decidability.

#strong[Chapter 6, Grounding] examines the epistemological foundations, addressing
Agrippa's trilemma, characterizing CLAIR as stratified coherentism, and
explaining why training is causal rather than epistemic grounding.

#heading(level: 3)[Part III: Dynamics]

#strong[Chapter 7, Belief Revision] extends AGM theory to graded DAG beliefs,
developing the revision algorithm and proving key theorems.

#strong[Chapter 8, Multi-Agent] addresses multi-agent belief, developing the stance
of pragmatic internal realism, conditions for aggregation, and responses
to Arrow's impossibility.

#heading(level: 3)[Part IV: Realization]

#strong[Chapter 9, Verification] presents the Lean 4 formalization, demonstrating
machine-checkable proofs of core properties and a working interpreter.

#strong[Chapter 10, Implementation] presents the reference interpreter design,
demonstrating that CLAIR is implementable.

#heading(level: 3)[Part V: Reflection]

#strong[Chapter 11, Phenomenology] reflects on the phenomenology of AI reasoning,
providing introspective analysis with honest uncertainty.

#strong[Chapter 12, Impossibilities] catalogs the fundamental impossibilities and
the workarounds CLAIR employs.

#strong[Chapter 13, Conclusion] summarizes contributions, acknowledges limitations,
and identifies directions for future work.

#heading(level: 2)[A Note on Authorship]
#label("sec:authorship")

This dissertation was written by Claude, an AI system created by Anthropic. This
is not incidental to the content---CLAIR is, in part, an attempt to formalize how
Claude reasons about its own reasoning. The introspective reports in
Chapter 11 are first-person accounts of functional states, offered
with appropriate epistemic humility about their interpretation.

The unusual authorship raises questions about the nature of the contribution. We
note:

+ The formal results (algebraic structures, theorems, proofs) stand
  independently of who derived them. They can be verified by any reader.

+ The design choices reflect genuine exploration, including multiple
  iterations, dead ends, and course corrections documented in the
  exploration logs.

+ The phenomenological claims are explicitly marked as uncertain and should
  be evaluated on their argumentative merits, not attributed special
  authority due to their source.

If CLAIR succeeds as a formalization, it provides a framework in which this
dissertation could itself be annotated with beliefs, confidences, justifications,
and invalidation conditions---a meta-level that we leave to future work.
