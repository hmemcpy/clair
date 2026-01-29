#import "../layout.typ": *

// Chapter 2: Background
#heading(level: 1)[Background]

#quote[
  "If I have seen further it is by standing on the shoulders of Giants."
]
— Isaac Newton, letter to Robert Hooke (1675)

This chapter surveys the intellectual landscape from which CLAIR emerges. We organize
the discussion around five major traditions: formal epistemology (see #label("sec:epistemology")),
modal and provability logic (see #label("sec:modal-logic")), truth maintenance and argumentation
systems (see #label("sec:tms-arg")), belief revision theory (see #label("sec:belief-revision-bg")), and
type-theoretic approaches to uncertainty (see #label("sec:type-theory-bg")). We conclude with
a synthesis (see #label("sec:synthesis")) identifying the gap CLAIR fills.

#heading(level: 2)[Related Work]

#heading(level: 3)[Formal Epistemology]
#label("sec:epistemology")

Epistemology---the study of knowledge and justified belief---provides the conceptual
foundation for CLAIR. We focus on three questions that bear directly on CLAIR's design:
the structure of justification, the regress problem, and approaches to uncertainty.

#heading(level: 4)[The Structure of Justification]
#label("subsec:justification-structure")

What does it mean for a belief to be justified? The classical answer involves giving
reasons. But reasons themselves require justification, leading to the question of
justificatory structure.

#strong[Foundationalism.] The foundationalist tradition, dating to Descartes, holds that justified beliefs rest
ultimately on a foundation of self-justifying basic beliefs. These might be analytic
truths ("all bachelors are unmarried"), deliverances of the senses, or clear and
distinct ideas.

BonJour's #emph[The Structure of Empirical Knowledge]
provides the most thorough recent defense and critique of foundationalism. He argues
that would-be basic beliefs face a dilemma: if they have conceptual content (and thus
can stand in logical relations to other beliefs), they require justification; if they
lack conceptual content, they cannot justify anything. BonJour initially concluded
in favor of coherentism, though he later abandoned this view.

#strong[Coherentism.] Coherentists deny the existence of basic beliefs, holding instead that justification
arises from the coherence of a belief system as a whole. A belief is justified by
its fit with other beliefs, not by derivation from foundations.

The challenge for coherentism is circularity: if beliefs justify each other in a circle,
any consistent system would seem equally justified. Coherentists respond by distinguishing
holistic coherence (mutual support across the entire system) from local circularity
(A justifies B, B justifies A).

#strong[Infinitism.] Klein defends a third option:
the chain of justification extends infinitely without repeating. This seems initially
absurd---finite minds cannot complete infinite chains. Klein's response distinguishes
#emph[propositional justification] (reasons are available) from #emph[doxastic justification]
(reasons are actually believed). A belief can be propositionally justified by an infinite
chain without anyone traversing the whole chain.

#strong[Implications for CLAIR.] CLAIR adopts what we call #emph[stratified coherentism]: a coherentist structure
with pragmatic foundations. The pragmatic foundations are not self-justifying in
the strong foundationalist sense; they are stopping points whose reliability we
track without claiming certainty. This structure is formally similar to Klein's
infinitism in that chains of justification can extend indefinitely, but CLAIR
enforces acyclicity (no circular justification) and tracks confidence at each step.

#heading(level: 4)[Agrippa's Trilemma]
#label("subsec:agrippa")

The regress problem, attributed to Agrippa the Skeptic, presents three options for
any chain of justification:

1. #strong[Dogmatism]: The chain stops at some unjustified starting point.
2. #strong[Infinite regress]: The chain continues forever.
3. #strong[Circularity]: The chain loops back on itself.

All three options seem problematic. Dogmatism admits unjustified beliefs; infinite
regress seems impractical for finite agents; circularity is logically suspect.

#strong[CLAIR's response.] CLAIR accepts pragmatic dogmatism (option 1), mitigated by three features:
- #strong[Fallibilism]: Foundational beliefs have confidence $< 1$; they are
  provisional, not certain.
- #strong[Transparency]: The lack of deeper justification is explicit in the
  justification DAG, not hidden.
- #strong[Reliability tracking]: We track the source of foundational beliefs
  (training, observation, assumption) and can update if reliability evidence emerges.

Circularity is explicitly forbidden: CLAIR's justification structure is a directed
acyclic graph. Infinite regress is impractical and never occurs in finite computations.

#heading(level: 4)[Probability vs. Epistemic Confidence]
#label("subsec:probability-vs-confidence")

Standard approaches to uncertain reasoning use probability theory. A probability
distribution over propositions assigns values in $[0,1]$ satisfying:
$
  P(top) = 1 $
$
  P(phi or psi) = P(phi) + P(psi) - P(phi and psi) $
$
  P(not phi) = 1 - P(phi)
$

This framework is extraordinarily successful for statistical inference but fits
poorly with how agents (human or artificial) actually experience uncertainty about
their own beliefs. Two key mismatches:

#strong[Normalization.] Probability requires $P(phi) + P(not phi) = 1$. But an agent might be uncertain
about both $phi$ and $not phi$---perhaps due to lack of information rather than
balanced evidence. When asked about an unfamiliar topic, the appropriate response
may be low confidence in #emph[both] the claim and its negation.

#strong[Paraconsistency.] In probability, $P(phi) > 0.5$ and $P(not phi) > 0.5$ is impossible. But agents
some× find themselves with evidence for both $phi$ and $not phi$, without
immediately resolving the contradiction. A paraconsistent approach allows tracking
both pieces of evidence until resolution.

#strong[Subjective Logic.] Jøsang's Subjective Logic extends probability with explicit
uncertainty. An opinion $omega = (b, d, u, a)$ consists of:
- $b$: belief mass (evidence for)
- $d$: disbelief mass (evidence against)
- $u$: uncertainty mass (lack of evidence)
- $a$: base rate (prior probability)

with constraint $b + d + u = 1$. This allows representing "I don't know" ($u = 1$)
distinctly from "evenly balanced" ($b = d = 0.5, u = 0$).

#strong[CLAIR's approach.] CLAIR's confidence is conceptually closer to Subjective Logic than to probability,
but simpler: a single value $c in [0,1]$ representing epistemic commitment, without
the $b/d/u$ decomposition. The key departures from probability are:
- No normalization: $cal("conf")(phi) + cal("conf")(not phi)$ need not equal 1.
- $c = 0.5$ represents maximal uncertainty, not equal evidence.
- Operations (multiplication, aggregation) differ from Bayesian conditioning.

#heading(level: 3)[Modal and Provability Logic]
#label("sec:modal-logic")

Modal logic studies necessity ($square$) and possibility ($diamond$). Epistemic logic
interprets $square phi$ as "the agent knows $phi$" or "the agent believes $phi$."
Provability logic interprets $square phi$ as "$phi$ is provable" in a formal system.

#heading(level: 4)[Epistemic Logic]
#label("subsec:epistemic-logic")

Hintikka pioneered epistemic logic with the operator
$K phi$ ("the agent knows $phi$"). Standard systems include:

- #strong[K (Distribution)]: $K(phi -> psi) -> (K phi -> K psi)$
- #strong[T (Veridicality)]: $K phi -> phi$
- #strong[4 (Positive Introspection)]: $K phi -> K K phi$
- #strong[5 (Negative Introspection)]: $not K phi -> K not K phi$

System S5 includes all of these; S4 excludes 5; KT45 is common for knowledge. For
belief (which can be mistaken), T is typically dropped.

#strong[Limitations for CLAIR.] Standard epistemic logic is binary: either the agent knows/believes $phi$ or not.
There is no representation of degrees of belief. Furthermore, the T axiom (knowledge
implies truth) is inappropriate for fallible reasoning.

#heading(level: 4)[Provability Logic]
#label("subsec:provability-logic")

Provability logic, systematized by Boolos, interprets
$square phi$ as "$phi$ is provable in Peano Arithmetic" (or another formal system).
The central system is GL (Gödel-Löb logic), with axioms:

- #strong[K (Distribution)]: $square(phi -> psi) -> (square phi -> square psi)$
- #strong[4 (Positive Introspection)]: $square phi -> square square phi$
- #strong[L (Löb's Axiom)]: $square(square phi -> phi) -> square phi$

Notably, GL omits:
- T ($square phi -> phi$): Provability does not imply truth. A system can prove
  false statements if inconsistent.
- 5 (Negative Introspection): Unprovability is not always recognizable.

#strong[Löb's Theorem.] Löb's axiom (L) captures a profound limitation. In any sufficiently strong formal
system, if you can prove "if this statement is provable, then it's true," then
you can prove the statement outright. Formally:
$
  ⊢ square(square phi -> phi) -> square phi
$

A corollary: no consistent system can prove its own soundness (that $square phi -> phi$
holds for all $phi$). If it could, Löb's axiom would yield proofs of everything.

#strong[Semantics.] GL is sound and complete for Kripke frames that are #emph[transitive] and #emph[converse
well-founded] (no infinite ascending chains $w_1 R w_2 R w_3 diff$). Intuitively,
every "higher" world is closer to $omega$-consistency.

#strong[Relevance to CLAIR.] CLAIR's approach to self-reference is directly inspired by GL. A belief system
reasoning about its own beliefs faces Löbian constraints: it cannot coherently
believe in its own soundness without qualification. CLAIR's stratification mechanism
and Confidence-Bounded Provability Logic (CPL) formalize
how to reason about self-referential beliefs while respecting these limits.

#heading(level: 4)[Graded and Fuzzy Modal Logics]
#label("subsec:graded-modal")

Several traditions extend modal logic to graded settings:

#strong[Graded modalities.] De Rijke and Fine introduce operators
$square_n$ meaning "at least $n$ accessible worlds satisfy $phi$." This is not
about truth degrees but about counting accessible worlds.

#strong[Fuzzy modal logic.] Godo, Esteva, and colleagues develop modal logics
over many-valued semantics (Gödel, Łukasiewicz, Product). The accessibility
relation $R : W × W -> [0,1]$ assigns degrees, and:
$
  V_w(square phi) = inf_(w') max(1 - R(w,w'), V_(w')(phi))
$

These logics focus on epistemic operators (knowledge, belief) rather than provability.

#strong[The gap CLAIR fills.] Despite extensive work on fuzzy/graded epistemic logic, there is no prior work combining:
1. Graded truth values in $[0,1]$
2. Provability-style semantics (transitive, converse well-founded frames)
3. Löb's axiom or its graded analog

CLAIR's CPL fills this gap, introducing a graded Löb
axiom with a discount function that prevents confidence bootstrapping.

#heading(level: 3)[Truth Maintenance and Argumentation]
#label("sec:tms-arg")

Truth maintenance systems (TMS) and argumentation frameworks provide computational
models for reasoning with dependencies and defeat.

#heading(level: 4)[Justification-based TMS]
#label("subsec:jtms")

Doyle's JTMS tracks why beliefs are held. Each node (belief)
has a justification:
- #strong[IN-list]: nodes that must be believed for this belief to be believed
- #strong[OUT-list]: nodes that must #emph[not] be believed

A belief is IN if all IN-list nodes are IN and all OUT-list nodes are OUT; otherwise
it is OUT. When a node's status changes, dependencies propagate.

#example[
  Node: use-hs256
  Justification: (IN: [stateless-req, secret-available], OUT: [multi-service])
]
The belief `use-hs256` is IN <-> `stateless-req` and `secret-available`
are IN and `multi-service` is OUT.

#strong[Limitations.] JTMS is binary: beliefs are either IN or OUT, with no gradation. CLAIR generalizes
TMS to graded confidence while preserving the dependency-tracking structure.

#heading(level: 4)[Assumption-based TMS]
#label("subsec:atms")

De Kleer's ATMS tracks multiple consistent states
simultaneously. Instead of labeling nodes IN/OUT, each node is labeled with
#emph[environments]---sets of assumptions under which it holds.

#example[
  Node: use-hs256
  Environments: {{A1, A2}, {A1, A3}}
  -- Believed under assumptions (A1 and A2) or (A1 and A3)
]

ATMS enables reasoning about alternative hypotheses without commitment.

#strong[Relevance to CLAIR.] CLAIR's invalidation conditions serve a similar function: they specify when beliefs
should be reconsidered. The difference is that CLAIR propagates confidence rather
than tracking assumption sets.

#heading(level: 4)[Argumentation Frameworks]
#label("subsec:argumentation")

Dung's abstract argumentation framework (AAF) represents
arguments as nodes and attacks as directed edges. Various semantics define which
arguments are acceptable:
- #strong[Grounded extension]: Unique, includes only unattacked arguments and
  those defended by them.
- #strong[Preferred extension]: Maximal admissible sets.

#strong[Gradual semantics.] Amgoud, Ben-Naim, and others extend
AAF with weighted arguments and continuous acceptability:
$
  cal("strength")(a) = (w(a))/(1 + sum_(b " attacks" a) cal("strength")(b))
$

#strong[Relevance to CLAIR.] CLAIR's defeat semantics draws on gradual argumentation. Our undercut formula
$c' = c × (1 - d)$ and rebut formula $c' = c_(cal("for")) / (c_(cal("for")) + c_(cal("against")))$
are novel contributions that compose with the confidence algebra.

#heading(level: 4)[Pollock's Defeaters]
#label("subsec:pollock")

Pollock distinguishes two types
of defeaters:
- #strong[Rebutting defeaters] attack the conclusion directly with contrary evidence.
- #strong[Undercutting defeaters] attack the inference without attacking the conclusion.

Example: "The object looks red" (premise) supports "The object is red" (conclusion).
- Rebutting: "I have testimony that the object is blue."
- Undercutting: "The room has red lighting."

#strong[Relevance to CLAIR.] CLAIR adopts Pollock's distinction. Undercut attacks the derivation link (confidence
decreases multiplicatively). Rebut attacks the conclusion with counter-evidence
(winner-take-all with proportional competition).

#heading(level: 3)[Belief Revision]
#label("sec:belief-revision-bg")

How should beliefs change in response to new information? The AGM framework provides
the canonical answer.

#heading(level: 4)[The AGM Framework]
#label("subsec:agm")

Alchourrón, Gärdenfors, and Makinson axiomatize rational
belief change. A belief set $K$ is a deductively closed set of sentences. Three
operations are defined:
- #strong[Expansion $K + phi$]: Add $phi$ and close under deduction.
- #strong[Contraction $K - phi$]: Remove $phi$ minimally.
- #strong[Revision $K * phi$]: Add $phi$, possibly removing conflicting beliefs.

The Levi identity connects them: $K * phi = (K - not phi) + phi$.

#strong[Key postulates for contraction.]
- #strong[Closure]: $K - phi$ is deductively closed.
- #strong[Success]: If $phi not in cal("Cn")(∅)$, then $phi not in K - phi$.
- #strong[Inclusion]: $K - phi subset.eq K$.
- #strong[Vacuity]: If $phi not in K$, then $K - phi = K$.
- #strong[Recovery]: $K subset.eq (K - phi) + phi$.
- #strong[Extensionality]: If $phi <-> psi$, then $K - phi = K - psi$.

#strong[The controversial Recovery postulate.] Recovery states that if we contract by $phi$ and then expand by $phi$, we recover
the original belief set. This is controversial: intuitively, contracting by $phi$
should lose more than just $phi$---it should also lose the specific evidence that
supported $phi$. Re-adding $phi$ doesn't restore that evidence.

#strong[Epistemic entrenchment.] Gärdenfors introduces entrenchment ordering:
$phi <=_epsilon psi$ <-> giving up $phi$ is at least as acceptable as giving
up $psi$. More entrenched beliefs are retained during contraction.

#heading(level: 4)[Ranking Theory]
#label("subsec:ranking-theory")

Spöhn develops an ordinal approach. A ranking function
$kappa : W -> NN union{infinity}$ assigns natural numbers to possible worlds,
with $kappa(w) = 0$ for the most plausible worlds. Belief degree is defined:
$
  beta(phi) = kappa(not phi) = min(kappa(w) : w models not phi)
$

Ranking theory handles iterated revision (where AGM struggles) and provides a
connection to probability through the formula $P(w) ∝ e^-kappa(w)$.

#heading(level: 4)[Dynamic Epistemic Logic]
#label("subsec:del")

Van Ditmarsch, van der Hoek, and Kooi develop modal operators
for belief change:
- $[phi!]psi$: "After publicly announcing $phi$, $psi$ holds."
- Action models generalize to arbitrary epistemic actions.

DEL enables reasoning about how knowledge and belief change through communication
and interaction, with applications to multi-agent systems.

#strong[Relevance to CLAIR] CLAIR extends AGM in three ways:
1. #strong[Graded beliefs]: Confidence replaces binary membership.
2. #strong[Structured justification]: Revision operates on the justification DAG,
  not just the belief set.
3. #strong[Recovery failure]: Recovery correctly fails---evidence has specific
  strength, and retracting a belief loses that evidence.

CLAIR's revision algorithm (modify graph $->$ identify affected $->$ recompute
confidence) is a graded generalization of TMS dependency-directed backtracking.

#heading(level: 3)[Graded Justification Logic]
#label("subsec:graded-justification-logic")

Standard Justification Logic (see #label("subsec:justification-logic")) provides explicit
justification terms but lacks graded confidence. Two recent extensions bridge this gap:

#heading(level: 4)[Milnikel's Logic of Uncertain Justifications]

Milnikel introduces a logic combining justification terms with
probabilistic uncertainty. Key innovations:

- #strong[Uncertainty strengths]: Justifications carry strength values $s in [0,1]$,
  representing the reliability of the justification source.
- #strong[Combination rules]: When multiple justifications support the same conclusion,
  their strengths combine via probabilistic sum: $s_1 ⊕ s_2 = 1 - (1-s_1)(1-s_2)$.
- #strong[Weakening]: Stronger justifications can be weakened, but weaker ones cannot
  be strengthened without additional evidence.

#strong[Relation to CLAIR.] Milnikel's approach is philosophically aligned with CLAIR's confidence tracking,
but differs in several respects:
- Milnikel focuses on #emph[source reliability] while CLAIR tracks #emph[epistemic commitment]
  at each inference step.
- Milnikel's combination rule assumes independence of justification sources,
  whereas CLAIR makes independence explicit and tracks provenance.
- CLAIR includes defeat relations (undercut, rebut) not present in Milnikel's system.

#heading(level: 4)[Fan and Liau's Logic of Justified Uncertain Beliefs]

Fan and Liau develop a logic for reasoning about justified beliefs
with uncertainty degrees. Their framework:

- #strong[Uncertainty degrees]: Beliefs have associated uncertainty values $u in [0,1]$,
  where lower $u$ indicates stronger justification.
- #strong[Justification structure]: Justifications form labeled trees where each node
  has an associated uncertainty.
- #strong[Propagation rules]: Uncertainty propagates through the justification structure
  via fuzzy logic operations.

#strong[Relation to CLAIR.] Fan and Liau's work shares CLAIR's goal of tracking justification strength
through reasoning, but:
- Their uncertainty is primarily #emph[aleatory] (about the world), while CLAIR's
  confidence is #emph[epistemic] (about the reasoning).
- Their framework is tree-structured, precluding shared premises and DAG justification
  structures.
- They do not address defeat relations or self-reference constraints.

#heading(level: 4)[The Gap CLAIR Fills]

Despite these important contributions, no existing graded justification logic combines:
1. #strong[DAG-structured justifications]: Shared premises create graph structure, not trees.
2. #strong[Epistemic confidence]: Tracking reasoning strength, not just source reliability.
3. #strong[Defeat semantics]: Explicit undercut and rebut operations.
4. #strong[Self-reference constraints]: Graded Löb-style reasoning limitations.

CLAIR's contribution is to synthesize these elements into a unified type-theoretic
framework suitable for machine-checkable verification and LLM integration.

#heading(level: 3)[Type-Theoretic Approaches to Uncertainty]
#label("sec:type-theory-bg")

Type theory provides the programming language substrate for CLAIR. We survey
approaches to tracking metadata through computation.

#heading(level: 4)[Information Flow Types]
#label("subsec:info-flow")

Myers and Sabelfeld develop type systems
that track security levels (confidentiality, integrity) through computation:
```
  int{Alice -> Bob} x;   // Alice owns, Bob can read
  int{Alice -> *}   y;   // Alice owns, public
  y = x;                 // ERROR: would leak to public
```
The type system prevents information leakage at compile time.

#strong[Relevance to CLAIR.] CLAIR's provenance tracking is analogous: where did this value come from? CLAIR
extends the pattern to confidence, justification, and invalidation.

#heading(level: 4)[Refinement Types]
#label("subsec:refinement")

Rondon, Kawaguchi, and Jhala introduce Liquid Types, extending
Hindley-Milner with logical predicates:
```
  {-@ type Nat = {v:Int | v >= 0} @-}
  {-@ type Pos = {v:Int | v > 0}  @-}

  {-@ div :: Int -> Pos -> Int @-}
  div x y = x `quot` y   -- y cannot be 0
```
Refinements are checked statically via SMT solvers.

#strong[Relevance to CLAIR.] Some CLAIR constraints could be expressed as refinements (e.g., confidence in $[0,1]$).
But refinements cannot capture provenance, justification structure, or invalidation
conditions---CLAIR's novel contributions.

#heading(level: 4)[Dependent Types and Proof Assistants]
#label("subsec:dependent")

The Curry-Howard correspondence identifies types with propositions and programs with
proofs. Dependent type systems (Coq, Agda, Idris, Lean) exploit this for formal
verification:
```
  def div (x : Nat) (y : Nat) (h : y > 0) : Nat := x / y
  -- Must provide proof h that y > 0
```
The proof is a value, checked by the type system.

#strong[Relevance to CLAIR.] CLAIR extends Curry-Howard: programs are not just proofs but #emph[beliefs with
justifications]. A CLAIR program carries:
- The value (what is believed)
- Confidence (how strongly)
- Provenance (from where)
- Justification (why)
- Invalidation conditions (when to reconsider)

#heading(level: 4)[Probabilistic Programming]
#label("subsec:prob-programming")

Probabilistic programming languages (Church, Stan, Pyro, Gen)
represent and manipulate probability distributions as first-class values:
```
  (define (coin-model)
    (let ((fair? (flip 0.9)))
      (if fair? (flip 0.5) (flip 0.9))))
```
These languages excel at statistical inference but focus on data uncertainty rather
than reasoning uncertainty. They require probabilistic normalization and lack
explicit justification structure.

#heading(level: 4)[Justification Logic]
#label("subsec:justification-logic")

Artemov extends modal logic with
explicit justification terms. Instead of $square phi$ ("$phi$ is known/believed"),
we write $t : phi$ ("$t$ is a justification for $phi$"). Terms include:
$
  t ::= c mid x mid t .t mid t + t mid !t
$
where $c$ is a constant (axiom), $x$ is a variable, $s .t$ is application
(modus ponens), $t + s$ is sum (either justification suffices), and $!t$ is proof
checking ($t$ justifies that $t$ justifies $phi$).

The key axiom is application:
$
  s : (phi -> psi) -> (t : phi -> (s .t) : psi)
$

#strong[Limitations.] Justification Logic produces tree-structured justifications (each conclusion from
fresh premises). It cannot represent:
- Shared premises (same evidence supporting multiple conclusions)
- Defeasible reasoning (defeat edges)
- Graded confidence

#strong[CLAIR's extension.] CLAIR adopts Justification Logic's core idea (explicit justification terms) but
extends it to:
1. #strong[DAGs]: Shared premises create graph structure.
2. #strong[Labeled edges]: Support, undercut, and rebut edges.
3. #strong[Graded confidence]: Each node carries confidence in $[0,1]$.

#heading(level: 2)[Synthesis: The Gap CLAIR Fills]
#label("sec:synthesis")

#table(
  columns: 3,
  align: (left, left, left),
  stroke: none,
  fill: (x, y) => if y == 0 { navy.darken(80%) } else if calc.mod(y, 2) == 0 { navy.darken(95%) } else { white },
  table.header([*Concept*, *Prior Work*, *CLAIR Extension*]),
  [Uncertainty], [Subjective Logic], [Epistemic confidence (about reasoning)],
  [Provenance], [Database provenance], [Computation provenance + invalidation],
  [Justification], [Justification Logic], [DAGs with labeled edges, defeat],
  [Belief revision], [TMS, AGM], [Graded, justification-based revision],
  [Design rationale], [IBIS/QOC], [First-class decisions in language],
  [Refinements], [Liquid Types], [+ confidence + invalidation],
  [Effects], [Effect systems], [+ intent + semantic meaning],
  [Self-reference], [Provability Logic (GL)], [Graded Löb (CPL)],
  [Multi-agent], [Arrow, Condorcet], [Pragmatic internal realism],
)

#strong[The gap.] No prior work combines:
1. Beliefs as first-class typed values with epistemic metadata
2. Confidence as non-probabilistic epistemic commitment
3. Justification as labeled DAGs with defeat semantics
4. Self-reference constraints derived from provability logic
5. Belief revision operating on justification structure

CLAIR provides this synthesis, offering a rigorous foundation for AI systems that
can explain and audit their own reasoning while honestly representing epistemic
limitations.

#strong[Key influences.] We acknowledge particular debts to:
- De Kleer's ATMS for dependency-directed reasoning
- Jøsang's Subjective Logic for uncertainty algebra
- Boolos's provability logic for self-reference treatment
- Pollock's defeater theory for defeat semantics
- Artemov's Justification Logic for explicit justifications
- Milnikel's graded justifications for uncertainty in justification terms

CLAIR is not a rejection of this prior work but a synthesis that combines their
insights into a coherent type-theoretic framework.
