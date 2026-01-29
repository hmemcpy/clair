#import "../layout.typ": *

// Chapter 3: Confidence System
#heading(level: 1)[Confidence System]

#align(center)[
  #set text(font: "Georgia", size: 10pt, style: "italic", fill: rgb("#666"))
  "Probability is not about what is true. It is about what is reasonable to believe."
  #h(0.3em)
  #align(right)[--- E.T. Jaynes, #emph[Probability Theory: The Logic of Science]]
]

The confidence system is the algebraic foundation of CLAIR. This chapter defines
confidence formally, distinguishes it from probability, and develops the theory of
#emph[epistemic linearity]---treating evidence as a resource that cannot be
counted multiple times. We then establish the three monoid structures that govern
how confidence values combine, proving key properties in Lean 4 to connect
abstract theory to machine-verified implementation.

#heading(level: 2)[Confidence as Calibrated Reliability]

#heading(level: 3)[Semantic Commitments]

Before defining the confidence algebra, we must state our semantic commitments
explicitly. The PhD review correctly identified that "confidence" was underspecified
in earlier drafts. We now clarify:

#definition[
  #strong[Calibrated Reliability.]

  A confidence value #emph[c in C = [0,1]] represents the #strong[calibrated reliability]
  of an information source or derivation process. Specifically:

  + If a source assigns confidence #emph[c] to proposition #emph[phi], this means: #quote[Across the
    reference class of similar situations where this source assigns confidence #emph[c],
    the proposition #emph[phi] is correct with frequency #emph[c].]

  + Calibration is an #emph[external] property: a source is calibrated if its stated
    confidences match empirical accuracy over relevant reference classes.

  + CLAIR #emph[tracks] calibrated reliability without #emph[guaranteeing] it. The system
    propagates confidence values through derivation rules, but calibration of the
    initial axioms and sources is an empirical question.
]

This interpretation addresses three semantic options from the review:

+ #strong[Not pure probability]: Confidence does #strong[not] satisfy #emph[P(phi) + P(not phi) = 1].
  We allow paraconsistent reasoning where both #emph[phi] and #emph[not phi] may have low confidence.

+ #strong[Not fuzzy truth degree]: Confidence is #strong[not] the degree to which #emph[phi] is true
  in some multivalued logic. It is the reliability of the #emph[source asserting] #emph[phi].

+ #strong[Reliability semantics]: Confidence is calibrated reliability of the epistemic
  process producing the belief. This distinguishes #quote[how strongly I believe] from
  #quote[how often I'm right when I believe this strongly].

#heading(level: 3)[The Problem with Probability]

Standard approaches to uncertain reasoning use probability. A probability measure
#emph[P] on a set #emph[Omega] of outcomes satisfies the Kolmogorov axioms:

+ #emph[P(A) >= 0] (Non-negativity)
+ #emph[P(Omega) = 1] (Normalization)
+ #emph[P(A union B) = P(A) + P(B) - P(A intersect B)] (Additivity)

For propositions, this implies the fundamental constraint:
#emph[P(phi) + P(not phi) = 1]

This #strong[normalization requirement] creates three problems for modeling epistemic
states:

+ #strong[Balanced uncertainty.]
  An agent confronting an unfamiliar topic may be uncertain about both #emph[phi] and
  #emph[not phi]. If asked #quote[Is there intelligent life elsewhere in the universe?]
  a reasonable response is low confidence in #emph[both] yes and no---not because
  the evidence is balanced, but because there is insufficient evidence either way.
  Probability forces #emph[P(yes) + P(no) = 1], conflating #quote[I don't know]
  with #quote[the evidence is exactly balanced.]

+ #strong[Paraconsistent reasoning.]
  Evidence sometimes supports both #emph[phi] and #emph[not phi] before contradiction
  resolution. A detective might have testimony that a suspect was present (supporting
  guilt) and an alibi (supporting innocence), without yet knowing which is false.
  Probability makes this impossible: #emph[P(phi) > 0.5] and #emph[P(not phi) > 0.5] is
  a contradiction.

+ #strong[Derivation semantics.]
  In Bayesian reasoning, #emph[P(A and B) = P(A) times P(B|A)], where conditioning
  captures the dependency structure. But for derivation---where #emph[B] follows from #emph[A]
  by some rule---there is no clear conditional to use. The semantics of #quote[A is a
  premise for B] differs from #quote[B is probable given A is true.]

#heading(level: 3)[Definition of Confidence]

CLAIR's confidence addresses these problems by dropping normalization:

#definition[
  #strong[Confidence Value.]

  A #strong[confidence value] is a real number #emph[c in [0, 1]]. We write #emph[C]
  for the set of confidence values: #emph[C = set(c in RR | 0 <= c <= 1)]
]

The semantic interpretation under calibrated reliability:

+ #emph[c = 1]: Axiomatic acceptance (treated as foundational)
+ #emph[c = 0]: Complete rejection (treated as impossibility)
+ #emph[c = 0.5]: Maximal uncertainty (no evidence either direction)
+ #emph[c > 0.5]: Net evidence for acceptance
+ #emph[c < 0.5]: Net evidence for rejection

#definition[
  #strong[Epistemic Commitment.]

  Confidence represents #strong[epistemic commitment]: the degree to which an agent
  commits to a proposition based on available evidence and reasoning, #emph[interpreted]
  as the calibrated reliability of the source or derivation producing the belief.

  Unlike probability:

  1. #strong[No normalization]: #emph[conf(phi) + conf(not phi)] need not equal 1.
  2. #strong[Not frequency]: #emph[conf(phi) = 0.9] does #emph[not] mean #quote[true 90% of the time]
     in a single case. It means #quote[this source is calibrated such that across
     similar cases with confidence 0.9, the proposition is correct 90% of the time.]
  3. #strong[Derivation-based]: Confidence propagates through inference rules,
        not conditioning.
]

#example[
  #strong[Non-normalized confidence.]

  Consider the proposition #quote[This code has no security vulnerabilities.] An honest
  assessment might be:
  #emph[conf(no vulnerabilities) = 0.4] (some evidence from testing)
  #emph[conf(has vulnerabilities) = 0.3] (some evidence from complexity)
  The sum #emph[0.4 + 0.3 = 0.7 < 1] reflects residual uncertainty---neither hypothesis
  is well-supported. This is inexpressible in probability.
]

#heading(level: 3)[Falsifiability Criteria]

Following the review's requirement, we state explicitly what would falsify CLAIR's
confidence model:

+ #strong[Empirical falsification]: If sources systematically assign confidence #emph[c]
  to propositions but are correct with frequency #emph[f != c], they are #emph[uncalibrated].
  CLAIR provides no mechanism to #emph[detect] uncalibrated sources---this requires
  external validation.

+ #strong[Semantic falsification]: If interpretation as #quote[calibrated reliability]
  leads to contradictions in the algebra (e.g., violations of monoid laws), the
  semantics would be inadequate. The Lean 4 formalization verifies algebraic consistency.

+ #strong[Competing semantics]: If an alternative interpretation (e.g., pure probability
  or fuzzy truth) provides better empirical calibration or algebraic properties,
  CLAIR's semantics would need revision.

#heading(level: 3)[Comparison with Subjective Logic]

Jøsang's Subjective Logic (Jøsang, 2016) extends probability with
explicit uncertainty. An #emph[opinion] is a tuple #emph[omega = (b, d, u, a)]:

+ #emph[b]: belief mass (evidence for)
+ #emph[d]: disbelief mass (evidence against)
+ #emph[u]: uncertainty mass (lack of evidence)
+ #emph[a]: base rate (prior probability)

with constraint #emph[b + d + u = 1].

CLAIR's confidence can be viewed as a simplification of Subjective Logic:
#emph[c = b + u times a]
where we collapse uncertainty into the confidence value via the base rate. This
loses the #emph[b/d/u] decomposition but gains simplicity. The trade-off is appropriate
for CLAIR's focus on derivation tracking rather than uncertainty quantification.

#quote[
  _Note._ #linebreak

  CLAIR could be extended to full Subjective Logic opinions. The algebraic
  structure developed in this chapter would generalize, with the three monoids
  operating on opinion tuples. We leave this extension to future work.
]

#heading(level: 2)[The Aggregation Monoid]

When multiple independent pieces of evidence support the same conclusion,
confidence should #emph[increase]. This requires the probabilistic OR operation.

#heading(level: 3)[Probabilistic OR (Oplus)]

#definition[
  #strong[Probabilistic OR (Oplus).]

  For confidence values #emph[a, b in C], their #strong[aggregation] is:
  #emph[a oplus b = a + b - a times b]
]

The formula has several equivalent forms:
+ #emph[a oplus b = a + b(1 - a)]
+ #emph[a oplus b = a(1 - b) + b]
+ #emph[a oplus b = 1 - (1 - a)(1 - b)] (De Morgan duality with multiplication)

The last form reveals the duality: #emph[a oplus b] is the complement of the product of complements.

#theorem[
  #strong[Oplus Preserves Bounds.]

  For all #emph[a, b in C]: #emph[a oplus b in C]
  #proof[
    #strong[Lower bound]: #emph[a oplus b = a + b(1 - a) >= 0] since #emph[a >= 0], #emph[b >= 0], and #emph[(1 - a) >= 0].

    #strong[Upper bound]: #emph[a oplus b = a + b(1 - a) <= 1] since #emph[b <= 1] implies #emph[b(1 - a) <= 1 - a],
    therefore #emph[a + b(1 - a) <= a + (1 - a) = 1].
  ]
]

#theorem[
  #strong[Oplus Monoid.]

  #emph[(C, oplus, 0)] is a commutative monoid with absorbing element #emph[1]:

  1. #strong[Associativity]: #emph[(a oplus b) oplus c = a oplus (b oplus c)]
  2. #strong[Commutativity]: #emph[a oplus b = b oplus a]
  3. #strong[Identity]: #emph[0 oplus a = a oplus 0 = a]
  4. #strong[Absorption]: #emph[1 oplus a = a oplus 1 = 1]
  #proof[
    All properties follow from standard real number arithmetic on #[0,1].
  ]
]

#heading(level: 3)[Confidence-Increasing Property]

Unlike multiplication, #emph[oplus] #emph[increases] confidence:

#theorem[
  #strong[Oplus is Confidence-Increasing.]

  For all #emph[a, b in C]: #emph[a oplus b >= max(a, b)]
  #proof[
    Using form #emph[a oplus b = a + b(1-a)]. Since #emph[b(1-a) >= 0], we have #emph[a oplus b >= a].
    By commutativity, #emph[a oplus b >= b]. Therefore #emph[a oplus b >= max(a, b)].
  ]
]

#corollary[
  #strong[Diminishing Returns.]

  The marginal gain from additional evidence decreases as confidence grows:
  #emph[(del)/(del b)(a oplus b) = 1 - a]
  When #emph[a] is already high, additional evidence contributes less.
]

#example[
  #strong[Aggregation of Weak Evidence.]

  Suppose we have ten independent pieces of weak evidence, each with confidence
  #emph[0.3]. The combined confidence is:
  #emph[0.3 oplus 0.3 oplus ... oplus 0.3 (10 times) = 1 - (1 - 0.3)^10 = 1 - 0.7^10 approx 0.972]
  Ten weak independent witnesses produce high combined confidence.
]

#heading(level: 3)[The "Survival of Doubt" Interpretation]

The formula #emph[a oplus b = 1 - (1-a)(1-b)] admits a probability-theoretic
interpretation under calibrated reliability:

+ #emph[(1 - a)] is the #quote[doubt] in evidence #emph[a]
+ #emph[(1 - a)(1 - b)] is the probability #emph[both] pieces of evidence fail (assuming independence)
+ #emph[a oplus b] is the probability #emph[at least one] succeeds

This #quote[survival of doubt] interpretation explains why aggregation increases
confidence: more independent evidence means more chances for at least one
to be correct.

#heading(level: 2)[The Multiplication Monoid]

When a conclusion is derived from premises, its confidence depends on the
premises' confidences. The simplest case is conjunctive derivation: both
premises must hold for the conclusion to follow.

#heading(level: 3)[Conjunctive Confidence Propagation]

#definition[
  #strong[Confidence Multiplication.]

  For confidence values #emph[a, b in C], their #strong[multiplicative combination]
  is standard multiplication: #emph[a times b]
]

This models the intuition that deriving #emph[C] from #emph[A] and #emph[B] requires both to
be true. If we are 90% confident in #emph[A] and 80% confident in #emph[B], our
confidence in #emph[C] (derived from both) is at most #emph[0.9 times 0.8 = 0.72].

#theorem[
  #strong[Multiplication Preserves Bounds.]

  For all #emph[a, b in C]: #emph[a times b in C]
  #proof[
    We prove both bounds:
    1. #emph[a times b >= 0]: Since #emph[a >= 0] and #emph[b >= 0], their product is non-negative.
    2. #emph[a times b <= 1]: Since #emph[b <= 1], we have #emph[a times b <= a times 1 = a <= 1].
  ]
]

#theorem[
  #strong[Multiplication Monoid.]

  #emph[(C, times, 1)] is a commutative monoid with absorbing element #emph[0]:

  1. #strong[Associativity]: #emph[(a times b) times c = a times (b times c)]
  2. #strong[Commutativity]: #emph[a times b = b times a]
  3. #strong[Identity]: #emph[1 times a = a times 1 = a]
  4. #strong[Absorption]: #emph[0 times a = a times 0 = 0]
  #proof[
    All properties follow from standard real number arithmetic on #[0,1].
  ]
]

#heading(level: 3)[The Derivation Monotonicity Principle]

A fundamental property of CLAIR is that derivation can only decrease confidence:

#theorem[
  #strong[Derivation Monotonicity.]

  For all #emph[a, b in C]: #emph[a times b <= min(a, b)]
  In particular, #emph[a times b <= a] and #emph[a times b <= b].
  #proof[
    Since #emph[b <= 1], we have #emph[a times b <= a times 1 = a].
    By commutativity, #emph[a times b <= b].
    Therefore #emph[a times b <= min(a, b)].
  ]
]

#corollary[
  #strong[No Confidence Amplification.]

  No sequence of conjunctive derivations can increase confidence. If #emph[c_0] is
  the confidence of a foundational belief and #emph[c_n] is derived through #emph[n]
  multiplicative steps, then #emph[c_n <= c_0].
]

This principle is essential for CLAIR's epistemology: derived beliefs are
never more confident than their sources. Certainty (#emph[c = 1]) is reserved for
axioms, not conclusions.

#heading(level: 2)[Defeat Operations]

Beyond derivation and aggregation, CLAIR requires operations for #emph[defeat]:
when evidence undermines a belief.

#heading(level: 3)[Undercut: Attacking the Inference]

Following Pollock (2001), an #emph[undercutting defeater]
attacks the inferential link, not the conclusion directly.

#definition[
  #strong[Undercut.]

  For confidence #emph[c] in a conclusion and defeat strength #emph[d]:
  #emph[undercut(c, d) = c times (1 - d)]
]

#example[
  #strong[Undercutting Defeat.]

  Consider the inference: #quote[The object looks red, therefore it is red.]
  An undercut #quote[The room has red lighting] doesn't claim the object isn't red;
  it undermines the inference from appearance to reality.

  If #emph[conf(looks red => is red) = 0.9] and
  #emph[conf(red lighting) = 0.6], then:
  #emph[undercut(0.9, 0.6) = 0.9 times (1 - 0.6) = 0.9 times 0.4 = 0.36]
  The inference confidence drops from 0.9 to 0.36.
]

#theorem[
  #strong[Undercut Preserves Bounds.]

  For all #emph[c, d in C]: #emph[undercut(c, d) in C]
  #proof[
    Since #emph[d <= 1], we have #emph[(1 - d) >= 0].
    Since #emph[c >= 0], we have #emph[c times (1 - d) >= 0].
    Since #emph[c <= 1] and #emph[(1 - d) <= 1], we have #emph[c times (1 - d) <= 1].
  ]
]

#theorem[
  #strong[Undercut Composition.]

  Sequential undercuts compose via #emph[oplus]:
  #emph[undercut(undercut(c, d_1), d_2) = undercut(c, d_1 oplus d_2)]
  #proof[
    By expanding the definition:
    #emph[undercut(undercut(c, d_1), d_2) = c(1 - d_1)(1 - d_2)]
    #emph[= c(1 - (d_1 + d_2 - d_1 times d_2))]
    #emph[= c(1 - (d_1 oplus d_2))]
    #emph[= undercut(c, d_1 oplus d_2)]
  ]
]

This beautiful result shows that defeat strengths aggregate via #emph[oplus]: multiple
undercuts combine as if their doubts aggregated.

#heading(level: 3)[Rebut: Competing Evidence]

A #emph[rebutting defeater] provides counter-evidence for the conclusion directly.

#definition[
  #strong[Rebut.]

  For confidence #emph[c_for] in favor and #emph[c_against] against:
  #emph[rebut(c_for, c_against) = cases((c_for / (c_for + c_against), if c_for + c_against > 0), (0.5, if c_for = c_against = 0))]
]

The formula treats evidence symmetrically: the resulting confidence is the
#quote[market share] of supporting evidence.

#theorem[
  #strong[Rebut Preserves Bounds.]

  For all #emph[c_for, c_against in C]: #emph[rebut(c_for, c_against) in C]
  #proof[
    If #emph[c_for + c_against = 0], the result is #emph[0.5 in [0,1]].
    Otherwise:
    + #emph[rebut >= 0] because #emph[c_for >= 0] and the denominator is positive.
    + #emph[rebut <= 1] because #emph[c_for <= c_for + c_against].
  ]
]

#theorem[
  #strong[Rebut Antisymmetry.]

  #emph[rebut(a, b) + rebut(b, a) = 1]
  #proof[
    When #emph[a + b > 0]:
    #emph[rebut(a, b) + rebut(b, a) = a/(a+b) + b/(a+b) = (a+b)/(a+b) = 1]
    When #emph[a = b = 0]: #emph[rebut(a,b) = rebut(b,a) = 0.5], so the sum is #emph[1].
  ]
]

#heading(level: 2)[Independence Assumptions for Aggregation]

The #emph[oplus] operation assumes independence of evidence sources. This is a critical
assumption that must be stated explicitly:

#definition[
  #strong[Conditional Independence for Oplus.]

  Two evidence sources #emph[e_1] and #emph[e_2] are #strong[independent] with respect
  to proposition #emph[phi] if:
  #emph[P(phi | e_1, e_2) = P(phi | e_1) + P(phi | e_2) - P(phi | e_1) times P(phi | e_2)]
  Under calibrated reliability, this means the reference classes of #emph[e_1] and #emph[e_2]
  do not systematically overlap.
]

When independence fails, #emph[oplus] overcounts evidence. CLAIR provides two mechanisms:

1. #strong[Correlation-aware aggregation]: Chapter 4 introduces #emph[oplus_delta] for
   correlated evidence, where #emph[delta in [0,1]] measures dependency.

2. #strong[Affine type system]: Evidence usage is tracked at type level, preventing
   the same source from being counted twice in a derivation.

#heading(level: 2)[Conclusion]

This chapter established the algebraic and semantic foundation of CLAIR:

+ #strong[Confidence as calibrated reliability]: We explicitly interpret confidence
  as the calibrated reliability of information sources and derivation processes.
  This addresses the review's concern about underspecified semantics.

+ #strong[Independence assumptions]: The #emph[oplus] operation requires conditional
  independence of evidence sources. We provide #emph[oplus_delta] for correlated evidence
  and affine typing to prevent double-counting.

+ #strong[Three monoids, not a semiring]: Multiplication (derivation),
  and oplus (aggregation) serve distinct semantic roles and do not distribute.

+ #strong[Defeat operations]: Undercut and rebut formalize how evidence
  can undermine beliefs, with undercuts composing beautifully via oplus.

+ #strong[Machine-verified]: The algebra is formalized in Lean 4, ensuring
  type safety and algebraic correctness.

The confidence system provides the numeric foundation. The next
chapter develops the #emph[structural] foundation: how beliefs connect through
justification DAGs.
