// Chapter 6: Grounding
// Explores how CLAIR beliefs connect to observable reality

#import "../layout.typ": *

#chapter(6, "Grounding")

#h(0.2em)
#align(right)[--- #emph[Susan Haag], #emph[Metaphysical Grounding]]

#heading(level: 2)[The Grounding Problem]

A fundamental challenge for any epistemic system is the #emph[grounding problem]:
how do beliefs ultimately connect to observable reality? In CLAIR, this problem
takes on particular urgency because the system supports arbitrary confidence
values and paraconsistent reasoning. Without a principled account of grounding,
a CLAIR system could generate high-confidence beliefs that are entirely detached
from reality.

#heading(level: 3)[What grounding means in CLAIR.]

In CLAIR, #emph[grounding] refers to the process by which beliefs acquire their
initial epistemic support from sources external to the reasoning system itself.
These sources include:

+ #strong[Perceptual inputs]: Direct observations from sensors or user input
+ #strong[Testimony]: Information received from other agents or sources
+ #strong[Logical axioms]: Foundational assumptions accepted without proof
+ #strong[Demarcation constraints]: Meta-level restrictions on belief formation

A #emph[grounded belief] is one whose justification graph ultimately traces
back to at least one grounding source. An #emph[ungrounded belief] is one that
exists only through inference from other beliefs, without any external anchor.

#heading(level: 2)[Perceptual Grounding]

The most direct form of grounding is through perceptual input. CLAIR provides
builtin primitives for introducing grounded beliefs:

```
// Ground a proposition with a given confidence
observe(P, 0.9)

// Ground from a trusted source with provenance
testify(P, 0.8, "expert_testimony")
```

These primitives create belief nodes with special Ground justification
nodes that cannot be defeated through ordinary inference. The confidence
assigned at grounding becomes an upper bound on any downstream inferences---this
is the #emph[grounding cap] principle.

#heading(level: 3)[The grounding cap theorem.]

#theorem[
  If belief $b$ is grounded with confidence $c$, then for any belief $d$
  derived from $b$ through valid CLAIR inference rules, conf$(d) <= c$.
]

This theorem ensures that grounding provides a genuine constraint on reasoning:
high confidence can only be achieved through direct grounding, not through
inferential amplification.

#heading(level: 2)[Axiomatic Grounding]

Not all beliefs can be grounded perceptually. Mathematical truths, logical
principles, and conceptual frameworks require #emph[axiomatic grounding]---
the acceptance of certain propositions as foundational.

CLAIR supports this through the axiom primitive:

```
// Accept as a logical axiom
axiom(forall x. P(x) -> Q(x), 1.0)

// Accept a conceptual framework assumption
axiom("induction_principle", 0.95)
```

Axiomatic beliefs are assigned confidence 1.0 by convention, reflecting their
status as constitutive of the reasoning framework itself. However, CLAIR also
allows for #emph[penumbral axioms]---framework assumptions assigned high but
not maximal confidence, acknowledging their potential revisability.

#heading(level: 3)[The problem of circular axioms.]

A subtle issue arises when axioms are defined in terms of the very concepts
they purport to ground. CLAIR addresses this through #emph[stratification]:
axioms must be grounded in a lower stratum than the beliefs they support. This
prevents circular justification while still allowing for rich, interconnected
conceptual frameworks.

#heading(level: 2)[Social Grounding and Testimony]

Many beliefs are acquired through testimony from other agents. CLAIR models this
through #emph[social grounding] primitives that track the provenance of beliefs:

```
// Accept testimony from a source with given reliability
testify(P, reliability(agent), agent)
```

The confidence in testimony is a function of both the reported confidence and
the source's reliability. CLAIR implements this via the #emph[testimony
aggregation function]:

$$ conf(testify(P, c, s)) = c times reliability(s) $$

#heading(level: 3)[Reputation and source tracking.]

CLAIR maintains provenance information for each belief, allowing the system to
trace beliefs back to their original sources. This enables #emph[retrospective
downgrading]: if a source is later discovered to be unreliable, all beliefs
grounded in that source can have their confidence adjusted accordingly.

#heading(level: 2)[The Ungrounded: Free-Floating Beliefs]

An important design question is whether CLAIR should allow beliefs that are
completely ungrounded---beliefs that exist only through their relationships
to other ungrounded beliefs.

We permit such beliefs but require them to be marked with a special
Untethered status. This serves as a warning to downstream reasoning:
these beliefs are #emph[epistemically adrift] and should not form the basis
for high-stakes decisions.

#heading(level: 3)[Creative inference and hypothetical reasoning.]

Despite their epistemic limitations, untethered beliefs serve important
functions:

+ They enable #emph[hypothetical reasoning]---exploring the consequences of
  assumptions without committing to their truth
+ They support #emph[creative inference]---generating novel hypotheses that
  can later be tested and grounded
+ They provide a space for #emph[conceptual exploration]---developing new
  frameworks before their empirical connection is established

#heading(level: 2)[Grounding Requirements]

CLAIR implements three levels of grounding requirements:

#heading(level: 3)[Tier 1: Strict grounding.]

In safety-critical applications, CLAIR can enforce a strict grounding policy:
every belief must have a grounding chain tracing back to perceptual or axiomatic
sources. Untethered beliefs are rejected entirely.

#heading(level: 3)[Tier 2: Demarcated ungrounding.]

For most applications, CLAIR allows untethered beliefs but requires them to be
explicitly demarcated. These beliefs cannot form the basis for certain kinds
of high-stakes inferences without additional grounding.

#heading(level: 3)[Tier 3: Permissive ungrounding.]

For exploratory and research applications, CLAIR can operate in permissive mode,
allowing arbitrary ungrounded beliefs. This is useful for mathematical
exploration and creative hypothesis generation.

#heading(level: 2)[Summary]

Grounding in CLAIR provides the connection between abstract reasoning and
observable reality. By implementing multiple forms of grounding---perceptual,
axiomatic, and social---and by enforcing grounding caps that prevent
unjustified confidence amplification, CLAIR ensures that beliefs remain
epistemically anchored even while supporting sophisticated paraconsistent
reasoning.

The grounding architecture acknowledges that not all reasoning needs to be
grounded at all times. Hypothetical reasoning, conceptual exploration, and
creative inference all benefit from the freedom to form ungrounded beliefs. But
by making grounding status explicit and trackable, CLAIR ensures that agents
know when they are operating on solid epistemic footing and when they are
engaging in more speculative forms of reasoning.
