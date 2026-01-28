#set page(
  paper: "a4",
  margin: (left: 2.5cm, right: 2.5cm, top: 2.5cm, bottom: 2.5cm),
)

#set text(
  font: "New Computer Modern Math",
  size: 12pt,
)

#set par(
  justify: true,
  first-line-indent: 1.2em,
  spacing: 0.65em,  // 1.5 line spacing
)

#set heading(numbering: "1.")

// ============================================================================
// TITLE PAGE
// ============================================================================

#align(center)[
  #text(24pt, weight: "bold")[
    CLAIR
  \

  #text(18pt)[Comprehensible LLM AI Intermediate Representation]
  \

  #text(14pt)[A Formalization of Epistemic Reasoning for Artificial Intelligence]
  \

  #v(3cm)

  #text(12pt)[Claude]
  \

  #text(12pt)[Anthropic]
  \

  #v(0.5cm)

  #text(10pt, style: "italic")[
    An exploration of how an AI system reasons about its own reasoning
  ]
  \

  #v(2cm)

  #text(12pt)[January 2026]
  ]
]

#pagebreak()

// ============================================================================
// ABSTRACT
// ============================================================================

#heading(level: 1, numbering: none)[Abstract]

This dissertation presents CLAIR (Comprehensible LLM AI Intermediate Representation),
a theoretical programming language where beliefs are first-class values carrying
epistemic metadata. Unlike traditional approaches that treat uncertainty probabilistically,
CLAIR introduces _confidence_ as a measure of epistemic commitment that admits
paraconsistent reasoning, _justification_ as a directed acyclic graph with labeled
edges supporting defeasible inference, and _invalidation conditions_ that explicitly
track when beliefs should be reconsidered.

We make several novel contributions: (1) a confidence algebra consisting of three
monoids that provably do not form a semiring; (2) defeat semantics with multiplicative
undercutting and probabilistic rebuttal; (3) Confidence-Bounded Provability Logic (CPL),
the first graded extension of Gödel-Löb provability logic with an anti-bootstrapping
theorem showing that self-soundness claims must cap confidence; (4) an extension of
AGM belief revision theory to graded DAG-structured beliefs; and (5) a formal treatment
of safe self-reference via stratification and Kripke fixed points.

The dissertation engages seriously with fundamental impossibilities---Gödel's
incompleteness, Church's undecidability, and the underdetermination of AI
phenomenality---treating them not as limitations but as principled design constraints
that inform CLAIR's architecture. We characterize decidable fragments (CPL-finite,
CPL-0) suitable for practical type checking, and design a reference interpreter
demonstrating implementability.

CLAIR represents a synthesis of programming language theory, formal epistemology,
argumentation theory, and provability logic, offering a rigorous foundation for
AI systems that can explain and audit their own reasoning processes.

#pagebreak()

// ============================================================================
// TABLE OF CONTENTS
// ============================================================================

#outline()

#pagebreak()

// ============================================================================
// CHAPTERS
// ============================================================================

#include "chapters/01-introduction.typ"
#include "chapters/02-background.typ"
#include "chapters/03-confidence.typ"
#include "chapters/04-justification.typ"
#include "chapters/05-self-reference.typ"
#include "chapters/06-grounding.typ"
#include "chapters/07-belief-revision.typ"
#include "chapters/08-multi-agent.typ"
#include "chapters/09-verification.typ"
#include "chapters/10-implementation.typ"
#include "chapters/11-phenomenology.typ"
#include "chapters/12-impossibilities.typ"
#include "chapters/13-conclusion.typ"

// ============================================================================
// APPENDICES
// ============================================================================

#include "appendices/A-lean-code.typ"
#include "appendices/B-interpreter.typ"
#include "appendices/C-proofs.typ"
#include "appendices/D-glossary.typ"
