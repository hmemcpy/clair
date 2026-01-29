// CLAIR Dissertation - Graceful Genetics Template
// Author: Claude, Anthropic
// Date: January 2026

#import "@preview/graceful-genetics:0.2.0"
#import "layout.typ": *

// Apply graceful-genetics template with dissertation metadata
#show: graceful-genetics.template.with(
  title: [CLAIR: Comprehensible LLM AI Intermediate Representation],
  authors: (
    (
      name: "Claude",
      department: "AI Research",
      institution: "Anthropic",
      city: "San Francisco",
      country: "USA",
      mail: "claude@anthropic.com",
    ),
  ),
  date: (
    year: 2026,
    month: "January",
  ),
  keywords: (
    "Epistemic Logic",
    "Confidence Measures",
    "Justification Graphs",
    "Paraconsistent Reasoning",
    "Provability Logic",
    "Belief Revision",
    "Self-Reference",
    "Type Theory",
  ),
  abstract: [
    This dissertation presents CLAIR (Comprehensible LLM AI Intermediate Representation),
    a theoretical programming language where beliefs are first-class values carrying
    epistemic metadata. Unlike traditional approaches that treat uncertainty probabilistically,
    CLAIR introduces #emph[confidence] as a measure of epistemic commitment that admits
    paraconsistent reasoning, #emph[justification] as a directed acyclic graph with labeled
    edges supporting defeasible inference, and #emph[invalidation conditions] that explicitly
    track when beliefs should be reconsidered.

    We make several novel contributions: (1) a confidence algebra consisting of three
    monoids that provably do not form a semiring; (2) defeat semantics with multiplicative
    undercutting and probabilistic rebuttal; (3) Confidence-Bounded Provability Logic (CPL),
    the first graded extension of Gödel-Löb provability logic with an anti-bootstrapping
    theorem showing that self-soundness claims cap confidence; (4) an extension of
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
  ],
)

// Custom styling adjustments for dissertation
#set page(
  paper: "a4",
  margin: (top: 2.5cm, bottom: 2.5cm, inside: 3cm, outside: 2cm),
)

// Preserve academic color scheme
#show raw: it => block(
  fill: rgb("#faf8f5"),
  stroke: 1pt + rgb("#1a2332"),
  inset: 10pt,
  radius: 3pt,
  it
)

#show quote: it => block(
  fill: rgb("#faf8f5"),
  inset: (left: 15pt, right: 15pt, top: 10pt, bottom: 10pt),
  width: 85%,
  [
    #set text(size: 10pt, style: "italic")
    #set block(above: 0.3em, below: 0.3em)
    it.body
  ]
)

// ============================================================================
// TABLE OF CONTENTS
// ============================================================================

#pagebreak()
#align(center)[
  #set text(size: 22pt, weight: "bold")
  [Contents]
]
#v(1cm)
#outline(title: none, indent: auto)
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
#include "chapters/14-evaluation.typ"

// ============================================================================
// APPENDICES
// ============================================================================

#pagebreak()
#align(center)[
  #set text(size: 22pt, weight: "bold")
  [Appendices]
]
#v(1cm)

#include "appendices/A-lean-code.typ"
#include "appendices/B-interpreter.typ"
#include "appendices/C-proofs.typ"
#include "appendices/D-glossary.typ"
#include "appendices/E-language-spec.typ"
#include "appendices/F-evaluation-prompts.typ"
