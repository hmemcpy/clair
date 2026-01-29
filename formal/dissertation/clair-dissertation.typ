// CLAIR Dissertation - Professional Academic Layout
// Author: Claude, Anthropic
// Date: January 2026

#import "layout.typ": *

#set page(
  paper: "a4",
  margin: (top: 2.5cm, bottom: 2.5cm, inside: 3cm, outside: 2cm),
  footer: context {
    align(center)[
      set text(size: 9pt, fill: rgb("#666"))
      counter(page).display()
    ]
  },
)

#set text(
  font: "Georgia",
  size: 11pt,
)

#show heading: it => {
  set text(font: "Helvetica", weight: "bold")
  set block(above: 0.8em, below: 0.4em)
  if it.level == 1 {
    set text(size: 22pt)
    it
    v(0.3em, weak: true)
    line(length: 30%, stroke: 0.5pt)
  } else if it.level == 2 {
    set text(size: 16pt)
    it
  } else {
    set text(size: 13pt)
    it
  }
}

#set par(
  justify: true,
  first-line-indent: 1.2em,
  spacing: 0.65em,
)

#show heading: it => {
  it
  set par(first-line-indent: 0em)
}

#show raw: it => block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  it
)

#show quote: it => block(
  fill: academic-cream,
  inset: (left: 15pt, right: 15pt, top: 10pt, bottom: 10pt),
  width: 85%,
  [
    #set text(size: 10pt, style: "italic")
    #set block(above: 0.3em, below: 0.3em)
    it.body
  ]
)

#show list.item: it => {
  set text(fill: academic-burgundy, weight: "bold")
  it.body
}

#set list(spacing: 0.5em)

// ============================================================================
// FRONT MATTER
// ============================================================================

#title_page()
#abstract_page()
#toc_page()

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
#include "appendices/E-language-spec.typ"
