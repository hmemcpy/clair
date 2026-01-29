// CLAIR: The Book
// A modern, readable book-style layout for the CLAIR specification
// Inspired by the Rust Book and other great programming language docs

// ============================================================================
// COLOR PALETTE (Warm, readable tones)
// ============================================================================

#let clair-colors = (
  primary: rgb("#2c3e50"),        // Deep slate for headings
  secondary: rgb("#34495e"),       // Lighter slate
  accent: rgb("#e67e22"),          // Warm orange for highlights
  accent-light: rgb("#f39c12"),    // Golden
  code-bg: rgb("#faf8f5"),         // Warm cream for code blocks
  code-border: rgb("#e8e4df"),     // Subtle border
  text: rgb("#2c3e50"),            // Main text
  text-light: rgb("#5d6d7e"),      // Secondary text
  sidebar-bg: rgb("#f8f9fa"),      // Light gray for sidebars
  tip-bg: rgb("#e8f6f3"),          // Soft green for tips
  note-bg: rgb("#fef9e7"),         // Soft yellow for notes
  warning-bg: rgb("#fdedec"),      // Soft red for warnings
)

// ============================================================================
// TYPOGRAPHY
// ============================================================================

#set page(
  paper: "a4",
  margin: (left: 2.5cm, right: 2.5cm, top: 2.5cm, bottom: 2.5cm),
  footer: context [
    #set text(size: 9pt, fill: clair-colors.text-light)
    #align(center)[
      #counter(page).display("1")
    ]
  ]
)

#set text(
  font: "Source Serif Pro",
  size: 11pt,
  fill: clair-colors.text,
  hyphenate: true,
)

#set par(
  justify: true,
  leading: 1.6em,
  first-line-indent: 0pt,
  spacing: 1.2em,
)

// ============================================================================
// HEADINGS
// ============================================================================

#set heading(numbering: "1.1.")

#show heading: it => {
  set text(font: "Source Sans Pro")
  set par(spacing: 0.8em)

  if it.level == 1 {
    v(2em)
    set text(size: 24pt, weight: "bold", fill: clair-colors.primary)
    it
    v(1.5em)
  } else if it.level == 2 {
    v(1.5em)
    set text(size: 16pt, weight: "bold", fill: clair-colors.primary)
    it
    v(1em)
  } else if it.level == 3 {
    v(1.2em)
    set text(size: 13pt, weight: "bold", fill: clair-colors.secondary)
    it
    v(0.8em)
  } else {
    v(1em)
    set text(size: 11pt, weight: "bold", fill: clair-colors.secondary)
    it
    v(0.6em)
  }
}

// ============================================================================
// CODE BLOCKS (Syntax Highlighting)
// ============================================================================

#show raw.where(block: true): it => {
  set text(
    font: "Source Code Pro",
    size: 9.5pt,
    fill: clair-colors.text,
  )

  block(
    fill: clair-colors.code-bg,
    stroke: 1pt + clair-colors.code-border,
    inset: 12pt,
    radius: 4pt,
    width: 100%,
    {
      // Add a subtle header bar
      place(top + left, dy: -12pt, dx: -12pt)[
        block(
          fill: clair-colors.code-border,
          width: 100% + 24pt,
          height: 8pt,
          radius: (top: 4pt),
        )
      ]
      v(4pt)
      it
    }
  )
}

#show raw.where(block: false): it => {
  set text(
    font: "Source Code Pro",
    size: 9.5pt,
    fill: clair-colors.accent,
  )
  box(
    fill: clair-colors.code-bg,
    inset: (x: 3pt, y: 1pt),
    radius: 2pt,
    it,
  )
}

// ============================================================================
// LISTS
// ============================================================================

#set list(
  indent: 1.5em,
  marker: ([•], [◦], [‣]),
)

#set enum(
  indent: 1.5em,
  numbering: "1.",
)

// ============================================================================
// LINKS
// ============================================================================

#show link: it => {
  set text(fill: clair-colors.accent)
  underline(it)
}

// ============================================================================
// TABLES
// ============================================================================

#set table(
  stroke: 0.5pt + clair-colors.code-border,
  inset: 8pt,
)

#show table: it => {
  block(
    fill: white,
    stroke: 1pt + clair-colors.code-border,
    radius: 4pt,
    inset: 0pt,
    it,
  )
}

#show table.cell.where(y: 0): it => {
  set text(weight: "bold", fill: clair-colors.primary)
  table.cell(fill: clair-colors.sidebar-bg, it)
}

// ============================================================================
// QUOTES
// ============================================================================

#show quote: it => {
  block(
    fill: clair-colors.sidebar-bg,
    stroke: (left: 4pt + clair-colors.accent),
    inset: 12pt,
    radius: (right: 4pt),
    width: 95%,
    {
      set text(style: "italic", size: 10.5pt)
      it.body
    }
  )
}

// ============================================================================
// CUSTOM ENVIRONMENTS
// ============================================================================

#let note(title: "Note", color: clair-colors.note-bg, icon: "📝", body) = {
  block(
    fill: color,
    stroke: 1pt + color.darken(20%),
    inset: 12pt,
    radius: 4pt,
    width: 100%,
    {
      text(weight: "bold", size: 10pt)[#icon #title]
      v(0.3em)
      body
    }
  )
  v(0.8em)
}

#let tip(body) = note(title: "Tip", color: clair-colors.tip-bg, icon: "💡", body)
#let warn(body) = note(title: "Warning", color: clair-colors.warning-bg, icon: "⚠️", body)

// ============================================================================
// TITLE PAGE
// ============================================================================

#page(margin: (left: 3cm, right: 3cm, top: 4cm, bottom: 3cm))[
  #align(center)[
    #v(2cm)

    #text(size: 42pt, weight: "bold", fill: clair-colors.primary)[
      CLAIR
    ]

    #v(0.5cm)

    #text(size: 18pt, fill: clair-colors.text-light)[
      Comprehensible LLM AI Intermediate Representation
    ]

    #v(1.5cm)

    #text(size: 14pt, style: "italic", fill: clair-colors.secondary)[
      A Specification for Auditable AI Reasoning
    ]

    #v(3cm)

    #block(
      fill: clair-colors.code-bg,
      stroke: 1pt + clair-colors.code-border,
      inset: 16pt,
      radius: 8pt,
      width: 80%,
      {
        set text(font: "Source Code Pro", size: 10pt)
        ```clair
        b1 .95 L0 @user "Explain yourself"
        b2 .9  L0 @self <b1 "I track my reasoning"
        b3 .85 L0 @self <b2 "So you can audit it"
        ```
      }
    )

    #v(3cm)

    #text(size: 12pt)[
      A comprehensive specification of the intermediate representation \
      for reasoning traces, confidence propagation, and epistemic transparency
    ]

    #v(2cm)

    #text(size: 11pt, fill: clair-colors.text-light)[
      January 2026
    ]
  ]
]

// ============================================================================
// TABLE OF CONTENTS
// ============================================================================

#pagebreak()

#outline(
  title: [
    #v(1cm)
    #text(size: 24pt, weight: "bold", fill: clair-colors.primary)[Contents]
    #v(1cm)
  ],
  indent: auto,
)

// ============================================================================
// PREFACE
// ============================================================================

#pagebreak()

= Preface

This book is a complete specification of CLAIR—an intermediate representation designed for AI systems that need to explain their reasoning. Unlike traditional programming languages or compiler IRs, CLAIR treats *epistemic state* as first-class: beliefs carry confidence, justifications, and invalidation conditions.

#tip[
  If you're new to CLAIR, start with Chapter 1 (Introduction) and Chapter 10 (Implementation) for a quick overview of the format and the Thinker+Assembler architecture.
]

CLAIR is not a programming language. It is a *data format* for reasoning traces—a directed acyclic graph of beliefs that captures what an AI concluded, why, and when it should reconsider. The content of each belief is opaque natural language; the structure (confidence, provenance, justification DAG) is what makes CLAIR useful.

#warn[
  CLAIR emerged from a paradigm shift during its development. Earlier drafts treated CLAIR as a typed programming language. The current specification—presented in this book—treats it as an intermediate representation produced by one LLM (the Thinker) and consumed by another (the Assembler).
]

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

= Appendices

These appendices contain supplementary material: the Lean formalization, proofs, glossary, and complete language specification.

#include "appendices/A-lean-code.typ"
#include "appendices/B-interpreter.typ"
#include "appendices/C-proofs.typ"
#include "appendices/D-glossary.typ"
#include "appendices/E-language-spec.typ"
#include "appendices/F-evaluation-prompts.typ"
