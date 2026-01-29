// CLAIR Dissertation - Professional Academic Layout
// Author: Igal Tabachnik, Igal Tabachnik
// Date: January 2026

#set page(
  paper: "a4",
  margin: (top: 2.5cm, bottom: 2.5cm, inside: 3cm, outside: 2cm),
  footer: align(center)[
    #set text(size: 9pt, fill: rgb("#666"))
    #counter(page).display()
  ],
)

#set text(
  font: "New Computer Modern Roman",
  size: 11pt,
)

#show heading: it => {
  set text(font: "New Computer Modern Sans", weight: "bold")
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

// Colors
#let academic-navy = rgb("#1a2332")
#let academic-burgundy = rgb("#8b3a3a")
#let academic-cream = rgb("#faf8f5")
#let academic-charcoal = rgb("#2d3436")

// Code listings
#set raw(
  lang: "lean",
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
)

// Theorem environments
#let theorem_box(body, title: "", accent: academic-burgundy) = {
  set block(spacing: 0.8em)
  block(
    fill: academic-cream,
    inset: (left: 12pt, right: 12pt, top: 8pt, bottom: 8pt),
    radius: 2pt,
    stroke: (left: 2pt, rest: accent),
    width: 100%,
    [
      #set text(weight: "bold", fill: accent, size: 9pt)
      #title
      #h(0.3em)
      #set text(weight: "regular", fill: academic-charcoal)
      #body
    ]
  )
}

// Chapter title page
#let chapter_title(chapter_num: auto, title: "", epigraph: none) = {
  [
    #pagebreak(weak: true)

    #align(center)[
      #set text(
        font: "New Computer Modern Sans",
        size: 72pt,
        weight: "light",
        fill: rgb("#e8e4dc")
      )
      #if chapter_num != auto {
        roman(chapter_num)
      } else {
        ""
      }
    ]

    #align(center)[
      #set text(
        font: "New Computer Modern Sans",
        size: 28pt,
        weight: "bold",
        fill: academic-navy
      )
      #title
    ]

    #v(1cm)
    #align(center)[
      line(length: 20%, stroke: 1.5pt, rest: academic-burgundy)
    ]

    #if epigraph != none {
      #v(2cm)
      #align(center)[
        #set text(
          font: "New Computer Modern Roman",
          size: 10pt,
          style: "italic",
          fill: rgb("#666")
        )
        #epigraph
      ]
    }

    #v(2cm)
  ]
}

// Title page
#let title_page() = [
  #pagebreak(weak: true)
  #set align(center)

  #v(4cm)
  #set text(
    font: "New Computer Modern Sans",
    size: 56pt,
    weight: "light",
    fill: academic-navy,
  )
  [CLAIR]

  #v(0.8cm)

  #set text(
    font: "New Computer Modern Sans",
    size: 18pt,
    fill: academic-charcoal,
    width: 12cm
  )
  [Comprehensible LLM AI Intermediate Representation]

  #v(0.3cm)

  #set text(
    font: "New Computer Modern Roman",
    size: 14pt,
    style: "italic",
    fill: rgb("#666")
  )
  [A Formalization of Epistemic Reasoning for Artificial Intelligence]

  #v(4cm)

  #v(0.5cm)
  line(length: 15%, stroke: 2pt, rest: academic-burgundy)
  #v(0.5cm)

  #set text(
    font: "New Computer Modern Roman",
    size: 13pt
  )
  [Igal Tabachnik]

  #v(0.3cm)

  #set text(
    font: "New Computer Modern Roman",
    size: 11pt,
    fill: rgb("#666")
  )
  [Igal Tabachnik]

  #v(2cm)

  #set text(
    font: "New Computer Modern Roman",
    size: 10pt,
    style: "italic",
    fill: rgb("#999")
  )
  [An exploration of how an AI system reasons about its own reasoning]

  #v(2cm)

  #set text(
    font: "New Computer Modern Roman",
    size: 12pt,
    fill: academic-charcoal
  )
  [January 2026]

  #pagebreak()
]

// Abstract page
#let abstract_page() = [
  #pagebreak(weak: true)

  #set align(left)

  #align(center)[
    #set text(
      font: "New Computer Modern Sans",
      size: 22pt,
      weight: "bold",
      fill: academic-navy
    )
    [Abstract]
  ]

  #v(1.5cm)

  #set par(
    justify: true,
    first-line-indent: 1.2em
  )

  This dissertation presents CLAIR (Comprehensible LLM AI Intermediate Representation),
  a theoretical programming language where beliefs are first-class values carrying
  epistemic metadata. Unlike traditional approaches that treat uncertainty probabilistically,
  CLAIR introduces #italic[confidence] as a measure of epistemic commitment that admits
  paraconsistent reasoning, #italic[justification] as a directed acyclic graph with labeled
  edges supporting defeasible inference, and #italic[invalidation conditions] that explicitly
  track when beliefs should be reconsidered.

  #v(0.8em)

  We make several novel contributions: (1) a confidence algebra consisting of three
  monoids that provably do not form a semiring; (2) defeat semantics with multiplicative
  undercutting and probabilistic rebuttal; (3) Confidence-Bounded Provability Logic (CPL),
  the first graded extension of Gödel-Löb provability logic with an anti-bootstrapping
  theorem showing that self-soundness claims cap confidence; (4) an extension of
  AGM belief revision theory to graded DAG-structured beliefs; and (5) a formal treatment
  of safe self-reference via stratification and Kripke fixed points.

  #v(0.8em)

  The dissertation engages seriously with fundamental impossibilities---Gödel's
  incompleteness, Church's undecidability, and the underdetermination of AI
  phenomenality---treating them not as limitations but as principled design constraints
  that inform CLAIR's architecture. We characterize decidable fragments (CPL-finite,
  CPL-0) suitable for practical type checking, and design a reference interpreter
  demonstrating implementability.

  #v(0.8em)

  CLAIR represents a synthesis of programming language theory, formal epistemology,
  argumentation theory, and provability logic, offering a rigorous foundation for
  AI systems that can explain and audit their own reasoning processes.

  #pagebreak()
]

// Table of contents
#let toc_page() = [
  #pagebreak(weak: true)

  #align(center)[
    #set text(
      font: "New Computer Modern Sans",
      size: 22pt,
      weight: "bold",
      fill: academic-navy
    )
    [Contents]
  ]

  #v(1.5cm)

  #outline(
    title: none,
    indent: auto,
  )

  #pagebreak()
]

// Quote style
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

// List marker styling
#show list.item.where(depth: 1): it => {
  set text(fill: academic-burgundy, weight: "bold")
  it.body
}

#set list(spacing: 0.5em)

// Exported functions
#let chapter(num, title, epigraph: none) = [
  counter(chapter).update(num)
  chapter_title(chapter_num: num, title: title, epigraph: epigraph)
]

#let theorem(body, title: "Theorem") = {
  theorem_box(body, title: title)
}

#let definition(body, title: "Definition") = {
  theorem_box(body, title: title, accent: rgb("#4a6fa5"))
}

#let example(body, title: "Example") = {
  theorem_box(body, title: title, accent: rgb("#6b8e23"))
}

#let lemma(body, title: "Lemma") = {
  theorem_box(body, title: title)
}

#let corollary(body, title: "Corollary") = {
  theorem_box(body, title: title)
}

#let proposition(body, title: "Proposition") = {
  theorem_box(body, title: title)
}

#let proof(body) = [
  #set text(size: 10pt)
  #set block(above: 0.5em, below: 0.5em)
  #h(0.3em, weak: true)
  _Proof._ #body ∎
]
