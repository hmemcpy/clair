#heading(level: 1)[Introduction]
#label("ch:introduction")

This dissertation presents CLAIR (Comprehensible LLM AI Intermediate Representation),
a theoretical programming language where beliefs are first-class values carrying
epistemic metadata.

#heading(level: 2)[Motivation]

Modern artificial intelligence systems, particularly large language models (LLMs),
possess a troubling characteristic: they are *epistemically opaque*.

#heading(level: 2)[Research Questions]

This dissertation addresses four central research questions:

1. Can beliefs be formalized as typed values?
2. What is the structure of justification?
3. What self-referential beliefs are safe?
4. How should beliefs be revised in response to new information?

#heading(level: 2)[Thesis Statement]

This dissertation defends the following thesis:

#block[
  *Thesis.* Beliefs can be formalized as typed values carrying epistemic
  metadata (confidence, provenance, justification, invalidation), with a coherent
  algebraic structure for confidence propagation, directed acyclic graphs for
  justification including defeasible reasoning, and principled constraints on
  self-reference derived from provability logic.
]

#heading(level: 2)[Contributions]

This dissertation makes the following novel contributions:
