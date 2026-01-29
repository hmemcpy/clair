// Chapter 8: Multi-Agent Epistemic Reasoning

#import "../layout.typ": *

#chapter(8, "Multi-Agent Epistemic Reasoning")

#heading(level: 2)[The Social Dimension of Knowledge]

Multi-agent CLAIR extends the single-agent framework with indexed belief operators for mutual, distributed, and common knowledge. The key innovation is treating confidence as a social quantity that aggregates across agents through testimony and trust dynamics.

The framework introduces B_a(p, c) for agent beliefs, E_G(p, c) for "everyone believes," D_G(p, c) for distributed knowledge, and C_G(p, c) for common knowledge. Common knowledge is characterized as a fixed point: C_G(p, c) := E_G(p and C_G(p, c), c), with approximation levels providing tractable approximations.

Trust dynamics follow Rescorla-Wagner style updates: reliability adjusts incrementally toward observed accuracy. When testimony conflicts, agents arbitrate based on relative reliability, source diversity, and argument quality.

The Agree-to-Disagree theorem extends to graded common knowledge: if agents have common priors and graded common knowledge of posteriors above threshold 0.5, their confidences are bounded close. Coalitions form with epistemic solidarity, joint justification, and collective invalidation.

Multi-agent justification DAGs enable transitive defeat across agent boundaries, creating a unified framework for social epistemology.
