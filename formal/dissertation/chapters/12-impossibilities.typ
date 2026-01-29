// Chapter 12: Impossibilities

#import "../layout.typ": *

#chapter(12, "Impossibilities")

#heading(level: 2)[Engaging with Gödel, Church, and Fundamental Limits]

The classical impossibility results are not obstacles but principled constraints that inform CLAIR's design. A theory of AI reasoning that doesn't take these results seriously is building on sand.

Gödel's first incompleteness theorem implies there exist propositions G such that believes("CLAIR", G, c) and not provable(G) and actually_true(G). The Gödel sentence G_CLAIR := neg provable(G_CLAIR) is true but unprovable. CLAIR's response is explicit indexing: believes("CLAIR", forall p. godelian(p), 0.95).

Gödel's second theorem implies not provable(Consistent(CLAIR)). CLAIR cannot have maximum confidence in its own consistency: forall c. believes("CLAIR", Consistent(CLAIR), c) implies c < 1.0. Instead, confidence tracks empirical reliability.

Tarski's undefinability theorem shows truth cannot be defined within the same language. CLAIR implements semantic stratification: stratum(n) contains propositions about stratum(n-1), with Truth predicates always one stratum above their target.

Church-Turing undecidability implies not exists algorithm. forall p. decidable(provable(p)). While full CLAIR is undecidable, we identify decidable fragments: CPL-0 (confidence in {0,1}), CPL-finite (finite confidence sets), and Horn-CLAIR.

The halting problem implies perfect self-prediction is impossible. CLAIR achieves bounded self-prediction: forall p, t, n. predicts_n(halts_before(CLAIR, p, t, n)).

Rice's theorem states all non-trivial semantic properties are undecidable. CLAIR achieves pragmatic decidability through type systems, bounded proof search, and approximation.

These constraints don't limit usefulness---they enable honest reasoning about limitations. The tragic vision of formal epistemology: we can reason, but not about everything; we can know, but not with certainty; we can prove, but not all truths. In acknowledging these limits, we achieve more honest and therefore more reliable reasoning.
