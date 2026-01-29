# Theoretical Foundations of CLAIR

A reading guide to the theoretical work underpinning CLAIR.

## Core Logic & Self-Reference

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **Provability Logic (GL)** | Boolos, *The Logic of Provability* (1993) | Foundation for safe self-reference; Löb's theorem constrains what a system can believe about itself |
| **Gödel's Incompleteness Theorems** | Gödel (1931) | CLAIR cannot prove its own soundness; tracking vs. proving paradigm |
| **Löb's Theorem** | Löb (1955) | Graded Löb axiom (`c → c²`) prevents confidence bootstrapping |
| **Tarski's Undefinability** | Tarski (1936) | Truth predicate cannot be defined within the same language; motivates stratification |

## Epistemology & Belief

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **Formal Epistemology** | Hendricks & Symons, *Formal Philosophy* | Graded belief, justification structure |
| **Epistemic Modal Logic** | Hintikka, *Knowledge and Belief* (1962) | `Kₐ P` and `Bₐ P` operators; graded belief `B_{a,c} P` |
| **Subjective Logic** | Jøsang, *Subjective Logic* (2016) | Belief, disbelief, uncertainty masses; opinion fusion |
| **AGM Belief Revision** | Alchourrón, Gärdenfors, Makinson (1985) | How to revise beliefs rationally; CLAIR extends to graded DAG beliefs |
| **Ranking Theory** | Spohn, *The Laws of Belief* (2012) | Ordinal confidence rankings; epistemic entrenchment |

## Argumentation & Defeasible Reasoning

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **Defeasible Reasoning** | Pollock, *Cognitive Carpentry* (1995) | Undercutters vs. rebutters; defeat semantics |
| **Abstract Argumentation** | Dung, "On the acceptability of arguments" (1995) | Attack relations, grounded semantics |
| **Weighted Argumentation** | Amgoud & Ben-Naim; Bonzon et al. | Confidence-weighted argument strength |
| **IBIS/QOC** | Rittel & Webber; MacLean et al. | Design rationale; issue-based information systems |

## Truth Maintenance & Dependency

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **Truth Maintenance Systems** | Doyle, "A truth maintenance system" (1979) | Dependency-directed backtracking |
| **ATMS** | de Kleer, "An assumption-based TMS" (1986) | Assumption-based reasoning; justification tracking |
| **Database Provenance** | Buneman, Khanna, Tan (2001) | Where-provenance, why-provenance |

## Justification Logic

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **Justification Logic** | Artemov, "Explicit provability" (2001) | Explicit justification terms `t : φ` |
| **Graded Justification** | Milnikel (2014); Fan & Liau (2015) | Uncertainty in justification terms |
| **Logic of Proofs (LP)** | Artemov (1994) | Internalized proof predicates |

## Paraconsistent & Many-Valued Logic

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **Paraconsistent Logic** | Priest, *In Contradiction* (2006) | Reasoning with contradictions without explosion |
| **Many-Valued Modal Logic** | Fitting (1992); Bou et al. | Graded modalities; fuzzy accessibility |
| **Transitive Fuzzy Modal Logic** | Vidal (2019) | Undecidability results that apply to CPL |

## Type Theory (Conceptual Influence)

| Topic | Key Work | Why It Matters |
|-------|----------|----------------|
| **BHK Interpretation** | Brouwer, Heyting, Kolmogorov | Constructive evidence; beliefs have witnesses |
| **Information Flow Types** | Myers & Liskov (1997) | Tracking metadata through computation |
| **Refinement Types** | Rondon, Kawaguchi, Jhala (Liquid Types) | Constraints on values |

---

## Recommended Reading Order

### Start here (most directly relevant)

1. **Boolos, *The Logic of Provability*** — chapters on GL and Löb's theorem
2. **Pollock, *Cognitive Carpentry*** — defeaters and justification
3. **Jøsang, *Subjective Logic*** — uncertainty algebra

### Then

4. **de Kleer on ATMS** — dependency tracking
5. **Dung on argumentation** — attack semantics
6. **AGM original paper** — belief revision postulates

### For depth

7. Artemov on Justification Logic
8. Priest on paraconsistent logic
9. Hintikka on epistemic logic

---

## Quick Reference: What CLAIR Uses From Each

| Foundation | CLAIR Feature |
|------------|---------------|
| GL/Löb | Stratification levels, Löb discount (`c²`) |
| Subjective Logic | Confidence in `[0,1]`, but NOT three-component opinions |
| Pollock | Undercut (`c × (1-d)`) and rebut (`c_for/(c_for + c_against)`) |
| ATMS | DAG structure, dependency tracking |
| AGM | Revision on edges, Recovery correctly fails |
| Epistemic Logic | Graded belief operators |
| Paraconsistent | Both `P` and `¬P` can have low confidence |

---

## Full Bibliography

### Books

- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press.
- Hintikka, J. (1962). *Knowledge and Belief: An Introduction to the Logic of the Two Notions*. Cornell University Press.
- Jøsang, A. (2016). *Subjective Logic: A Formalism for Reasoning Under Uncertainty*. Springer.
- Pollock, J. L. (1995). *Cognitive Carpentry: A Blueprint for How to Build a Person*. MIT Press.
- Priest, G. (2006). *In Contradiction: A Study of the Transconsistent* (2nd ed.). Oxford University Press.
- Spohn, W. (2012). *The Laws of Belief: Ranking Theory and Its Philosophical Applications*. Oxford University Press.

### Papers

- Alchourrón, C. E., Gärdenfors, P., & Makinson, D. (1985). On the logic of theory change: Partial meet contraction and revision functions. *Journal of Symbolic Logic*, 50(2), 510-530.
- Artemov, S. (1994). Logic of proofs. *Annals of Pure and Applied Logic*, 67(1-3), 29-59.
- Artemov, S. (2001). Explicit provability and constructive semantics. *Bulletin of Symbolic Logic*, 7(1), 1-36.
- Buneman, P., Khanna, S., & Tan, W. C. (2001). Why and where: A characterization of data provenance. *ICDT 2001*, 316-330.
- de Kleer, J. (1986). An assumption-based TMS. *Artificial Intelligence*, 28(2), 127-162.
- Doyle, J. (1979). A truth maintenance system. *Artificial Intelligence*, 12(3), 231-272.
- Dung, P. M. (1995). On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games. *Artificial Intelligence*, 77(2), 321-357.
- Fan, T. F., & Liau, C. J. (2015). A logic for reasoning about justified uncertain beliefs. *IJCAI 2015*, 2948-2954.
- Fitting, M. (1992). Many-valued modal logics. *Fundamenta Informaticae*, 15(3-4), 235-254.
- Gödel, K. (1931). Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I. *Monatshefte für Mathematik und Physik*, 38, 173-198.
- Löb, M. H. (1955). Solution of a problem of Leon Henkin. *Journal of Symbolic Logic*, 20(2), 115-118.
- Milnikel, R. S. (2014). The logic of uncertain justifications. *Annals of Pure and Applied Logic*, 165(1), 305-315.
- Myers, A. C., & Liskov, B. (1997). A decentralized model for information flow control. *SOSP 1997*, 129-142.
- Tarski, A. (1936). The concept of truth in formalized languages. In *Logic, Semantics, Metamathematics* (1956), 152-278.
- Vidal, A. (2019). On transitive modal many-valued logics. *Fuzzy Sets and Systems*, 407, 97-114.
