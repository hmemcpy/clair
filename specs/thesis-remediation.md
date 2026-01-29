# CLAIR Thesis Remediation Specification

**Source**: PhD-style external review (`clair_thesis_review.md`)
**Recommendation**: Major revisions required (not pass in current form)
**Overall Score**: 40-50/100

---

## Overview

Address all concerns from the PhD review to bring the CLAIR dissertation to defensible PhD standard. The review identifies 6 major concerns (blocking), 7 foundational holes, 30 missing citations, and requires empirical evaluation.

---

## Requirements

### R1: Fix Bibliography (30 Missing Citations)
Add all 30 missing citation keys to `references.bib`:
- `alchourron1985logic`, `amgoud2017evaluation`, `amgoud2023weighted`
- `artemov2001`, `beklemishev2004provability`, `bonjour1999defense`, `bonjour1999dialectic`
- `bonzon2016comparative`, `bou2011finite`, `caicedo2013godel`
- `condorcet1785essai`, `dekleer1986`, `derijke2000graded`
- `doyle1979`, `fine1972conjunction`, `frankish2016illusionism`
- `garrabrant2016logical`, `godo2003many`, `godo2011fuzzy`
- `goldman2012reliabilism`, `hintikka1962knowledge`, `josang2016`
- `klein2003infinite`, `klein2003regress`, `klein2005infinitism`
- `nagel1974bat`, `pollock2001defeasible`, `tarski1933`
- `van2007dynamic`, `xue2024loeb`

Fix key mismatches (e.g., `doyle1979` → `doyle1979truth`).

### R2: Semantic Foundations for "Confidence"
Add explicit "Semantic Commitments" section to Chapter 3:
1. What confidence IS: Calibrated reliability interpretation
2. Independence assumptions: EXPLICIT conditional independence for ⊕
3. Required properties (axioms)
4. Falsifiability criteria

Remove "0.5 = ignorance" claim (not formalizable with current operators).

### R3: Complete Language Specification
Create Appendix E with:
- Complete BNF/EBNF grammar for CLAIR
- Full typing rules (all judgment forms)
- Operational semantics (small-step rules)
- Well-formedness constraints

### R4: DAG vs Cycles Resolution
Either:
- (A) DAG-only with type checker enforcement, OR
- (B) Full fixed-point semantics with convergence proofs

Add to Chapter 4:
- Explicit well-formedness constraints
- Fixed-point existence/uniqueness theorems
- Convergence bounds

### R5: CPL Soundness Clarification
Clarify in Chapter 5:
- Graded Löb is a DESIGN AXIOM (not semantic theorem)
- Prove consistency (exhibit non-trivial model)
- List modal axioms explicitly (K ✓, 4 ✓, GL ✓, T ✗)

### R6: Verification Artifacts
- Ensure `lake build` runs cleanly
- Add build instructions to Appendix A
- Create theorem inventory (machine-checked vs sketched)
- Downgrade claims where proofs incomplete

### R7: Runnable Implementation
Create Haskell reference interpreter:
- Parser for CLAIR syntax
- Type checker
- Evaluator
- Test suite with examples

### R8: Empirical Evaluation
New Chapter 14 with full evaluation:
- Tasks: GSM8K, HotpotQA, FOLIO, ArgMining
- Baselines: CoT, Self-Consistency, ToT, DSPy
- Metrics: Accuracy, Brier score, ECE, syntax/type validity
- Optional: User study on auditability

### R9: Theorem Labeling
Audit all theorem environments:
- Label conjectures as "Conjecture" not "Theorem"
- Label proof sketches explicitly
- Use Claim/Remark for informal assertions

### R10: Related Work Engagement
Engage with overlapping literature in Chapter 2:
- Graded justification logics (Milnikel 2014, Fan & Liau 2015)
- Many-valued modal logic (Bou et al. 2011, Vidal 2019)
- Weighted argumentation (Amgoud & Ben-Naim 2017)

### R11: Foundational Hole Repairs
- **Hole A**: Add dependency model or bounds for non-independent evidence
- **Hole B**: Drop "0.5 = ignorance" (covered in R2)
- **Hole C**: Add uncertainty preservation to rebut normalization
- **Hole D**: Formalize acyclicity constraints (covered in R4)
- **Hole E**: Prove CPL consistency (covered in R5)
- **Hole F**: Fix theorem labeling (covered in R9)
- **Hole G**: Formalize "tracking paradigm" with state/update rules

---

## Constraints

- **Format**: Typst primary (`.typ` files)
- **Lean**: Must build cleanly with `lake build`
- **Haskell**: Must compile and pass tests
- **PDF**: Must compile with no undefined references
- **Preserve**: Core theoretical framework and existing proofs

---

## Edge Cases

- Some citations may have alternate spellings - search thoroughly before adding
- Lean proofs may need Mathlib updates
- Some "theorems" may need to become conjectures if proofs cannot be completed
- Evaluation may be limited by API costs/access

---

## Out of Scope

- LaTeX format (Typst primary per user decision)
- Production-quality interpreter (reference implementation sufficient)
- Full user study (framework design + pilot acceptable if resources limited)
- Multi-agent protocols beyond Chapter 8 foundation
