# Implementation Plan: CLAIR Thesis Remediation

> **Scope**: Full remediation | **Risk**: Balanced | **Validation**: Full verification (Lean + Typst + checklist + examples)

## Gap Analysis Summary

### What's Already Done (Verified)
- **Lean formalization**: Builds cleanly, ~95% machine-checked (only 5 sorries in substitution/weakening lemmas)
- **Typst compilation**: Compiles with no errors
- **13 dissertation chapters**: All have substantial content (not placeholders)
- **Chapter 3 semantic commitments**: Already EXISTS and explicitly rejects "0.5 = ignorance"
- **76 citations in references.bib**: Many "missing" citations are actually key mismatches

### What's Actually Missing
- **Appendix C**: Placeholder content (lorem ipsum) - needs real content
- **Appendix D**: COMPLETED (glossary with term definitions, notation table, and acronym list)
- **Appendices A-B**: Have substantial real content (verified during this iteration)
- **Appendix E (language spec)**: Does not exist - needs grammar, typing rules, operational semantics
- **Chapter 14 (evaluation)**: Does not exist - needs empirical results
- **Haskell implementation**: Does not exist - only design discussion in Chapter 10
- **~15 truly missing citations**: After accounting for key mismatches

---

## Phase 1: Bibliography Fixes (HIGH PRIORITY - Blocking)

### Citation Key Mismatches (8 fixes)
These citations EXIST but are cited with wrong keys in text:

- [x] **1.1 Fix tarski1933 → tarski1933concept** - Update all @tarski1933 citations (DONE)
- [x] **1.2 Fix doyle1979 → doyle1979truth** - Update all @doyle1979 citations (DONE)
- [x] **1.3 Fix dekleer1986 → dekleer1986assumption** - Update all @dekleer1986 citations (DONE)
- [x] **1.4 Fix josang2016 → josang2016subjective** - Update all @josang2016 citations (DONE)
- [x] **1.5 Fix condorcet1785essai → condorcet1785essay** - Update all citations (DONE)
- [x] **1.6 Fix artemov2001 → artemov2001explicit** - Update all @artemov2001 citations (DONE)
- [x] **1.7 Fix nagel1974bat → nagel1974like** - Update all @nagel1974bat citations (DONE - comment only)
- [x] **1.8 Fix van2007dynamic → ditmarsch2007dynamic** - Update all @van2007dynamic citations (DONE)

### Additional Key Mismatches Fixed During Implementation:
- [x] **1.2a Fix alchourron1985logic → agm1985logic** - Update all @alchourron1985logic citations (DONE)
- [x] **1.2b Fix caicedo2013godel → caicedo2013finite** - Update all @caicedo2013godel citations (DONE)
- [x] **1.2c Fix bou2011finite → bou2011minimum** - Update all @bou2011finite citations (DONE)
- [x] **1.2d Fix bonjour1999dialectic → bonjour1999defense** - Standardize to bonjour1999defense (DONE)
- [x] **1.2e Remove klein2003infinite, klein2005infinitism, klein2003regress** - Use only klein1999human (DONE)

### Additional Fixes During Iteration (2026-01-29):
- [x] **2.15 Fix Appendix B function call syntax** - Changed `#theorem(body, title: "...")[...]` to `#theorem[*Title.* ...]` (DONE)
- [x] **2.16 Fix layout.typ stroke parameter** - Changed `paint: accent` to `rest: accent` in theorem_box (DONE)
- [x] **2.17 Implement Appendix D: Glossary** - Complete glossary with term definitions, notation table, and acronym list (DONE)
- [x] **2.18 Fix Appendix D table code mode issues** - Fixed #sym[...] and underscore issues in table cells (DONE 2026-01-29)

### Truly Missing Citations (~15 to add to references.bib)

- [x] **1.9 Add hintikka1962knowledge** - Hintikka's "Knowledge and Belief" (foundational epistemic logic) (DONE)
- [x] **1.10 Add garrabrant2016logical** - Garrabrant et al. "Logical Induction" (MIRI) (DONE)
- [x] **1.11 Add amgoud2017evaluation** - Amgoud & Ben-Naim "Evaluation of Arguments in Weighted Bipolar Graphs" (ECSQARU 2017) (DONE 2026-01-29)
- [x] **1.12 Add amgoud2023parameterised** - Amgoud, Doder & Vesic "Parameterised Gradual Semantics Dealing with Varied Degrees of Compensation" (IJCAI 2023) (DONE 2026-01-29)
- [ ] **1.13 Add beklemishev2004provability** - Beklemishev "Provability algebras and proof-theoretic ordinals"
- [ ] **1.14 Add bonjour1999defense** - BonJour "The Dialectic of Foundationalism and Coherentism"
- [ ] **1.15 Add bonzon2016comparative** - Bonzon et al. "Comparative analysis of weighted argumentation"
- [ ] **1.16 Add derijke2000graded** - de Rijke "Graded Modalities"
- [ ] **1.17 Add fine1972conjunction** - Fine "Propositional Quantifiers in Modal Logic"
- [ ] **1.18 Add frankish2016illusionism** - Frankish "Illusionism as a Theory of Consciousness"
- [ ] **1.19 Add godo2003many** - Godo et al. "Many-valued modal logics"
- [ ] **1.20 Add godo2011fuzzy** - Godo et al. "Fuzzy modal logics over finite residuated lattices"
- [ ] **1.21 Add goldman2012reliabilism** - Goldman "Reliabilism" (Stanford Encyclopedia)
- [ ] **1.22 Add klein2005infinitism** - Klein "Infinitism is the Solution to the Regress Problem"
- [ ] **1.23 Add pollock2001defeasible** - Pollock "Defeasible Reasoning and Degrees of Justification"
- [ ] **1.24 Add xue2024loeb** - Xue et al. "Graded Löb logic" (if exists; may be conjectural)

### Verification

- [x] **1.25 Run typst compile with bibliography** - Verify no undefined references remain (DONE - compiles cleanly)
- [ ] **1.26 Cross-check all 30 originally flagged citations** - Ensure each is resolved (PARTIAL - key mismatches fixed, missing citations remain)

---

## Phase 2: Appendix Content (HIGH PRIORITY - Currently Placeholder)

All appendices are lorem ipsum placeholders. Need real content.

### Appendix A: Lean Code

- [x] **2.1 Add Lean project structure overview** - Module organization, dependencies (DONE)
- [x] **2.2 Add build instructions** - `lake build`, prerequisites, expected output (DONE)
- [x] **2.3 Create theorem inventory table** - List all 50+ theorems with status (proven/sorry) (DONE)
- [x] **2.4 Add key proof excerpts** - Confidence operations, monad laws, stratification (DONE)
- [x] **2.5 Document the 5 sorry lemmas** - Why deferred, impact on soundness claims (DONE)

### Appendix B: Interpreter

- [x] **2.6 Add interpreter architecture diagram** - Parser → TypeChecker → Evaluator pipeline (DONE)
- [x] **2.7 Document Lean interpreter code** - The existing Semantics/Eval.lean with fuel (DONE)
- [x] **2.8 Add example program walkthroughs** - Step-by-step evaluation of hello-world.clair (DONE)

### Appendix C: Additional Proofs

- [x] **2.9 Add detailed proof of DAG necessity** - Full formal argument (DONE 2026-01-29)
- [x] **2.10 Add CPL consistency proof sketch** - Non-trivial model construction (DONE 2026-01-29)
- [x] **2.11 Add defeat composition proofs** - Undercut and rebut algebra (DONE 2026-01-29)

### Appendix D: Glossary

- [x] **2.12 Create term definitions** - Confidence, Justification, Provenance, Invalidation, etc. (DONE)
- [x] **2.13 Add notation table** - ⊕, ⊗, □_c, etc. with meanings (DONE)
- [x] **2.14 Add acronym list** - CLAIR, CPL, AGM, DAG, etc. (DONE)

---

## Phase 3: Language Specification (Appendix E - New)

Formal grammar and semantics do not exist as a standalone readable spec.

- [ ] **3.1 Create appendices/E-language-spec.typ** - New file with proper Typst structure
- [ ] **3.2 Write complete BNF/EBNF grammar** - Types: `T ::= Nat | Bool | String | Unit | Belief<T> | ...`
- [ ] **3.3 Write expression grammar** - `e ::= x | λx:T.e | e e | belief(v,c,p,j,i) | ...`
- [ ] **3.4 Write typing judgment rules** - All 16 rules: `Γ ⊢ e : A @ c` format with inference rules
- [ ] **3.5 Write operational semantics** - Small-step reduction: `e → e'` rules
- [ ] **3.6 Document well-formedness constraints** - DAG requirement, stratification, confidence bounds
- [ ] **3.7 Add to main dissertation** - Update clair-dissertation.typ to include E-language-spec.typ

---

## Phase 4: Semantic Foundations Refinement (Chapter 3)

Chapter 3 already has semantic commitments and rejects "0.5 = ignorance". Minor refinements needed.

- [ ] **4.1 Verify calibration definition** - Add explicit definition of "calibrated reliability"
- [ ] **4.2 Add independence assumptions discussion** - When ⊕ is valid, when it breaks
- [ ] **4.3 Add falsifiability section** - What would falsify CLAIR as better than alternatives?
- [ ] **4.4 Document rebut normalization limitation** - c_for/(c_for+c_against) collapses absolute strength

---

## Phase 5: CPL Soundness Clarification (Chapter 5)

- [ ] **5.1 Add explicit axiom status statement** - "Graded Löb is a DESIGN AXIOM, not semantic theorem"
- [ ] **5.2 List modal axioms with status** - K ✓, 4 ✓, GL ✓, T ✗ with explanations
- [ ] **5.3 Add consistency proof** - Exhibit non-trivial model satisfying CPL axioms
- [ ] **5.4 Clarify "conservative over GL"** - Define precisely what this means, prove or remove

---

## Phase 6: DAG/Cycle Handling (Chapter 4)

- [ ] **6.1 Add well-formedness constraint section** - Formal definition of isAcyclic predicate
- [ ] **6.2 Formalize fixed-point semantics** - Kleene iteration with Banach fixed-point theorem
- [ ] **6.3 Add convergence bounds** - When |weights| < λ < 1, convergence in O(log(1/ε)/log(1/λ)) steps
- [ ] **6.4 State DAG-only vs cyclic choice** - Which is primary semantics, when cycles allowed

---

## Phase 7: Haskell Reference Interpreter (NEW - Major)

No Haskell implementation exists. Chapter 10 only discusses design.

- [ ] **7.1 Create implementation/haskell/ directory** - cabal project structure
- [ ] **7.2 Implement CLAIR.Confidence module** - Confidence type, oplus, mult, undercut, rebut
- [ ] **7.3 Implement CLAIR.Syntax module** - AST types matching Lean Expr
- [ ] **7.4 Implement CLAIR.Parser module** - Parse CLAIR surface syntax
- [ ] **7.5 Implement CLAIR.TypeChecker module** - Bidirectional type checking with confidence grades
- [ ] **7.6 Implement CLAIR.Evaluator module** - Small-step or big-step semantics
- [ ] **7.7 Create test suite** - QuickCheck properties, unit tests for all operations
- [ ] **7.8 Port hello-world.clair** - Run through interpreter, verify output
- [ ] **7.9 Port auth.clair** - More complex example
- [ ] **7.10 Add REPL** - Interactive evaluation for demonstration
- [ ] **7.11 Document in Chapter 10** - Architecture, key functions, usage examples
- [ ] **7.12 Add to Appendix B** - Full source code listing

---

## Phase 8: Empirical Evaluation (Chapter 14 - NEW - Major)

No evaluation chapter or empirical results exist.

- [ ] **8.1 Create chapters/14-evaluation.typ** - New chapter with evaluation framework
- [ ] **8.2 Design evaluation methodology** - Tasks, baselines, metrics, hypotheses
- [ ] **8.3 Create GSM8K evaluation prompts** - Few-shot CLAIR prompts for math reasoning
- [ ] **8.4 Create HotpotQA evaluation prompts** - Multi-hop QA with confidence tracking
- [ ] **8.5 Create FOLIO evaluation prompts** - Logical reasoning with justification
- [ ] **8.6 Define baselines** - Chain-of-thought, vanilla prompting, self-consistency
- [ ] **8.7 Run experiments** - Collect accuracy, calibration data
- [ ] **8.8 Compute calibration metrics** - Brier score, ECE, reliability diagrams
- [ ] **8.9 Write results section** - Tables, figures, statistical analysis
- [ ] **8.10 Add chapter to dissertation** - Update clair-dissertation.typ to include 14-evaluation.typ

---

## Phase 9: Theorem Labeling Audit

- [ ] **9.1 Grep for "likely" in theorem bodies** - Find conjectural statements
- [ ] **9.2 Grep for "sketch" in proofs** - Find incomplete proofs
- [ ] **9.3 Grep for "conjecture" already used** - See current labeling practice
- [ ] **9.4 Relabel theorems appropriately** - Theorem → Conjecture/Claim where proof incomplete
- [ ] **9.5 Add Typst macros if needed** - conjecture(), claim() environments

---

## Phase 10: Related Work Expansion (Chapter 2)

- [ ] **10.1 Add graded justification logic section** - Artemov extensions with confidence
- [ ] **10.2 Add many-valued modal logic section** - Bou, Vidal, Hájek connections
- [ ] **10.3 Add weighted argumentation section** - Amgoud & Ben-Naim, Bonzon
- [ ] **10.4 Position CLAIR explicitly** - How it differs from each, why approach chosen

---

## Phase 11: Foundational Hole Repairs

- [ ] **11.1 Formalize "tracking paradigm"** - State representation, update rules, correctness criteria
- [ ] **11.2 Add dependency bounds discussion** - When ⊕ breaks under correlation, interval alternatives
- [ ] **11.3 Document explanation extraction** - How CLAIR traces become human-auditable

---

## Phase 12: Final Polish & Verification

- [ ] **12.1 Run full Typst compile** - No errors, no undefined references
- [ ] **12.2 Run Lean build** - Clean build (accept 5 known sorries)
- [ ] **12.3 Run Haskell tests** - All tests pass
- [ ] **12.4 Verify defense questions answerable** - Check all 10 from review
- [ ] **12.5 Update conclusion (Chapter 13)** - Reflect completed remediation work
- [ ] **12.6 Final proofread** - Grammar, consistency, formatting

---

## Defense Question Checklist

After completion, verify these can be answered:

1. [ ] What is confidence: probability, truth degree, reliability, or something else?
2. [ ] Under what assumptions is ⊕ the correct support aggregator?
3. [ ] Why should undercut multiply by (1-d) rather than another function?
4. [ ] How do you prevent "argument inflation"?
5. [ ] If the justification graph contains cycles, what is the semantics?
6. [ ] Is CPL conservative over GL? What does "conservative" mean?
7. [ ] Is graded Löb sound w.r.t. your semantics?
8. [ ] Why is g(c)=c² the right discount?
9. [ ] Show a concrete scenario where CLAIR prevents overconfident self-bootstrapping.
10. [ ] What would falsify CLAIR as a "better reasoning IR" for LLMs?

---

## File Inventory

### Files to Modify
- `formal/dissertation/references.bib` - Add ~15 citations, verify key usage
- `formal/dissertation/chapters/02-background.typ` - Related work expansion
- `formal/dissertation/chapters/03-confidence.typ` - Semantic refinements
- `formal/dissertation/chapters/04-justification.typ` - DAG/cycle formalization
- `formal/dissertation/chapters/05-self-reference.typ` - CPL axiom status
- `formal/dissertation/chapters/10-implementation.typ` - Haskell documentation
- `formal/dissertation/chapters/13-conclusion.typ` - Update for remediation
- `formal/dissertation/appendices/A-lean-code.typ` - Real content (currently lorem ipsum)
- `formal/dissertation/appendices/B-interpreter.typ` - Real content (currently lorem ipsum)
- `formal/dissertation/appendices/C-proofs.typ` - Real content (currently lorem ipsum)
- `formal/dissertation/appendices/D-glossary.typ` - Real content (currently lorem ipsum)
- `formal/dissertation/clair-dissertation.typ` - Add Chapter 14, Appendix E

### Files to Create
- `formal/dissertation/appendices/E-language-spec.typ` - Complete grammar & semantics
- `formal/dissertation/chapters/14-evaluation.typ` - Empirical evaluation
- `implementation/haskell/clair.cabal` - Haskell project
- `implementation/haskell/src/CLAIR/*.hs` - Implementation modules
- `implementation/haskell/test/Spec.hs` - Test suite

---

## Validation Commands

```bash
# Typst compilation
cd formal/dissertation && typst compile clair-dissertation.typ

# Lean build
cd formal/lean && lake build

# Haskell tests (after Phase 7)
cd implementation/haskell && cabal test

# Check remaining tasks
grep -c "^\- \[ \]" IMPLEMENTATION_PLAN.md || echo 0
```

---

## Priority Order

1. **Phase 1** (Bibliography) - Blocking: undefined references break PDF
2. **Phase 2** (Appendix Content) - Major gap: appendices are placeholders
3. **Phase 3** (Language Spec) - Major gap: no formal grammar exists
4. **Phase 7** (Haskell) - Major gap: no implementation exists
5. **Phase 8** (Evaluation) - Major gap: no empirical results
6. **Phase 4-6** (Semantic refinements) - Polish: chapters exist but need strengthening
7. **Phase 9-11** (Audits) - Polish: cleanup and consistency
8. **Phase 12** (Final) - Verification

---

## Task Count

Total tasks: 89
- Phase 1 (Bibliography): 26 tasks
- Phase 2 (Appendix Content): 14 tasks
- Phase 3 (Language Spec): 7 tasks
- Phase 4 (Semantic Foundations): 4 tasks
- Phase 5 (CPL Soundness): 4 tasks
- Phase 6 (DAG/Cycle): 4 tasks
- Phase 7 (Haskell): 12 tasks
- Phase 8 (Evaluation): 10 tasks
- Phase 9 (Theorem Audit): 5 tasks
- Phase 10 (Related Work): 4 tasks
- Phase 11 (Hole Repairs): 3 tasks
- Phase 12 (Final Polish): 6 tasks
