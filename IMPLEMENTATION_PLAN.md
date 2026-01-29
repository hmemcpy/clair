# Implementation Plan: CLAIR Thesis Remediation

> **Scope**: Full remediation | **Risk**: Balanced | **Validation**: Full verification (Lean + Typst + checklist + examples)

## Summary

Address all concerns from the PhD-style review to bring the CLAIR dissertation to defensible PhD standard. Work proceeds in phases: bibliography fixes, semantic foundations, language specification, verification artifacts, implementation, evaluation, and polish. Target format is Typst.

---

## Phase 1: Bibliography & Immediate Fixes

- [ ] **1.1 Add missing citations to references.bib** - Add all 30 missing citation keys with proper BibTeX entries
- [ ] **1.2 Fix citation key mismatches** - Map `doyle1979` → `doyle1979truth` and similar
- [ ] **1.3 Verify Typst compiles** - Run `typst compile` with no undefined references

## Phase 2: Semantic Foundations (Chapter 3)

- [ ] **2.1 Add "Semantic Commitments" section** - Define what confidence IS (calibrated reliability), independence assumptions, required properties, falsifiability
- [ ] **2.2 Remove "0.5 = ignorance" claims** - Search and remove all assertions that 0.5 represents ignorance
- [ ] **2.3 Fix rebut normalization** - Document that c_for/(c_for+c_against) collapses uncertainty, add discussion of limitations
- [ ] **2.4 Add dependency-aware aggregation discussion** - Document when independence assumption breaks, suggest bounds/alternatives

## Phase 3: Language Specification (New Appendix E)

- [ ] **3.1 Create appendix-E-language-spec.typ** - New appendix file with proper Typst structure
- [ ] **3.2 Write complete BNF grammar** - Types, expressions, justifications, confidence literals
- [ ] **3.3 Write complete typing rules** - All judgment forms (Γ ⊢ e : A @c)
- [ ] **3.4 Write operational semantics** - Small-step reduction rules
- [ ] **3.5 Document well-formedness constraints** - DAG requirement, stratification rules
- [ ] **3.6 Add to main dissertation** - Include new appendix in clair-dissertation.typ

## Phase 4: DAG & Cycle Handling (Chapter 4)

- [ ] **4.1 Add well-formedness section** - Define isAcyclic or hasStratifiedCycles requirement
- [ ] **4.2 Formalize fixed-point semantics** - Kleene iteration, continuity, existence theorem
- [ ] **4.3 Add convergence bounds** - When all weights < λ, convergence in O(log(1/ε)/log(1/λ))
- [ ] **4.4 Clarify DAG-only vs cyclic semantics** - State which is primary, when cycles allowed

## Phase 5: CPL Soundness (Chapter 5)

- [ ] **5.1 Clarify axiom status** - Graded Löb is DESIGN AXIOM, not semantic theorem
- [ ] **5.2 List modal axioms explicitly** - K ✓, 4 ✓, GL ✓, T ✗ with explanations
- [ ] **5.3 Prove consistency** - Exhibit non-trivial model satisfying CPL axioms
- [ ] **5.4 Document what "conservative over GL" means** - If claimed, prove; if not, remove claim

## Phase 6: Verification Artifacts (Chapter 9 + Appendix A)

- [ ] **6.1 Verify Lean builds cleanly** - Run `cd formal/lean && lake build`, fix any warnings
- [ ] **6.2 Add build instructions to Appendix A** - Clone, install deps, build, run
- [ ] **6.3 Create theorem inventory** - Table of all theorems with status (machine-checked vs sketch)
- [ ] **6.4 Downgrade unproven claims** - Change "Theorem" to "Conjecture" where proof incomplete
- [ ] **6.5 Add CI configuration** - lakefile or GitHub Actions for reproducible builds

## Phase 7: Haskell Implementation

- [ ] **7.1 Create implementation/haskell directory** - Project structure with cabal/stack
- [ ] **7.2 Implement Confidence module** - Oplus, multiplication, undercut, rebut
- [ ] **7.3 Implement Syntax module** - AST types matching Lean definitions
- [ ] **7.4 Implement Parser** - Parse CLAIR surface syntax
- [ ] **7.5 Implement TypeChecker** - Bidirectional type checking with confidence
- [ ] **7.6 Implement Evaluator** - Small-step or big-step evaluation
- [ ] **7.7 Create test suite** - Unit tests for all operations
- [ ] **7.8 Port example programs** - hello-world.clair, auth.clair
- [ ] **7.9 Document in Chapter 10** - Architecture, key functions, REPL examples

## Phase 8: Empirical Evaluation (New Chapter 14)

- [ ] **8.1 Create chapter 14-evaluation.typ** - New chapter with evaluation framework
- [ ] **8.2 Design evaluation framework** - Tasks, baselines, metrics
- [ ] **8.3 Create evaluation prompts** - Few-shot CLAIR prompts for each task
- [ ] **8.4 Run GSM8K experiments** - Math reasoning with CLAIR vs CoT
- [ ] **8.5 Run HotpotQA experiments** - Multi-hop QA
- [ ] **8.6 Run FOLIO experiments** - Logical reasoning
- [ ] **8.7 Compute calibration metrics** - Brier score, ECE, reliability diagrams
- [ ] **8.8 Write results section** - Tables, figures, analysis
- [ ] **8.9 Design user study protocol** - If resources permit
- [ ] **8.10 Add chapter to dissertation** - Include in clair-dissertation.typ

## Phase 9: Theorem Labeling Audit

- [ ] **9.1 Search for "likely" in theorems** - Identify all conjectural statements
- [ ] **9.2 Search for "sketch" in proofs** - Identify incomplete proofs
- [ ] **9.3 Relabel as appropriate** - Theorem → Conjecture/Claim where needed
- [ ] **9.4 Add Typst macros** - Distinct styling for Conjecture, Claim, Remark

## Phase 10: Related Work Expansion (Chapter 2)

- [ ] **10.1 Add graded justification logic section** - Milnikel 2014, Fan & Liau 2015, Kokkinis 2018
- [ ] **10.2 Add many-valued modal logic section** - Bou et al. 2011, Vidal 2019, Hájek 1998
- [ ] **10.3 Add weighted argumentation section** - Amgoud & Ben-Naim 2017, Bonzon 2016
- [ ] **10.4 Position CLAIR against each** - How CLAIR differs, why approach preferable

## Phase 11: Foundational Hole Repairs

- [ ] **11.1 Formalize "tracking paradigm"** - Definition with state, update rules, correctness criteria
- [ ] **11.2 Add dependency bounds discussion** - When ⊕ breaks under correlation, alternatives
- [ ] **11.3 Formalize explanation extraction** - How CLAIR traces become human-auditable

## Phase 12: Final Polish & Verification

- [ ] **12.1 Run full Typst compile** - No errors, no undefined references
- [ ] **12.2 Run Lean build** - Clean build, all tests pass
- [ ] **12.3 Run Haskell tests** - All tests pass
- [ ] **12.4 Check against defense questions** - Answer all 10 questions from review
- [ ] **12.5 Update conclusion** - Reflect completed work
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
- `formal/dissertation/references.bib` - Add 30 citations
- `formal/dissertation/chapters/02-background.typ` - Related work
- `formal/dissertation/chapters/03-confidence.typ` - Semantic commitments
- `formal/dissertation/chapters/04-justification.typ` - Cycle handling
- `formal/dissertation/chapters/05-self-reference.typ` - CPL axiom status
- `formal/dissertation/chapters/09-verification.typ` - Build instructions
- `formal/dissertation/chapters/10-implementation.typ` - Haskell details
- `formal/dissertation/chapters/13-conclusion.typ` - Update
- `formal/dissertation/appendices/A-lean-code.typ` - Theorem inventory
- `formal/dissertation/clair-dissertation.typ` - Add new chapters/appendices

### Files to Create
- `formal/dissertation/appendices/E-language-spec.typ` - Complete grammar
- `formal/dissertation/chapters/14-evaluation.typ` - Empirical evaluation
- `implementation/haskell/` - Reference interpreter
- `tests/` - Test suite

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
