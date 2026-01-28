# Prior Art and Related Work

This document traces the intellectual lineage of CLAIR's Belief Types.

## 1. Subjective Logic (Jøsang, 1997-present)

### Core Idea
Subjective Logic extends probabilistic logic with explicit uncertainty. Instead of probabilities, it uses "opinions":

```
Opinion ω = (b, d, u, a)

b = belief mass      (confidence it's true)
d = disbelief mass   (confidence it's false)
u = uncertainty mass (don't know)
a = base rate        (prior probability)

Constraint: b + d + u = 1
```

### Key Operations
- **Conjunction**: ω₁ ∧ ω₂ (both true)
- **Disjunction**: ω₁ ∨ ω₂ (at least one true)
- **Deduction**: ω₁ → ω₂ (modus ponens with uncertainty)
- **Abduction**: reverse inference
- **Discounting**: adjusting based on source trust

### Relevance to CLAIR
Our confidence component is a simplified opinion (just belief mass). We could extend to full opinions if needed.

### Key Papers
- Jøsang, "A Logic for Uncertain Probabilities" (2001)
- Jøsang, "Subjective Logic: A Formalism for Reasoning Under Uncertainty" (2016, book)

---

## 2. Truth Maintenance Systems (Doyle, de Kleer, 1979-1986)

### Core Idea
A TMS tracks *why* beliefs are held, not just *what* is believed. Each belief has a justification—a record of its support. When support is removed, beliefs are retracted.

### JTMS (Justification-based TMS, Doyle 1979)
```
Node: a belief
Justification: (IN-list, OUT-list)
  - IN-list: nodes that must be IN (believed) for this to be IN
  - OUT-list: nodes that must be OUT (not believed) for this to be IN

Example:
  Node: use-hs256
  Justification: ({stateless-req, secret-available}, {multi-service})

  "Believe use-hs256 if stateless-req and secret-available are believed,
   and multi-service is NOT believed"
```

When `multi-service` becomes believed, `use-hs256` loses its support and is retracted.

### ATMS (Assumption-based TMS, de Kleer 1986)
Instead of tracking one consistent state, ATMS tracks all possible states simultaneously via "environments" (sets of assumptions).

```
Each belief is labeled with environments:
  use-hs256: {{A1, A2}, {A1, A3}}

  "use-hs256 is believed in environments where (A1∧A2) or (A1∧A3)"
```

### Relevance to CLAIR
- Our justification component is inspired by JTMS justifications
- Our invalidation conditions are similar to OUT-lists
- ATMS's multiple environments could model alternative design choices

### Key Papers
- Doyle, "A Truth Maintenance System" (1979, AI Journal)
- de Kleer, "An Assumption-based TMS" (1986, AI Journal)
- Forbus & de Kleer, "Building Problem Solvers" (1993, textbook with TMS chapters)

---

## 3. Justification Logic (Artemov, 1995-present)

### Core Idea
Standard modal logic has □P ("necessarily P" or "it is known that P"), but gives no account of *why* P is known. Justification Logic adds explicit justification terms:

```
Standard:       □P
Justification:  t : P    ("t is a justification for P")
```

### Justification Terms
```
Terms t ::= c           (constant justification, axiom)
          | x           (variable justification)
          | t · t       (application: if s:(P→Q) and t:P then s·t:Q)
          | t + t       (sum: if t:P then (t+s):P)
          | !t          (proof checker: if t:P then !t:(t:P))
```

### Key Axiom: Application
```
s : (P → Q) → (t : P → (s · t) : Q)

"If s justifies P→Q, and t justifies P, then s·t justifies Q"
```

### Relevance to CLAIR
Our justification composition directly mirrors justification logic's · operator. We have:
```
just(derive b₁, b₂ by r) = rule(r, just(b₁), just(b₂))
```

This is essentially `r · j₁ · j₂` in justification logic notation.

### Key Papers
- Artemov, "Explicit Provability and Constructive Semantics" (2001)
- Artemov & Fitting, "Justification Logic: Reasoning with Reasons" (2019, book)

---

## 4. Provenance in Databases (Green, Tannen, et al., 2007+)

### Core Idea
When querying a database, track *why* each output tuple appears:

```
Query: SELECT name FROM employees WHERE dept = 'eng'
Output: "Alice"

Provenance of "Alice":
  - Which input tuples: employee(Alice, eng)
  - Which query operations: selection (dept='eng'), projection (name)
```

### Types of Provenance
- **Why-provenance**: which input tuples contributed?
- **How-provenance**: what operations produced this?
- **Where-provenance**: which specific input locations?

### Provenance Semirings (Green et al., 2007)
Abstract algebra for provenance. Different semirings give different provenance types:
- Boolean semiring: "did this tuple contribute?" (yes/no)
- Counting semiring: "how many times?"
- Tropical semiring: "with what cost?"
- Lineage semiring: "which specific tuples?"

### Relevance to CLAIR
Our provenance component is essentially lineage provenance for computation (not just queries).

```
prov(derive b₁, b₂ by r) = derived(b₁, b₂)
```

### Key Papers
- Green, Karvounarakis, Tannen, "Provenance Semirings" (PODS 2007)
- Cheney, Chiticariu, Tan, "Provenance in Databases: Why, How, and Where" (2009)

---

## 5. Probabilistic Programming Languages

### Core Idea
Programs that explicitly represent and manipulate probability distributions.

### Examples
- **Church** (Goodman et al., 2008): Scheme with `flip`, `observe`, `query`
- **Stan** (2012): Statistical modeling language
- **Pyro** (2017): Deep probabilistic programming in Python
- **Gen** (2019): Julia-based, emphasis on inference

### Church Example
```scheme
(define (coin-model)
  (let ((fair? (flip 0.9)))           ; prior: 90% chance fair
    (if fair?
        (flip 0.5)                     ; fair coin
        (flip 0.9))))                  ; biased coin

(query
  (coin-model)
  (condition (= (coin-model) #t)))    ; given we saw heads
```

### Relevance to CLAIR
- Probabilistic PLs track uncertainty through computation
- But focused on statistical inference, not epistemic justification
- CLAIR is about reasoning uncertainty, not data uncertainty

### Key Papers
- Goodman et al., "Church: A Language for Generative Models" (2008)
- van de Meent et al., "Introduction to Probabilistic Programming" (2018)

---

## 6. Design Rationale Research (Rittel, Lee, MacLean, 1970-1990s)

### Core Idea
Software design involves decisions. Capture not just *what* was decided, but *why*.

### IBIS (Issue-Based Information Systems, Rittel 1970s)
```
Issue: "How should users authenticate?"
  Position: "Use JWT"
    Argument for: "Stateless, scalable"
    Argument against: "Token size"
  Position: "Use sessions"
    Argument for: "Simple, established"
    Argument against: "Requires server state"
  Resolution: JWT selected
```

### QOC (Questions, Options, Criteria, MacLean 1991)
```
Question: "Authentication method?"
  Option: JWT
    Criterion: Stateless → supports (+)
    Criterion: Simplicity → partial (o)
  Option: Session
    Criterion: Stateless → opposes (-)
    Criterion: Simplicity → supports (+)
```

### DRL (Decision Representation Language, Lee 1991)
Formal language for expressing design rationale with explicit goal structures, alternatives, and criteria.

### Relevance to CLAIR
Our Decision construct is directly inspired by this work:
```
decision auth_method:
  options: [jwt, session]
  criteria: [stateless, simplicity]
  selected: jwt
  rationale: "Stateless requirement dominates"
```

### Key Papers
- Lee, "Extending the Potts & Bruns Model for Recording Design Rationale" (1991)
- MacLean et al., "Questions, Options, and Criteria: Elements of Design Space Analysis" (1991)

---

## 7. Information Flow Type Systems (Myers, Sabelfeld, 1990s-present)

### Core Idea
Types that track security levels (confidentiality, integrity) through computation.

### Example (JIF/Jflow, Myers 1999)
```java
int{Alice→Bob} x;   // Alice owns, Bob can read
int{Alice→*} y;     // Alice owns, public
y = x;              // ERROR: would leak to public
```

### Relevance to CLAIR
- Tracks "metadata" through computation via types
- Provenance is analogous to information flow tracking
- "Where did this value come from?" ≈ "What security level?"

### Key Papers
- Sabelfeld & Myers, "Language-Based Information-Flow Security" (2003)
- Myers, "JFlow: Practical Mostly-Static Information Flow Control" (1999)

---

## 8. Refinement Types (Xi, Pfenning, Rondon, Jhala, 1998-present)

### Core Idea
Types augmented with logical predicates that are statically checked.

### Example (Liquid Haskell)
```haskell
{-@ type Nat = {v:Int | v >= 0} @-}
{-@ type Pos = {v:Int | v > 0} @-}

{-@ div :: Int -> Pos -> Int @-}
div x y = x `quot` y   -- y can't be 0, statically checked
```

### Relevance to CLAIR
- Refinements can encode some constraints we put in natural language
- `(assumes "user_id positive")` → `user_id : Pos`
- But refinements can't capture provenance, justification, or invalidation

### Key Papers
- Xi & Pfenning, "Dependent Types in Practical Programming" (1999)
- Rondon, Kawaguchi, Jhala, "Liquid Types" (2008)
- Vazou et al., "Refinement Types for Haskell" (2014)

---

## 9. Dependent Types and Proof Assistants

### Core Idea
Types can depend on values. Programs can carry proofs.

### The Curry-Howard Correspondence
```
Types      ↔ Propositions
Programs   ↔ Proofs
Evaluation ↔ Proof simplification
```

### Example (Lean 4)
```lean
def div (x : Nat) (y : Nat) (h : y > 0) : Nat := x / y

-- Must provide proof h that y > 0
-- Compiler verifies proof is valid
```

### Relevance to CLAIR
- Could encode some justifications as proofs
- But proofs are about logical truth, not epistemic confidence
- CLAIR extends: programs are beliefs-with-justifications

### Key Systems
- **Coq** (1984+): Calculus of Inductive Constructions
- **Agda** (1999+): Dependently typed functional language
- **Idris** (2007+): Dependent types for general programming
- **Lean** (2013+): Interactive theorem prover, increasingly practical

### Key Papers
- Coquand & Huet, "The Calculus of Constructions" (1988)
- The Univalent Foundations Program, "Homotopy Type Theory" (2013)

---

## 10. Effect Systems (Gifford, Lucassen, 1986+)

### Core Idea
Types that track computational effects (IO, state, exceptions).

### Example
```
read : () ->{IO} String        -- performs IO
pure : Int -> Int              -- no effects
comp : () ->{IO, State} Int    -- performs IO and State
```

### Relevance to CLAIR
Our effects tracking is similar, but extended:
```
effect: (io stdout write)
  confidence: 0.99
  intent: "display greeting to user"
```

### Key Papers
- Gifford & Lucassen, "Integrating Functional and Imperative Programming" (1986)
- Wadler, "The Marriage of Effects and Monads" (1998)

---

## Synthesis: What's Novel in CLAIR

| Concept | Existing Work | CLAIR Extension |
|---------|---------------|-----------------|
| Uncertainty | Probabilistic PL | Epistemic confidence (about code, not data) |
| Provenance | Database provenance | Computation provenance with invalidation |
| Justification | Justification Logic | Computational justifications with confidence |
| Belief Revision | TMS | Type-theoretic belief revision |
| Design Rationale | IBIS/QOC | First-class decisions in the language |
| Refinements | Liquid Types | Refinements + confidence + invalidation |
| Effects | Effect Systems | Effects + intent + semantic meaning |

The synthesis—beliefs as typed values with confidence, provenance, justification, AND invalidation conditions, in a unified type system—appears to be novel.

---

## Reading List (Prioritized)

### Essential (Start Here)
1. de Kleer, "An Assumption-based TMS" (1986) — Core mental model
2. Jøsang, "Subjective Logic" (2016 book, or 2001 paper) — Uncertainty algebra
3. Green et al., "Provenance Semirings" (2007) — Provenance foundations

### Important (Deep Understanding)
4. Artemov, "Justification Logic" (2019 book, or 2001 paper) — Justification theory
5. Lee, "Design Rationale" papers (1991) — Decision capture
6. Sabelfeld & Myers, "Language-Based Information-Flow Security" (2003) — Type-level tracking

### Background (Context)
7. Doyle, "A Truth Maintenance System" (1979) — Original TMS
8. Goodman et al., "Church" (2008) — Probabilistic programming
9. Rondon et al., "Liquid Types" (2008) — Refinement types

### Aspirational (Where This Could Go)
10. HoTT Book, "Homotopy Type Theory" (2013) — Foundations
11. Lean 4 documentation — Practical dependent types

---

## Gaps in Coverage (Session 8 Assessment)

### ✓ SURVEYED (Session 8)

**Thread 3 (Self-Reference):** ✓ COMPLETE
- Löb's theorem (1955) - rules out self-soundness beliefs
- Boolos, "The Logic of Provability" (1993) - GL modal logic
- Kripke's theory of truth (1975) - fixed points for self-reference
- Tarski's hierarchy (1933) - stratified truth predicates
- Gupta & Belnap, "The Revision Theory of Truth" (1993) - revision sequences

See exploration/thread-3-self-reference.md for detailed engagement.

### Not Yet Surveyed (Relevant to Open Threads)

**Thread 4 (Grounding):**
- Foundationalism vs coherentism literature (BonJour, Sosa)
- Infinitism (Klein)
- Sellars on "the myth of the given"

**Thread 5 (Belief Revision):**
- AGM theory core papers (Alchourrón, Gärdenfors, Makinson)
- Ranking theory (Spohn)
- Dynamic epistemic logic (van Ditmarsch et al.)

**Thread 9 (Phenomenology):**
- Dennett on heterophenomenology
- Chalmers on the hard problem
- Recent AI consciousness debates (Butlin et al. 2023)

### Partially Covered (Need Deeper Engagement)
- Artemov's Justification Logic — mentioned but not deeply used
- Subjective Logic — described but not adopted
- Graded monads — categorical structure sketched but not proven

### ✓ SURVEYED (Session 11)

**Thread 8 (Confidence Operations):** ✓ COMPLETE
- T-norms and T-conorms (Klement, Mesiar, Pap 2000) - fuzzy logic foundations
- Hájek, "Metamathematics of Fuzzy Logic" (1998) - algebraic structures on [0,1]
- Product t-norm = CLAIR's multiplication (×)
- Minimum t-norm (Gödel) = CLAIR's min
- Algebraic sum t-conorm = CLAIR's probabilistic OR (⊕)

**Key finding**: (⊕, ×) do NOT form a semiring—distributivity fails. This is a known result in fuzzy logic.

See exploration/thread-8-verification.md §12 for detailed formalization.

### ✓ SURVEYED (Session 12)

**Thread 2.10 (Defeat Confidence Propagation):** ✓ SUBSTANTIALLY COMPLETE

**Pollock's Defeaters (1987, 2001)**:
- Rebutting defeaters: Attack the conclusion directly
- Undercutting defeaters: Attack the inference without attacking conclusion
- Weakest link principle: Argument strength = min of all steps
- Variable degrees of justification (2001): Graded rather than binary defeat

**Dung's Abstract Argumentation (1995)**:
- Argumentation frameworks: Nodes are arguments, edges are attacks
- Grounded extension: Unique, accepts unattacked arguments iteratively
- Preferred extension: Maximal admissible sets
- Qualitative (in/out), not graded—too coarse for CLAIR

**Gradual/Weighted Argumentation Semantics**:
- Amgoud & Ben-Naim (2023): Weighted bipolar argumentation graphs
- h-categorizer: strength(a) = w(a) / (1 + Σ strength(attackers))
- Max-based: Only strongest attacker matters
- Card-based: Number of attackers matters
- Key principles: Maximality, Void Precedence, Quality/Cardinality Precedence, Compensation

**Subjective Logic Discounting (Jøsang)**:
- Discounting operator: ω' = ω_trust ⊗ ω_source
- Formula: (b_t·b_x, b_t·d_x + d_t, u_t + b_t·u_x, a_x)
- Trust dilution in transitive chains
- **Key for CLAIR undercut**: c' = c × (1 - undercut_strength)

**Spohn's Ranking Theory (2012)**:
- Ordinal rather than numerical belief measures
- Ranking functions: κ : W → ℕ ∪ {∞}
- Handles iterated belief revision where AGM fails
- Potential ordinal alternative if calibration issues arise

**Jeffrey Conditioning (Probability Kinematics)**:
- Extends Bayesian conditioning to uncertain evidence
- P_new(A) = P_old(A|B)·P_new(B) + P_old(A|¬B)·P_new(¬B)
- Preserves conditional probabilities through update
- Potential for uncertain defeat propagation

**Key design decisions for CLAIR**:
- Undercut uses multiplicative discounting: c' = c × (1 - d)
- Rebut uses probabilistic comparison: c' = c_for / (c_for + c_against)
- Different operations for different semantic roles

See exploration/thread-2.10-defeat-confidence.md for detailed analysis.
