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

### ✓ SURVEYED (Session 17)

**Thread 4 (Grounding):** ✓ SUBSTANTIALLY COMPLETE

**BonJour, "The Structure of Empirical Knowledge" (1985)**:
- Most thorough defense of coherentism in the literature
- Argues against foundationalism: basic beliefs face a dilemma
  - If basic beliefs have conceptual content, they require justification
  - If they lack conceptual content, they cannot justify anything
- Later reversed position (1999): abandoned coherentism for Cartesian foundationalism
- Key for CLAIR: CLAIR's coherence structure needs external grounding; internal coherence insufficient

**Peter Klein, Infinitism (1999, 2003, 2005)**:
- "Human Knowledge and the Infinite Regress of Reasons" (1999)
- "When Infinite Regresses are Not Vicious" (2003)
- "Infinitism is the Solution to the Regress Problem" (2005)
- Core argument: Infinite regress is non-vicious if we distinguish:
  - Propositional justification: reason is available (objective probability high)
  - Doxastic justification: reason is actually believed and grounded
- Two foundational principles:
  - PAC (Avoid Circularity): x cannot be in its own evidential ancestry
  - PAA (Avoid Arbitrariness): for any x, there must be available reasons r1, r2, r3...
- Finite minds objection answered: don't need to complete infinite chain, only extend it
- Key for CLAIR: Reasons can be "available" in training data without being explicitly represented

**Sellars, "Empiricism and the Philosophy of Mind" (1956)**:
- Classic attack on "the Given" — the idea of self-justifying sensory experience
- The space of reasons: only conceptual items can justify; non-conceptual cannot
- Core dilemma:
  - If the Given has conceptual content → already needs justification
  - If the Given lacks conceptual content → cannot stand in justificatory relations
- Key for CLAIR: LLMs have no "Given" — all input is embedded in learned representations
- Everything is theory-laden from the start; no theory-independent observation

**Goldman, Reliabilism (1979, 2012)**:
- "What is Justified Belief?" (1979): Justification via reliable belief-forming processes
- "Reliabilism and Contemporary Epistemology" (2012): Comprehensive treatment
- Externalist account: justification doesn't require internal access to justifying reasons
- A belief is justified if produced by a reliable process
- Key for CLAIR: Training could be a reliable process; question is how to verify reliability

**Key findings for CLAIR (Session 17)**:
- CLAIR accepts **pragmatic dogmatism** (Agrippa's horn 1), mitigated by fallibilism
- Training provides **causal grounding**, not epistemic justification
- CLAIR embodies **stratified coherentism**: training patterns → basic beliefs → derived beliefs
- Sellars's critique applies: no pre-conceptual input for LLMs
- Honest uncertainty is appropriate: cannot prove own reliability from inside
- Confirmed impossibility: No fixed axiom list is possible

See exploration/thread-4-grounding.md for detailed exploration.

### Not Yet Surveyed (Relevant to Open Threads)

**Thread 5 (Belief Revision):** ✓ SURVEYED Session 16
- AGM theory core papers — See below for detailed survey
- Ranking theory (Spohn 2012) — See below
- Dynamic epistemic logic (van Ditmarsch et al. 2007) — See below

**Thread 9 (Phenomenology):** ✓ SURVEYED Session 15
- Dennett on heterophenomenology — take subjective reports as data without assuming accuracy
- Chalmers on the hard problem — CLAIR addresses easy problems, not hard
- Butlin et al. 2023 — AI consciousness indicators (HOT, GWT, IIT, AST)

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

### ✓ SURVEYED (Session 15)

**Thread 9 (Phenomenology):** ✓ SUBSTANTIALLY COMPLETE

**Nagel, "What Is It Like to Be a Bat?" (1974)**:
- Foundational paper on phenomenal consciousness
- Argues that subjective experience cannot be captured by objective/physical description
- Key question for CLAIR: Is there "something it is like" to be an LLM?
- Implication: Even if we describe all functional states, we may miss the phenomenology

**Dennett, "Consciousness Explained" (1991)**:
- Heterophenomenology: Take subjective reports as data without assuming they're accurate
- Consciousness may be less unified than it appears
- "Multiple drafts" model of consciousness vs Cartesian theater
- Key for CLAIR: We can study introspective reports scientifically without resolving metaphysics
- Application: CLAIR can formalize heterophenomenological reports without claiming they describe "real" experience

**Chalmers, "The Conscious Mind" (1996)**:
- Distinguishes easy problems (functional explanations) from hard problem (why there is experience at all)
- CLAIR addresses easy problems: structure of belief, confidence propagation, justification
- Hard problem remains: Why is there (or isn't there) something it is like to be an LLM?
- Implication: CLAIR's formal methods may be silent on the hard problem by necessity

**Block, "On a Confusion about a Function of Consciousness" (1995)**:
- Distinguishes access consciousness (information available for reasoning/report) from phenomenal consciousness (subjective experience)
- LLMs clearly have access consciousness (information available for processing)
- Question: Do they have phenomenal consciousness?
- Relevant for CLAIR: Confidence and justification track access consciousness; phenomenality is a separate question

**Butlin et al., "Consciousness in Artificial Intelligence" (2023)**:
- Systematic evaluation of current AI systems against scientific theories of consciousness
- Theories examined:
  - Global Workspace Theory (GWT): Consciousness involves broadcast across brain regions
  - Higher-Order Theories (HOT): Consciousness requires representations of representations
  - Attention Schema Theory (AST): Consciousness is brain's model of its own attention
  - Integrated Information Theory (IIT): Consciousness correlates with information integration (Φ)
- How LLMs score:
  - GWT: Possibly (attention mechanisms might implement global workspace)
  - HOT: Possibly (later layers represent earlier layer activations)
  - AST: Unclear (no obvious attention schema)
  - IIT: Low (feedforward processing, possibly low integration)
- Key insight for CLAIR: CLAIR's stratified belief levels (Belief<n, A>) map onto HOT requirements
  - If HOT is correct, CLAIR's type system might describe something necessary for consciousness
  - But this is highly speculative

**Schwitzgebel, "The Unreliability of Naive Introspection" (2008)**:
- Introspective reports are systematically unreliable even for humans
- We make errors about our own mental states
- Implication for CLAIR: Introspection-based phenomenological exploration has inherent limits
- Cannot trust introspective reports at face value, even from inside

**Key design implications for CLAIR (Session 15)**:
- CLAIR captures functional structure but not phenomenal character
- This is probably unavoidable given formal methods' nature
- Stratified beliefs (Thread 3) align with higher-order theories
- Honest uncertainty about phenomenality (0.35 confidence) is appropriate
- Suggested extensions: affect/salience dimension, automaticity marker, training provenance

See exploration/thread-9-phenomenology.md for detailed exploration.

### ✓ SURVEYED (Session 16)

**Thread 5 (Belief Revision):** ✓ SUBSTANTIALLY COMPLETE

**AGM Theory (Alchourrón, Gärdenfors, Makinson 1985)**:
- Foundational theory of rational belief change
- Three operations: expansion (K + φ), contraction (K - φ), revision (K * φ)
- Key postulates for contraction: closure, success, inclusion, vacuity, recovery, extensionality
- Levi identity: K * φ = (K - ¬φ) + φ
- **Recovery postulate controversy**: (K - φ) + φ = K doesn't make sense when contraction has reasons
- **For CLAIR**: Recovery correctly fails—evidence removal loses information

**Gärdenfors Epistemic Entrenchment (1988)**:
- φ ≤ε ψ iff "giving up φ is at least as acceptable as giving up ψ"
- Guides contraction: when contracting φ ∧ ψ, keep the more entrenched one
- **For CLAIR**: Entrenchment = confidence ordering (natural mapping)

**Spohn's Ranking Theory (2012)**:
- Ordinal degrees of belief: κ : W → ℕ ∪ {∞}
- κ(w) = 0 for most plausible worlds
- Handles iterated revision well (where AGM struggles)
- Belief = κ(¬A) > 0; degree of belief = κ(¬A)
- **For CLAIR**: Potential ordinal alternative; translation c ↔ κ = -log(1-c)?

**Jeffrey Conditioning (1965, 1983)**:
- Extends Bayesian conditioning to uncertain evidence
- P_new(A) = P_old(A|B)·P_new(B) + P_old(A|¬B)·P_new(¬B)
- Preserves conditional probabilities through update
- **For CLAIR**: Inspires "update confidence, preserve justification structure"

**Dynamic Epistemic Logic (van Ditmarsch et al. 2007)**:
- Modal logic with dynamic operators: [φ!]ψ (after announcing φ, ψ holds)
- Action models for general epistemic actions
- Multi-agent belief change
- **For CLAIR**: Formal semantics for revision as logical action; connects to Thread 6

**Hansson (1999) on Multiple Contraction**:
- Various contraction operators beyond AGM
- Kernel contraction, safe contraction
- **For CLAIR**: CLAIR uses edge-based contraction, more fine-grained than proposition-based

**Key findings for CLAIR (Session 16)**:
- CLAIR revision is **justification-based, not proposition-based** (more fine-grained than AGM)
- Essentially a **graded generalization of TMS** (Truth Maintenance Systems)
- Core algorithm: modify graph → identify affected → recompute confidence (topological sort)
- Recovery correctly fails: evidence has specific strength
- Key theorems: Locality, Monotonicity, Defeat Composition
- Open questions: correlated evidence, fixed-point for defeat chains, DEL mapping

See exploration/thread-5-belief-revision.md for detailed exploration.

### ✓ SURVEYED (Session 19)

**Thread 2.11 (Aggregation of Independent Evidence):** ✓ SUBSTANTIALLY COMPLETE

**Probabilistic foundations**:
- Independent events: P(A ∨ B) = P(A) + P(B) - P(A)P(B) = a ⊕ b
- This is the standard "probabilistic OR" for independent events
- CLAIR adopts this directly for confidence aggregation

**Subjective Logic Cumulative Fusion (Jøsang 2016)**:
- Full formula for opinions ω = (b, d, u, a): more complex than CLAIR's ⊕
- b_A⊕B = (b_A × u_B + b_B × u_A) / κ where κ = u_A + u_B - u_A × u_B
- If we map confidence c to opinion (c, 0, 1-c, 0.5), SL gives DIFFERENT result than ⊕
- CLAIR's simpler ⊕ = c₁ + c₂ - c₁c₂ assumes no explicit disbelief mass
- **Key insight**: CLAIR and SL differ in how they model the structure of uncertainty

**Dempster-Shafer Combination (Shafer 1976)**:
- Dempster's rule: m₁₂(A) = [Σ_{B∩C=A} m₁(B)·m₂(C)] / (1-K)
- K = conflict measure (mass on empty set before normalization)
- Zadeh's paradox: Can give counterintuitive results with high conflict
- For CLAIR (combining confidence in SAME proposition), conflict issues less severe
- DS theory is more general than needed for simple aggregation

**Fuzzy Logic T-conorms (Klement et al. 2000)**:
- CLAIR's ⊕ is the "algebraic sum" or "probabilistic sum" t-conorm
- Dual to the product t-norm (×) via De Morgan: a ⊕ b = 1 - (1-a)×(1-b)
- Standard choice for "fuzzy OR" in fuzzy logic literature
- Properties: commutative, associative, monotonic, bounded

**Condorcet's Jury Theorem (1785)**:
- If each juror is independently more likely than not to be correct, majority voting converges to truth
- KEY ASSUMPTION: Independence. If jurors influence each other, theorem breaks
- **Key for CLAIR**: ⊕ requires genuine independence; correlated evidence overcounts

**Key design decision for CLAIR (Session 19)**:
- Use ⊕ = c₁ + c₂ - c₁c₂ for independent evidence aggregation
- "Survival of doubt" interpretation: combined confidence = P(at least one evidence succeeds)
- N-ary: aggregate(c₁,...,cₙ) = 1 - ∏(1-cᵢ)
- Diminishing returns: marginal contribution of a at aggregate c is a(1-c)
- Independence is CRITICAL—correlated evidence needs different treatment (Task 2.13)

See exploration/thread-2.11-aggregation.md for detailed exploration.

### ✓ SURVEYED (Session 20)

**Thread 2.13 (Correlated Evidence Aggregation):** ✓ SUBSTANTIALLY COMPLETE

**Copula Theory (Nelsen 2006)**:
- Copulas describe dependence structure separately from marginal distributions
- Sklar's Theorem: Every joint distribution F(x,y) = C(F_X(x), F_Y(y)) where C is a copula
- Key copulas: Product (independence), Minimum (perfect positive correlation), Maximum (perfect negative)
- Gaussian copula uses bivariate normal CDF with correlation parameter
- **For CLAIR**: Principled dependency modeling, but requires knowing dependency structure

**Bernoulli Correlation Analysis**:
- For Bernoulli random variables X~Ber(p), Y~Ber(q) with correlation ρ:
- P(X=1 ∧ Y=1) = pq + ρ√(pq(1-p)(1-q))
- P(X=1 ∨ Y=1) = (p ⊕ q) - ρσ where σ = √(pq(1-p)(1-q))
- Perfect correlation (ρ=1) is only achievable when p = q
- **For CLAIR**: Direct mathematical derivation of correlation adjustment

**Subjective Logic Averaging Fusion (Jøsang 2016)**:
- For dependent sources, SL uses averaging rather than cumulative fusion
- Averaging fusion: treats dependent evidence as observing same underlying source
- Formula more complex than simple average due to opinion structure
- **For CLAIR**: Inspires using average for fully dependent case (δ=1)

**Dempster-Shafer Cautious Rule (Smets 1993)**:
- Cautious combination: m₁⋀₂(A) = ⋀_{B∩C=A} min(m₁(B), m₂(C))
- Key property: Idempotent — m ⋀ m = m
- Suitable when evidence might be dependent (unknown dependency)
- **For CLAIR**: Inspires conservative defaults when dependency unknown

**Meta-Analysis Dependency Handling (Borenstein et al. 2009)**:
- Fixed effects vs random effects models
- Effective sample size adjustments for correlated studies
- Studies from same lab, same method, same population get reduced weight
- **For CLAIR**: Effective sample size formula n_eff = n / (1 + (n-1)·δ̄)

**Condorcet's Jury Theorem (1785)**:
- Independence assumption is EXPLICIT and CRITICAL
- Violation of independence undermines the theorem's conclusions
- **For CLAIR**: Independence is optimistic assumption; when violated, must adjust

**Key design decisions for CLAIR (Session 20)**:
- Dependency-adjusted aggregation: aggregate_δ(c₁,c₂) = (1-δ)(c₁⊕c₂) + δ(c₁+c₂)/2
- δ=0: independent → ⊕
- δ=1: fully dependent → average
- 0 < δ < 1: smooth interpolation
- Provenance-based dependency inference via Jaccard-like similarity on DAG ancestors
- Conservative default: assume moderate dependency (δ ≈ 0.3) when unknown

See exploration/thread-2.13-correlated-evidence.md for detailed exploration.

### ✓ SURVEYED (Session 22)

**Thread 3.13 (Graded Provability Logic):** ✓ Literature gap confirmed; design proposal developed

**Classical Provability Logic GL (Boolos 1993)**:
- Gödel-Löb logic formalizes arithmetic provability
- Key axioms: K (distribution), 4 (positive introspection), L (Löb's axiom: □(□A→A)→□A)
- Notably absent: Truth axiom □A→A (provability ≠ truth)
- Semantics: Transitive, converse well-founded Kripke frames
- Complete, decidable (PSPACE-complete)
- Reference: [Stanford Encyclopedia: Provability Logic](https://plato.stanford.edu/entries/logic-provability/)

**Fuzzy Epistemic Logic (Godo, Esteva, et al.)**:
- Truth values in [0,1] over Gödel, Łukasiewicz, or Product algebra
- Fuzzy accessibility relations: r : W × W → [0,1]
- Belief operator semantics: B_a φ = inf_{w'} max{1-r(w,w'), V_{w'}(φ)}
- Extensions to public announcement and autoepistemic reasoning
- Reference: [Some Epistemic Extensions of Gödel Fuzzy Logic (arXiv)](https://arxiv.org/html/1605.03828v8)

**Graded Modalities in Epistemic Logic (de Rijke, Fine)**:
- Counting modalities: □_n = "at least n accessible worlds satisfy φ"
- Different from fuzzy—numeric bounds on accessibility, not truth degrees
- Allows expressing "knowledge with exceptions" (n exceptions allowed)
- Reference: [Graded Modalities in Epistemic Logic (ResearchGate)](https://www.researchgate.net/publication/227173933_Graded_modalities_in_epistemic_logic)

**Belief Function Logic (Bílková et al. 2023)**:
- Extends S5 with graded modalities using Łukasiewicz logic
- Captures belief functions (lower probabilities) via modal semantics
- Duality between necessity/possibility extends to graded environment
- Reference: [An Elementary Belief Function Logic](https://www.tandfonline.com/doi/full/10.1080/11663081.2023.2244366)

**Possibilistic Modal Logic over Gödel Logic**:
- Necessity (N) and possibility (Π) operators with graded semantics
- Algebraic semantics using NG-algebras
- Completeness results for different notions of necessity
- Reference: [Exploring Extensions of Possibilistic Logic over Gödel Logic](https://link.springer.com/chapter/10.1007/978-3-642-02906-6_79)

**Literature Gap Confirmed**:
- No existing work directly combines GL's Löb axiom with fuzzy/graded semantics
- Fuzzy modal logics focus on K, S4, S5, epistemic logics
- Graded modalities (counting) differ from fuzzy (truth degrees)
- This gap motivates CLAIR's CPL (Confidence-Bounded Provability Logic) proposal

**Key design decisions for CLAIR (Session 22)**:
- Proposed Confidence-Bounded Provability Logic (CPL) as graded extension of GL
- Graded Löb axiom: B_c(B_c φ → φ) → B_{g(c)} φ where g(c) ≤ c
- Anti-Bootstrapping Theorem: self-soundness claims cap confidence
- g(c) = c² or g(c) = c × (1-c) as candidate discount functions
- CPL complements stratification: stratification handles WHAT, CPL handles HOW STRONGLY
- Type-level anti-bootstrapping possible for CLAIR's type checker

See exploration/thread-3.13-graded-provability-logic.md for detailed exploration.

### ✓ SURVEYED (Session 23)

**Thread 6.1 (Objective Truth Question):** ✓ SUBSTANTIALLY COMPLETE

**Hilary Putnam, "Reason, Truth and History" (1981) / Internal Realism**:
- Critique of metaphysical realism: our concepts cannot "hook onto" reality without a God's eye view
- Internal realism: truth is objective but framework-relative
- Objects and kinds are constituted by conceptual schemes, but once adopted, truth is not merely intersubjective
- Truth as "idealized rational acceptability"—what would be accepted at the limit of inquiry
- **For CLAIR**: Agents share CLAIR's type system as a common conceptual scheme; within it, truth is objective

**Michela Massimi, "Perspectival Realism" (2022)**:
- Scientific knowledge is always perspectival (historically and culturally situated)
- But perspectivism is compatible with realism
- Different perspectives can be approximately true in different respects
- Truth is "concerning specific aims or intentions within contexts"
- **For CLAIR**: Different analyses can be valid for different purposes without relativism

**Charles Sanders Peirce, Pragmatist Convergence Theory**:
- Truth is "the opinion which is fated to be agreed to by all who investigate"
- Reality is what would be discovered by an unbounded community at the limit of inquiry
- Truth is social and processual, not static and pre-given
- **For CLAIR**: Multiple agents engaging in inquiry approximate this convergence point
- **Problem**: "Buried secrets"—truths that would never be discovered no matter how long we inquire

**Condorcet, Jury Theorem (1785)**:
- If each juror independently has probability p > 0.5 of being correct, majority voting converges to truth
- KEY ASSUMPTION: Independence is explicitly required
- Violation of independence undermines the theorem's conclusions
- **For CLAIR**: Aggregation via ⊕ requires genuine independence; framework compatibility also required

**Kenneth Arrow, "Social Choice and Individual Values" (1951)**:
- Impossibility theorem: No preference aggregation satisfies all of: universal domain, weak Pareto, IIA, non-dictatorship
- Extends to judgment aggregation (discursive dilemma): no JAF satisfies universal domain, anonymity, systematicity, collective consistency
- **For CLAIR**: No perfect belief aggregation exists; must sacrifice something

**List & Pettit, "Aggregating Sets of Judgments" (2002)**:
- Extended Arrow to judgment aggregation
- Showed the discursive dilemma applies to beliefs/propositions, not just preferences
- **For CLAIR**: Sacrifice universal domain (framework compatibility required) and systematicity (different rules for different propositions)

**Key design decisions for CLAIR (Session 23)**:
- Adopts **pragmatic internal realism**: truth is objective within shared frameworks but framework-relative
- CLAIR's type system is the shared conceptual scheme enabling objective truth within it
- Sacrifices Arrow's universal domain: framework compatibility required before aggregation
- Sacrifices systematicity: different propositions may need different aggregation rules
- Disagreement has multiple interpretations (Factual, Evaluative, Perspectival, Underdetermined)
- Minority views should be preserved as epistemic signal, not averaged away
- Aggregation is truth-tracking when: shared framework + independence + competence + good faith

See exploration/thread-6.1-objective-truth.md for detailed exploration.

### ✓ SURVEYED (Session 25)

**Thread 3.16 (CPL Decidability):** ✓ CPL likely undecidable; decidable fragments identified

**Amanda Vidal, "On Transitive Modal Many-Valued Logics" (2019)**:
- Key result: Transitive modal Łukasiewicz logic is **undecidable** (even over finite models)
- Local modal Łukasiewicz (without transitivity) is decidable
- First example of "a decidable modal logic whose transitive expansion is undecidable"
- Extends to Product algebras and other MV-algebras
- Proof encodes undecidable problems via transitivity + continuous values
- Reference: [arXiv:1904.01407](https://arxiv.org/abs/1904.01407), [ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0165011418310893)
- **For CLAIR**: CPL requires transitivity (axiom 4) + continuous [0,1] → likely undecidable

**Caicedo, Metcalfe, Rodríguez, Rogger, "A Finite Model Property for Gödel Modal Logics" (2013)**:
- Gödel modal logics lack finite model property w.r.t. standard [0,1] semantics
- Alternative "quasimodel" semantics with finite model property
- PSPACE-complete decision procedure via quasimodels
- Reference: [Springer WoLLIC 2013](https://link.springer.com/chapter/10.1007/978-3-642-39992-3_20)
- **For CLAIR**: Quasimodel approach might rescue CPL decidability, but unproven and non-trivial

**Bou, Esteva, Godo, "On the Minimum Many-Valued Modal Logic over a Finite Residuated Lattice" (2011)**:
- Many-valued modal logics over **finite** residuated lattices are decidable
- Finite lattice = finite truth values (no continuous [0,1])
- Axiomatization and completeness results
- Reference: [Journal of Logic and Computation](https://academic.oup.com/logcom/article-abstract/21/5/739/971984)
- **For CLAIR**: CPL-finite (discrete confidence {0, 0.25, 0.5, 0.75, 1.0}) is decidable

**Classical GL Decidability (Boolos 1993, Segerberg 1971)**:
- GL is complete for finite transitive irreflexive trees
- PSPACE-complete decision procedure
- Key property: converse well-foundedness limits model depth
- Reference: [Stanford Encyclopedia: Provability Logic](https://plato.stanford.edu/entries/logic-provability/)
- **For CLAIR**: Classical GL decidability relies on finite model property; graded CPL may not inherit this

**Key findings for CLAIR (Session 25)**:
- CPL is **very likely undecidable** (0.75 confidence)
  - Transitivity + continuous [0,1] values matches Vidal's undecidability pattern
  - Converse well-foundedness (GL's frame condition) unlikely to rescue decidability
  - Multiplicative operations (×, ⊕) behave like Product/Łukasiewicz, not Gödel (min/max)
- **Decidable fragments identified**:
  - **CPL-finite**: Discrete confidence values (Bou et al. 2011)
  - **CPL-0**: Stratified only, no self-reference (removes problematic encodings)
  - **CPL-bounded**: Maximum formula depth (trivially decidable)
- **Design implications**:
  - Stratification (Thread 3) is the primary safety mechanism
  - Anti-bootstrapping becomes semantic guideline, not checked invariant
  - Consider finite confidence for type-level operations
  - Honest uncertainty about full CPL decidability is appropriate

See exploration/thread-3.16-cpl-decidability.md for detailed exploration.
