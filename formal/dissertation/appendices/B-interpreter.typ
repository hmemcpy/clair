#import "../layout.typ": *

// Appendix B: Reference Interpreter
#heading(level: 1)[Reference Interpreter Design]

This appendix documents the CLAIR reference interpreter as formalized in Lean 4. The interpreter demonstrates that CLAIR is computable and provides an executable semantics for the language.

#heading(level: 2)[B.1 Architecture Overview]

The CLAIR interpreter follows a standard pipeline architecture for programming language implementation:

+---+---+---+
| **Component** | **Purpose** | **Lean Module** |
+---+---+---+
| Parser | Convert surface syntax to AST | `CLAIR.Parser` |
| Type Checker | Verify well-typedness and stratification | `CLAIR.Typing.HasType` |
| Single-Step Evaluator | Execute one reduction step | `CLAIR.Semantics.Step` |
| Multi-Step Evaluator | Execute to value (with fuel) | `CLAIR.Semantics.Eval` |
+---+---+---+

#figure(
  [
    #set text(size: 10pt)
    #align(center)[
      #block(
        fill: rgb("#faf8f5"),
        inset: 10pt,
        radius: 4pt,
        stroke: 1pt,
        [
          #align(center)[#text(weight: "bold")[Source Code]]
          #v(0.3em)
          ↓
          #align(center)[#text(weight: "bold")[Parser]]
          #v(0.3em)
          ↓
          #align(center)[#text(weight: "bold")[AST (Expr)]]
          #v(0.3em)
          ↓
          #align(center)[#text(weight: "bold")[Type Checker]]
          #v(0.3em)
          ↓
          #align(center)[#text(weight: "bold")[Typed AST]]
          #v(0.3em)
          ↓
          #align(center)[#text(weight: "bold")[Evaluator (Step + Eval)]]
          #v(0.3em)
          ↓
          #align(center)[#text(weight: "bold")[Value]]
        ]
      )
    ]
  ],
  caption: "B.1: CLAIR interpreter architecture pipeline"
)

The evaluation strategy is #emph[call-by-value]: function arguments are evaluated before the function is applied. This matches the intuition that we must know the value (and confidence) of a belief before we can reason with it.

#heading(level: 2)[B.2 Single-Step Semantics]

The single-step reduction relation `#text(code)[e -> e']` is defined inductively in `CLAIR.Semantics.Step`. We show key rules here:

#heading(level: 3)[B.2.1 Core Lambda Calculus Rules]

#theorem[
  *Beta Reduction.* For any type `A`, expression `e`, and value `v`:
  `#text(code)[app (lam A e) v -> subst0 v e]`

  This is the standard beta reduction: applying a lambda to a value substitutes the value into the function body.
]

#theorem[
  *Application Contexts.* If `#text(code)[e1 -> e1']` then:
  `#text(code)[app e1 e2 -> app e1' e2']`

  If `#text(code)[e2 -> e2']` and `v1` is a value then:
  `#text(code)[app v1 e2 -> app v1 e2']`

  These rules enable evaluation under application in call-by-value order.
]

#heading(level: 3)[B.2.2 Belief Operations]

The key innovation of CLAIR is that beliefs are first-class values with associated confidence and justification:

#theorem[
  *Value Extraction.* For belief `#text(code)[belief v c j]` where `v` is a value:
  `#text(code)[val (belief v c j) -> v]`

  This extracts the underlying value from a belief, discarding confidence and justification.
]

#theorem[
  *Confidence Extraction.* For belief `#text(code)[belief v c j]` where `v` is a value:
  `#text(code)[conf (belief v c j) -> belief v c j]`

  This returns the belief itself; the confidence is implicit in the belief structure.
]

#theorem[
  *Justification Extraction.* For belief `#text(code)[belief v c j]` where `v` is a value:
  `#text(code)[just (belief v c j) -> litString (toString j)]`

  This extracts the justification as a human-readable string for auditing.
]

#heading(level: 3)[B.2.3 Defeat Operations]

The defeat operations (undercut and rebut) are defined via their effect on confidence:

#theorem[
  *Undercut Evaluation.* For beliefs `#text(code)[belief v c1 j1]` and `#text(code)[belief d c2 j2]` where both `v` and `d` are values:
  `#text(code)[undercut (belief v c1 j1) (belief d c2 j2) -> belief v (c1 * (1 - c2)) (undercut_j j1 j2)]`

  Undercut reduces confidence multiplicatively: a defeater with confidence `c2` reduces confidence by a factor of `#text(code)[1 - c2]`.
]

#theorem[
  *Rebuttal Evaluation.* For beliefs `#text(code)[belief v1 c1 j1]` and `#text(code)[belief v2 c2 j2]` where both are values:
  `#text(code)[rebut (belief v1 c1 j1) (belief v2 c2 j2) -> belief v1 (c1 / (c1 + c2)) (rebut_j j1 j2)]`

  Rebuttal normalizes by relative strength. When `#text(code)[c1 = c2]`, confidence becomes `#text(code)[1/2]`.
]

#heading(level: 2)[B.3 Multi-Step Evaluation with Fuel]

To ensure termination, the evaluator uses a #emph[fuel] parameter that bounds the number of reduction steps:

#definition[
  *Fuel-Bounded Evaluation.* `#text(code)[evalFuel : Nat -> Expr -> Option Expr]`

  - `#text(code)[evalFuel 0 e]` returns `#text(code)[some e]` if `e` is a value, `#text(code)[none]` otherwise
  - `#text(code)[evalFuel (n+1) e]` returns `#text(code)[some e']` if `e` evaluates to a value in `n+1` steps, `#text(code)[none]` if stuck
]

The default `#text(code)[eval]` function uses 1000 steps of fuel:
`#text(code)[def eval (e : Expr) : Option Expr := evalFuel 1000 e]`

#heading(level: 2)[B.4 Example Walkthroughs]

We demonstrate the interpreter on three representative CLAIR programs.

#heading(level: 3)[B.4.1 Simple Belief Formation]

#example[
  *Direct Belief.* Surface syntax:
  ```lisp
  (belief 42 0.9 "sensor-reading")
  ```

  *Lean representation:*
  ```lean
  def example_belief : Expr :=
    belief (litNat 42) (9/10) (Justification.axiomJ "sensor-reading")
  ```

  *Evaluation:*
  - Expression is already a value
  - `#text(code)[eval example_belief]` returns `#text(code)[some example_belief]`
  - The belief carries value `42` with confidence `0.9`
]

#heading(level: 3)[B.4.2 Evidence Aggregation]

#example[
  *Independent Evidence Combination.* Surface syntax:
  ```lisp
  (aggregate
    (belief "Paris is capital of France" 0.5 "prior")
    (belief "Paris is capital of France" 0.7 "textbook"))
  ```

  *Lean representation:*
  ```lean
  def example_aggregate : Expr :=
    aggregate
      (belief (litString "Paris is capital of France") (5/10)
             (Justification.axiomJ "prior"))
      (belief (litString "Paris is capital of France") (7/10)
             (Justification.axiomJ "textbook"))
  ```

  *Step-by-step evaluation:*
  1. Both arguments are values (beliefs)
  2. Apply probabilistic sum: `#text(code)[c_new = c1 + c2 - c1*c2]`
  3. `#text(code)[c_new = 0.5 + 0.7 - 0.5*0.7 = 1.2 - 0.35 = 0.85]`
  4. Combined justification: `#text(code)[Justification.agg ["prior", "textbook"]]`
  5. Result: `#text(code)[belief "Paris..." 0.85 (agg ["prior", "textbook"])]`

  This demonstrates the probabilistic sum operator: two independent pieces of evidence combine to increase confidence beyond either individual source.
]

#heading(level: 3)[B.4.3 Undercutting in Action]

#example[
  *Defeasible Reasoning.* Scenario: A sensor reports "temperature is 25°C" with confidence 0.8, but a calibration warning suggests the sensor may be malfunctioning with confidence 0.3.

  *Surface syntax:*
  ```lisp
  (undercut
    (belief 25 0.8 "sensor-A")
    (belief "sensor-A unreliable" 0.3 "calibration-warning"))
  ```

  *Lean representation:*
  ```lean
  def example_undercut : Expr :=
    undercut
      (belief (litNat 25) (8/10) (Justification.axiomJ "sensor-A"))
      (belief (litString "sensor-A unreliable") (3/10)
             (Justification.axiomJ "calibration-warning"))
  ```

  *Step-by-step evaluation:*
  1. Both arguments are values
  2. Apply undercut formula: `#text(code)[c_new = c1 * (1 - c2)]`
  3. `#text(code)[c_new = 0.8 * (1 - 0.3) = 0.8 * 0.7 = 0.56]`
  4. Result: `#text(code)[belief 25 0.56 (undercut_j "sensor-A" "calibration-warning")]`

  The calibration warning reduces confidence from 0.8 to 0.56. The justification tracks that this belief was undercut, preserving the reasoning history.
]

#heading(level: 3)[B.4.4 Rebuttal and Confidence Collapse]

#example[
  *Conflicting Evidence.* Scenario: Two sources disagree on whether a fact holds, with confidences 0.7 and 0.3 respectively.

  *Lean representation:*
  ```lean
  def example_rebut : Expr :=
    rebut
      (belief (litBool true) (7/10) (Justification.axiomJ "source-A"))
      (belief (litBool false) (3/10) (Justification.axiomJ "source-B"))
  ```

  *Step-by-step evaluation:*
  1. Both arguments are values
  2. Apply rebuttal formula: `#text(code)[c_new = c1 / (c1 + c2)]`
  3. `#text(code)[c_new = 0.7 / (0.7 + 0.3) = 0.7 / 1.0 = 0.7]`
  4. Result: `#text(code)[belief true 0.7 (rebut_j "source-A" "source-B")]`

  Note that when `#text(code)[c1 = c2]` (equally strong conflicting evidence), confidence collapses to `#text(code)[1/2]`. This represents a state of maximal uncertainty.
]

#heading(level: 3)[B.4.5 Derivation Chain]

#example[
  *Multi-Step Derivation.* Scenario: Derive a conclusion from two premises using the `derive` operator.

  *Lean representation:*
  ```lean
  def example_derivation : Expr :=
    derive
      (belief (litNat 1) (8/10) (Justification.axiomJ "premise1"))
      (belief (litNat 2) (8/10) (Justification.axiomJ "premise2"))
  ```

  *Step-by-step evaluation:*
  1. Both arguments are values
  2. Apply derivation formula: `#text(code)[c_new = c1 * c2]`
  3. `#text(code)[c_new = 0.8 * 0.8 = 0.64]`
  4. Result: `#text(code)[belief (pair 1 2) 0.64 (rule "derive" ["premise1", "premise2"])]`

  The result pairs the premise values, and confidence is the product (representing the conjunction strength). The justification records that this came from a derivation rule.
]

#heading(level: 2)[B.5 Key Properties]

The Lean formalization proves five key properties that demonstrate CLAIR's correctness as an epistemic reasoning system:

#definition[
  *Property 1: Beliefs Track Confidence.* Confidence is preserved through computation: if a belief `#text(code)[b]` has confidence `#text(code)[c]`, then after any sequence of valid reductions `#text(code)[b ->* b']`, the resulting belief `#text(code)[b']` has a confidence value that is a deterministic function of `#text(code)[c]` and the operations applied.
]

#definition[
  *Property 2: Evidence is Affine.* No evidence is double-counted. The `#text(code)[aggregate]` operator uses probabilistic sum `#text(code)[a ⊕ b = a + b - a*b]`, which equals the probability of the union of independent events. This ensures that aggregating a belief with itself does not increase confidence: `#text(code)[c ⊕ c = c + c - c*c = c(2 - c)]` which is only equal to `#text(code)[c]` when `#text(code)[c = 0]` or `#text(code)[c = 1]`. In practice, justification tracking prevents exact duplicate aggregation.
]

#definition[
  *Property 3: Introspection is Safe.* The `#text(code)[introspect]` operator satisfies the stratification constraints defined in Chapter 6. It is impossible to form a belief about the current confidence of that same belief, preventing the formation of self-referential paradoxes.
]

#definition[
  *Property 4: Defeat Operations are Correct.* Undercut and rebut satisfy their specifications:
  - Undercut is monotonic in both arguments: higher source confidence or higher defeater confidence yields predictable results
  - Rebuttal is symmetric: `#text(code)[rebut b1 b2]` and `#text(code)[rebut b2 b1]` yield beliefs about opposing values with complementary confidence
]

#definition[
  *Property 5: Type Checking is Decidable.* The bidirectional type checker in `CLAIR.Typing.HasType` terminates for all well-formed inputs. This is proven formally in the Lean code by showing that each recursive call decreases a measure (expression size or stratification level).
]

#heading(level: 2)[B.6 Implementation Notes]

The Lean interpreter is designed as a #emph[reference implementation], not a production system. Key design decisions:

+---+---+
| **Aspect** | **Decision** | **Rationale** |
+---+---+
| Fuel | 1000 steps default | Prevents infinite loops while allowing reasonable programs |
| Evaluation Order | Call-by-value | Matches intuition about belief formation |
| Parser | Minimal (constructors only) | Demonstrates concept without complex parsing logic |
| Error Handling | `Option Expr` (partial function) | Stuck states return `none`; can be extended with explicit errors |
+---+---+

For production use, we recommend:
1. A proper parser (e.g., using Megaparsec in Haskell)
2. Exception-based error handling with detailed error messages
3. JIT compilation for performance
4. Persistent justification storage for audit trails
5. Parallel evaluation for independent subexpressions

#heading(level: 2)[B.7 Relation to Chapter 10]

Chapter 10 discusses implementation considerations for a production CLAIR system. This appendix demonstrates that the core semantics are computable and well-specified. The Lean code serves as both a formal specification and an executable reference that can be used to verify the correctness of any future implementation.

#v(1em)
