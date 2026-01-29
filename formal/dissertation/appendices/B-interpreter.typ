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

#heading(level: 2)[B.8 Haskell Reference Implementation]

In addition to the Lean formalization, a complete Haskell reference implementation is provided. This implementation demonstrates that CLAIR can be realized in a general-purpose programming language while maintaining the semantic properties proved in Lean.

#heading(level: 3)[B.8.1 Project Structure]

The Haskell implementation is organized as a Cabal project with the following structure:

+---+---+
| **Module** | **Purpose** |
+---+---+
| `CLAIR.Syntax` | Abstract syntax trees (AST) for CLAIR expressions |
| `CLAIR.Confidence` | Confidence algebra: ⊕, ⊗, undercut, rebut |
| `CLAIR.Parser` | Parse surface syntax into AST (Parsec) |
| `CLAIR.TypeChecker` | Bidirectional type checking with confidence grades |
| `CLAIR.Evaluator` | Small-step operational semantics with fuel |
| `CLAIR.Pretty` | Pretty-printing for values and types |
| `CLAIR.TypeChecker.Types` | Type checker context and error types |
+---+---+

The implementation includes:
- A REPL (`app/Main.hs`) for interactive evaluation
- A comprehensive test suite (`test/`) with 35 passing tests
- QuickCheck properties for algebraic laws
- Example programs demonstrating belief operations

#heading(level: 3)[B.8.2 Syntax Definition]

The core AST in `CLAIR.Syntax` mirrors the Lean formalization:

```haskell
-- | A belief value with all its annotations
data Belief = Belief
  { beliefValue     :: Expr           -- The proposition/content
  , beliefConf      :: Confidence     -- Confidence level [0,1]
  , beliefJustify   :: Justification  -- Supporting arguments
  , beliefInvalidate :: Invalidation  -- Defeating information
  , beliefProvenance :: Provenance    -- Source tracking
  }

-- | Core expression language
data Expr
  = EVar Name              -- Variable: x
  | ELam Name Type Expr    -- Lambda: λx:A. e
  | EApp Expr Expr         -- Application: e1 e2
  | EAnn Expr Type         -- Type annotation: e : A
  | EBelief Belief         -- Belief: belief(v,c,j,i,p)
  | EBox Confidence Expr   -- Self-reference: □_c e
  | EPrim Op Expr Expr     -- Primitive operation
  | ELit Literal           -- Literal value
```

Key design decisions:
- GADTs enable type-safe AST construction
- Deriving `Generic` and `ToJSON/FromJSON` enables serialization
- Provenance and justification are explicit for audit trails

#heading(level: 3)[B.8.3 Confidence Algebra]

The `CLAIR.Confidence` module implements the confidence operations with careful attention to semantic correctness:

```haskell
-- | Probabilistic sum: a ⊕ b = 1 - (1-a)(1-b) = a + b - ab
-- Assumes: sources are conditionally independent
oplus :: Confidence -> Confidence -> Confidence
oplus (Confidence a) (Confidence b) = clamp (a + b - a * b)

-- | Product t-norm: a ⊗ b = a * b
otimes :: Confidence -> Confidence -> Confidence
otimes (Confidence a) (Confidence b) = clamp (a * b)

-- | Apply undercut defeat: multiply by (1-d)
-- Rationale: Undercut attacks the evidential connection
undercut :: Defeat -> Confidence -> Confidence
undercut (Defeat d) (Confidence c) = clamp (c * (1 - d))

-- | Apply rebut with normalization
-- Limitation: Collapses absolute strength; considers uncertainty-preserving alternatives
rebut :: Defeat -> Confidence -> Confidence -> Confidence
rebut (Defeat d_strength) (Confidence c_for) (Confidence c_against_base) =
  let c_against = d_strength * c_against_base
      total = c_for + c_against
  in if total == 0
     then Confidence 0.5  -- ignorance prior
     else clamp (c_for / total)

-- | Square discount for self-reference: g(c) = c²
-- Prevents bootstrapping while preserving high-confidence self-endorsement
squareDiscount :: DiscountFn
squareDiscount (Confidence c) = clamp (c * c)
```

#heading(level: 3)[B.8.4 Type Checking]

The bidirectional type checker in `CLAIR.TypeChecker` implements the rules from Appendix E:

```haskell
-- | Infer (synthesize): Γ ⊢ e ↑ τ
infer :: Context -> Expr -> Either TypeError TCResult
infer ctx expr = case expr of
  -- Variable: Γ ⊢ x : Γ(x)
  EVar x -> case ctxLookup x ctx of
    Just ty -> return (TCResult ty ctx)
    Nothing -> Left (UnboundVar x)

  -- Application: Γ ⊢ e ↑ τ₁ → τ₂, Γ ⊢ e' ↓ τ₁
  EApp e1 e2 -> do
    TCResult ty1 ctx1 <- infer ctx e1
    case ty1 of
      TFun argTy resTy -> do
        ctx2 <- check ctx1 e2 argTy
        return (TCResult resTy ctx2)
      _ -> Left (NotFunction ty1)

  -- Belief: Γ ⊢ e : τ, c ∈ [0,1]
  --         ──────────────────
  --         Γ ⊢ belief(e,c) ↑ Belief_c[τ]
  EBelief (Belief e c _ _ _) -> do
    unless (isNormalized c) $
      Left (InvalidConfidence c)
    TCResult ty ctx' <- infer ctx e
    let beliefTy = TBelief c ty
    return (TCResult beliefTy ctx')
```

The bidirectional approach provides:
- Better error messages (checking mode guides synthesis)
- Natural handling of implicit arguments
- Clear separation of inference vs. verification

#heading(level: 3)[B.8.5 Evaluation]

The small-step evaluator in `CLAIR.Evaluator` implements the operational semantics with fuel-bounded termination:

```haskell
-- | Single-step reduction: e → e'
step :: Env -> Expr -> Either EvalError (Maybe Expr)
step env expr = case expr of
  -- E-Beta: (λx:τ.e) v → e[x := v]
  EApp (ELam varName _ty body) arg
    | isValue arg -> do
        v <- evalExpr env arg
        return (Just (subst varName v body))

  -- E-Prim: Reduce primitive operations
  EPrim op e1 e2
    | isValue e1 && isValue e2 -> evalPrimOp env op e1 e2

  -- E-Belief: Evaluate belief content to value
  EBelief (Belief e c j i p) -> do
    me' <- step env e
    case me' of
      Just e' -> return (Just (EBelief (Belief e' c j i p)))
      Nothing -> return Nothing  -- Fully evaluated

  -- E-Box: □_c e becomes value when e is fully evaluated
  EBox c e -> do
    me' <- step env e
    case me' of
      Just e' -> return (Just (EBox c e'))
      Nothing -> return Nothing
```

Key features:
- **Fuel**: 1,000,000 steps default prevents infinite loops
- **Call-by-value**: Arguments evaluated before application
- **Capture-avoiding substitution**: Preserves variable hygiene
- **Error recovery**: Detailed error messages for debugging

#heading(level: 3)[B.8.6 REPL Usage]

The interactive REPL (`app/Main.hs`) supports:

```
clair> :help
CLAIR REPL - Commands:
  :quit  Exit the REPL
  :help  Show this help message

Examples:
  5
  λx:Nat. x
  (λx:Nat. x + 1) 5
  3 + 4
  □0.8 true
  belief(5, 0.9, none, none, none)
```

The REPL provides:
- Parse error reporting with locations
- Type checking with confidence grades
- Evaluation with fuel tracking
- Pretty-printed results

#heading(level: 3)[B.8.7 Test Suite]

The implementation includes 35 QuickCheck and HUnit tests covering:

+---+---+---+
| **Module** | **Tests** | **Coverage** |
+---+---+---+
| `CLAIR.Test.Confidence` | 12 | Algebraic laws: ⊕ associativity, ⊗ identity, undercut monotonicity |
| `CLAIR.Test.Evaluator` | 14 | Beta reduction, primitive operations, belief evaluation |
| `CLAIR.Test.TypeChecker` | 6 | Type inference, subtyping, error cases |
| `CLAIR.Test.HelloWorld` | 3 | End-to-end belief formation and evaluation |
+---+---+---+

Sample QuickCheck properties:

```haskell
-- Probabilistic sum is associative
prop_oplus_assoc :: Confidence -> Confidence -> Confidence -> Bool
prop_oplus_assoc a b c =
  oplus a (oplus b c) == oplus (oplus a b) c

-- Undercut is monotonic in defeat strength
prop_undercut_monotonic :: Confidence -> Defeat -> Defeat -> Property
prop_undercut_monotonic c d1 d2 =
  d1 <= d2 ==> undercut d1 c >= undercut d2 c
```

All tests pass: `cabal test` → `35/35 tests passed`.

#heading(level: 3)[B.8.8 Building and Running]

#heading(level: 4)[Build]

```bash
cd implementation/haskell
cabal build
```

This compiles the REPL (`clair-repl`) and test suite (`clair-test`).

#heading(level: 4)[Run REPL]

```bash
cabal run clair-repl
```

#heading(level: 4)[Run Tests]

```bash
cabal test
```

#heading(level: 3)[B.8.9 Design Rationale]

The Haskell implementation makes specific design choices that differ from the Lean reference:

+---+---+---+
| **Aspect** | **Lean** | **Haskell** | **Rationale** |
+---+---+---+
| Confidence type | `Rat` (rational) | `Double` | Performance vs. precision tradeoff |
| Parser | Constructors only | Parsec | Usable surface syntax |
| Error handling | `Option Expr` | `Either EvalError` | Stack traces for debugging |
| Fuel | 1000 steps | 1,000,000 steps | Allow more complex programs |
| Substitution | Formal proof | Direct implementation | No proof burden, faster iteration |
+---+---+---+

These choices reflect the different purposes:
- **Lean**: Formal verification, mathematical rigor
- **Haskell**: Usability, testing, experimentation

#heading(level: 3)[B.8.10 Relation to Lean Formalization]

The Haskell implementation is verified against the Lean formalization by:

1. **Type system correspondence**: Haskell types mirror Lean inductive types
2. **Semantic equivalence**: Reduction rules match Lean's `step` relation
3. **Property-based testing**: QuickCheck laws reflect Lean theorems
4. **Test coverage**: Each Lean example has a corresponding Haskell test

Discrepancies are documented as limitations:
- `Double` precision may cause floating-point drift
- Substitution is not proven capture-avoiding
- Stratification is checked but not enforced statically

For production deployment, we recommend:
- Use arbitrary-precision rationals for confidence
- Add formal proofs for substitution correctness
- Implement static stratification analysis
- Add persistent justification storage

#v(1em)
