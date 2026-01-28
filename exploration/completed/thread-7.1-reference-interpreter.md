# Thread 7.1: Reference Interpreter for CLAIR

> **Status**: Active exploration (Session 24)
> **Task**: 7.1 Reference interpreter — Write a minimal interpreter in Haskell or Lean that runs CLAIR programs
> **Question**: What would a minimal viable interpreter for CLAIR look like, and what design decisions are involved?

---

## 1. The Problem

CLAIR has extensive theoretical foundations documented across Threads 1-6 and 8-9. However, no working implementation exists. The goal of Task 7.1 is to design a **reference interpreter** that:

1. Demonstrates that CLAIR is implementable (beyond the theoretical Turing-completeness proof)
2. Provides a testable specification of CLAIR's semantics
3. Serves as a foundation for future compiler/runtime development
4. Validates the theoretical design against practical constraints

### 1.1 What Does "Reference Interpreter" Mean?

A **reference interpreter** prioritizes:
- **Clarity over performance**: Every step should be readable and match the formal specification
- **Completeness over optimization**: Support all language features, even inefficiently
- **Correctness over speed**: Proofs (in Lean) or tests (in Haskell) verify behavior

It is NOT meant to be:
- Production-ready
- Fast enough for real workloads
- A basis for industrial tooling

---

## 2. Prior Art Survey

### 2.1 Belief-Tracking Systems

**Truth Maintenance Systems (TMS)**:
- **JTMS (Doyle 1979)**: Maintains IN/OUT status for nodes. Uses justifications with IN-lists and OUT-lists.
- **ATMS (de Kleer 1986)**: Tracks all assumption environments. More complex but handles multiple contexts.
- **LTMS (McAllester 1990)**: Logical TMS combining aspects of both.

**Implementation languages**: Typically Lisp (Common Lisp, Scheme).

**Key lesson**: TMS implementations use dependency-directed propagation. When a node changes, only affected nodes are recomputed. CLAIR's DAG structure mirrors this.

**Subjective Logic implementations**:
- **SINTEF's Subjective Logic Library (Java)**: Implements (b, d, u, a) tuples and fusion operators
- **Jøsang's reference implementations**: Academic prototypes in various languages

**Key lesson**: Subjective Logic shows that belief representation with explicit uncertainty is tractable.

### 2.2 Dependently-Typed Language Interpreters

**Pie (Racket)**: From "The Little Typer" — a pedagogical dependently-typed language.
- Clean separation of type checking and evaluation
- Uses normalization-by-evaluation
- Small codebase (~2000 lines)

**Idris**: Full implementation with dependent types, tactics, and elaboration.
- Reference interpreter in Haskell
- Later self-hosted
- Demonstrates extraction from specifications

**Agda**: Dependently-typed functional language.
- Multiple backends (Haskell, JavaScript)
- Totality checking for termination

**Key lesson**: Dependent type systems can be implemented incrementally. Start with simple types, add dependency later.

### 2.3 Provenance-Tracking Interpreters

**PROV-DM implementations**: W3C provenance model.
- Libraries in Python, Java for tracking data provenance
- Graph-based representation of derivation history

**Curry-Howard interpreters**: Proof-carrying code.
- Extract computational content while maintaining proof terms
- Runtime overhead for proof representation

**Key lesson**: Provenance tracking can be implemented as metadata attached to values, propagated through evaluation.

### 2.4 Haskell vs Lean as Implementation Language

| Aspect | Haskell | Lean 4 |
|--------|---------|--------|
| **Maturity** | Very mature, extensive libraries | Newer, growing ecosystem |
| **Type system** | Expressive, practical | Dependently typed, extremely expressive |
| **Performance** | Good (GHC optimizations) | Good (compiled to C) |
| **Proof capability** | No built-in proofs | Full theorem prover |
| **Extraction** | N/A (it IS the executable) | Extract to executable code |
| **Ecosystem** | Huge (Hackage) | Growing (Mathlib, lake) |
| **Learning curve** | Moderate | Steep |

**Recommendation**: **Haskell** for the reference interpreter.

Rationale:
1. **Faster iteration**: Less ceremony than Lean for initial development
2. **Mature tooling**: GHC, Cabal/Stack, profiling tools
3. **Expressive enough**: GADTs, type families cover CLAIR's needs
4. **Readable**: Haskell code is more accessible for non-theorem-prover users
5. **Bridge to Lean**: The Haskell interpreter can serve as a specification; a Lean version can prove properties about a formalized version

However, **Lean 4** is the right choice if:
- We want machine-checked correctness from the start
- We plan to extract the interpreter from Lean proofs
- The Thread 8 formalization is complete enough to build on

---

## 3. CLAIR Core Language Analysis

From `formal/syntax.md`, `formal/derivation-calculus.md`, and exploration threads, the core CLAIR language includes:

### 3.1 Types

```
τ ::= Base                    -- Int, Bool, String, etc.
    | τ → τ                   -- Functions
    | τ × τ                   -- Products
    | τ + τ                   -- Sums
    | List τ                  -- Lists
    | Belief τ                -- Belief type
    | Effect ε τ              -- Effect type
    | { x : τ | φ }           -- Refinement type
```

### 3.2 Expressions

```
e ::= x                       -- Variable
    | λx:τ.e                  -- Lambda abstraction
    | e e                     -- Application
    | let x = e in e          -- Let binding
    | (e, e)                  -- Pair
    | fst e | snd e           -- Projections
    | inl e | inr e           -- Injections
    | case e of ...           -- Case analysis
    | fix f                   -- Fixed point (recursion)
    | primitives              -- Arithmetic, etc.

    -- Belief operations
    | belief e                -- Create belief with value
    | belief e @ c            -- Create belief with confidence
    | val e                   -- Extract value from belief
    | conf e                  -- Extract confidence
    | prov e                  -- Extract provenance
    | just e                  -- Extract justification
    | inv e                   -- Extract invalidation
    | derive e₁, ..., eₙ by r -- Derive new belief

    -- Decision operations
    | decide { ... }          -- Inline decision
```

### 3.3 Belief Representation

From Thread 1 (Confidence) and Thread 2 (Justification):

```
Belief<A> = {
  value      : A
  confidence : Confidence              -- [0,1] interval
  provenance : Provenance              -- Where did this come from?
  justification : JustificationGraph   -- DAG with labeled edges
  invalidation : Set<Condition>        -- When does this become invalid?
}

Confidence = { c : ℝ | 0 ≤ c ∧ c ≤ 1 }

Provenance =
  | Literal                           -- Hardcoded value
  | Input source                      -- External input
  | Derived (List ProvenanceRef)      -- Computed from other beliefs
  | Training                          -- From LLM training
  | Oracle                            -- External authority

JustificationNode =
  | Axiom
  | Rule r (List JustificationRef)
  | Assumption a
  | Choice options criteria reason
  | Abduction obs hyps selected reason
  | Analogy source similarity transfer
  | Induction instances rule
  | Aggregate lines combRule

EdgeType = Support | Undercut | Rebut

JustificationRef = (NodeId, EdgeType)

JustificationGraph = {
  nodes : Map NodeId JustificationNode
  root : NodeId
  -- Invariant: acyclic
}

Condition =
  | InputChanged source
  | AssumptionFalse assumption
  | ConfidenceBelow threshold
  | ConstraintViolated constraint
  | TimeElapsed duration
```

---

## 4. Design Decisions

### 4.1 Decision 1: Evaluation Strategy

**Question**: Should CLAIR be strict (eager) or lazy?

**Options**:
1. **Strict evaluation**: Evaluate arguments before function application
2. **Lazy evaluation**: Delay evaluation until value is needed
3. **Hybrid**: Strict by default with explicit laziness

**Analysis**:

Strict evaluation:
- Simpler implementation
- Predictable performance
- Confidence propagation is straightforward
- Matches most practical languages

Lazy evaluation:
- More expressive (infinite structures, etc.)
- Confidence of unevaluated expressions is undefined
- Provenance tracking becomes complex (what's the provenance of a thunk?)
- Invalidation checking is deferred

**Decision**: **Strict evaluation** for the reference interpreter.

Rationale:
1. CLAIR's focus is epistemic tracking, not expressiveness via laziness
2. Confidence must be computed at derivation time
3. Simpler implementation enables clearer correspondence to formal semantics
4. Can add laziness later if needed

### 4.2 Decision 2: Confidence Representation

**Question**: How should confidence values be represented at runtime?

**Options**:
1. **Float/Double**: Standard IEEE floating point
2. **Rational**: Exact rational arithmetic (Haskell's `Rational`)
3. **Fixed-point**: Integer representation (0-100 or 0-10000)
4. **Symbolic**: Keep formulas unevaluated

**Analysis**:

| Representation | Precision | Performance | Proof compatibility |
|----------------|-----------|-------------|---------------------|
| Float/Double | ~15 digits | Fast | Poor (rounding) |
| Rational | Exact | Moderate | Good |
| Fixed-point | Limited | Fast | Moderate |
| Symbolic | Exact | Slow | Excellent |

**Decision**: **Rational** for the reference interpreter.

Rationale:
1. Exact arithmetic matches the formal specification (ℝ subset)
2. Haskell's `Data.Ratio` is well-tested
3. Performance is acceptable for a reference interpreter
4. Can convert to Float for display/comparison
5. Avoids floating-point weirdness (0.1 + 0.2 ≠ 0.3)

### 4.3 Decision 3: Justification Graph Representation

**Question**: How should the DAG structure be represented?

**Options**:
1. **Explicit graph**: Nodes and edges as separate collections
2. **Algebraic data type**: Recursive ADT with sharing via references
3. **Hash-consed**: Deduplicated by content hash
4. **Indexed family**: Type-indexed representation for safety

**Analysis**:

From Thread 2, justifications are DAGs with:
- Shared premises (same belief used multiple times)
- Labeled edges (support, undercut, rebut)
- Acyclicity invariant

**Decision**: **Hash-consed algebraic data type** with explicit node IDs.

```haskell
type JustificationId = Int

data JustificationNode
  = JAxiom
  | JRule RuleName [(JustificationId, EdgeType)]
  | JAssumption Assumption
  | JChoice Options Criteria Reason
  | JAbduction JustificationId [JustificationId] Int Reason
  | JAnalogy JustificationId JustificationId TransferPrinciple
  | JInduction [JustificationId] InductiveRule
  | JAggregate [(JustificationId, CombinationRule)]

data EdgeType = Support | Undercut | Rebut

data JustificationGraph = JustificationGraph
  { jgNodes :: IntMap JustificationNode
  , jgRoot  :: JustificationId
  , jgNext  :: JustificationId  -- Next available ID
  }
```

Rationale:
1. Explicit IDs enable sharing without reference equality issues
2. IntMap provides efficient lookup
3. Acyclicity can be checked at construction time
4. Matches the formal specification closely

### 4.4 Decision 4: Error Handling

**Question**: How should type errors, runtime errors, and confidence-related errors be handled?

**Options**:
1. **Exceptions**: Throw and catch
2. **Either/Result**: Explicit error values
3. **Effect system**: Track errors in type
4. **Panic**: Fail hard on errors

**Decision**: **Either monad with typed errors**.

```haskell
data CLAIRError
  = TypeError String
  | ConfidenceOutOfBounds Rational
  | CyclicJustification JustificationId
  | InvalidationTriggered Condition
  | UndefinedVariable String
  | DivisionByZero
  | PatternMatchFailure

type CLAIRResult a = Either CLAIRError a
type CLAIR a = StateT InterpreterState (Either CLAIRError) a
```

Rationale:
1. Explicit error handling matches the epistemic focus
2. Can track what caused failures
3. No hidden control flow
4. Composable with State for interpreter state

### 4.5 Decision 5: Invalidation Checking

**Question**: When should invalidation conditions be checked?

**Options**:
1. **Eager**: Check on every access to a belief
2. **Lazy**: Check only when explicitly requested
3. **Periodic**: Check at specified intervals
4. **Event-driven**: Check when relevant events occur

**Decision**: **Lazy with explicit trigger**.

```haskell
checkValidity :: Belief a -> World -> CLAIR (Maybe InvalidationReason)

-- Usage pattern:
useBeliefValue :: Belief a -> CLAIR a
useBeliefValue belief = do
  world <- getCurrentWorld
  validity <- checkValidity belief world
  case validity of
    Nothing -> pure (beliefValue belief)
    Just reason -> throwError (InvalidationTriggered reason)
```

Rationale:
1. Eager checking is expensive (every access)
2. Lazy allows user control over when to validate
3. Matches CLAIR's philosophy: tracking, not proving
4. Can implement eager on top of lazy

---

## 5. Interpreter Architecture

### 5.1 Module Structure

```
CLAIR/
├── Types.hs           -- Core types (Confidence, Belief, etc.)
├── Syntax.hs          -- AST definition
├── Parser.hs          -- Surface syntax parser
├── TypeChecker.hs     -- Type checking
├── Confidence.hs      -- Confidence operations
├── Justification.hs   -- Justification DAG operations
├── Provenance.hs      -- Provenance tracking
├── Invalidation.hs    -- Invalidation checking
├── Evaluator.hs       -- Core evaluation
├── Primitives.hs      -- Built-in operations
├── World.hs           -- World state for invalidation
└── Main.hs            -- REPL and file execution
```

### 5.2 Core Types

```haskell
-- Types.hs

module CLAIR.Types where

import Data.Ratio (Rational)
import Data.IntMap (IntMap)
import Data.Set (Set)

-- | Confidence value in [0,1]
newtype Confidence = Confidence { getConfidence :: Rational }
  deriving (Eq, Ord, Show)

-- | Smart constructor enforcing bounds
mkConfidence :: Rational -> Either String Confidence
mkConfidence r
  | r < 0     = Left "Confidence cannot be negative"
  | r > 1     = Left "Confidence cannot exceed 1"
  | otherwise = Right (Confidence r)

-- | Belief type
data Belief a = Belief
  { beliefValue         :: a
  , beliefConfidence    :: Confidence
  , beliefProvenance    :: Provenance
  , beliefJustification :: JustificationGraph
  , beliefInvalidation  :: Set Condition
  } deriving (Show, Functor)

-- | Provenance tracking
data Provenance
  = PLiteral
  | PInput String
  | PDerived [ProvenanceRef]
  | PTraining
  | POracle String
  deriving (Show, Eq)

type ProvenanceRef = Int  -- Reference to another provenance node

-- | Justification graph
type JustificationId = Int

data JustificationGraph = JGraph
  { jgNodes :: IntMap JustificationNode
  , jgRoot  :: JustificationId
  , jgNextId :: JustificationId
  } deriving (Show)

data JustificationNode
  = JAxiom
  | JRule String [(JustificationId, EdgeType)]
  | JAssumption String
  | JChoice [String] [(String, Rational)] String
  | JAbduction JustificationId [JustificationId] Int String
  | JAnalogy JustificationId JustificationId String
  | JInduction [JustificationId] String
  | JAggregate [JustificationId] CombinationRule
  deriving (Show)

data EdgeType = Support | Undercut | Rebut
  deriving (Show, Eq)

data CombinationRule
  = Independent   -- Use probabilistic OR
  | Conservative  -- Use min
  | Multiplicative  -- Use product
  | Correlated Rational  -- Interpolation with dependency factor
  deriving (Show)

-- | Invalidation conditions
data Condition
  = InputChanged String
  | AssumptionFalse String
  | ConfidenceBelow Confidence
  | ConstraintViolated String
  | TimeElapsed Integer  -- milliseconds
  deriving (Show, Eq, Ord)
```

### 5.3 Confidence Operations

```haskell
-- Confidence.hs

module CLAIR.Confidence where

import CLAIR.Types

-- | Confidence multiplication (for derivation)
mulConf :: Confidence -> Confidence -> Confidence
mulConf (Confidence a) (Confidence b) = Confidence (a * b)

-- | Confidence minimum (conservative)
minConf :: Confidence -> Confidence -> Confidence
minConf (Confidence a) (Confidence b) = Confidence (min a b)

-- | Probabilistic OR (for aggregation)
oplusConf :: Confidence -> Confidence -> Confidence
oplusConf (Confidence a) (Confidence b) = Confidence (a + b - a * b)

-- | Undercut: multiplicative discounting
undercutConf :: Confidence -> Confidence -> Confidence
undercutConf (Confidence c) (Confidence d) = Confidence (c * (1 - d))

-- | Rebut: probabilistic comparison
rebutConf :: Confidence -> Confidence -> Confidence
rebutConf (Confidence cFor) (Confidence cAgainst)
  | cFor + cAgainst == 0 = Confidence (1 % 2)  -- maximal uncertainty
  | otherwise = Confidence (cFor / (cFor + cAgainst))

-- | Aggregate multiple confidences
aggregateConf :: CombinationRule -> [Confidence] -> Confidence
aggregateConf Independent confs =
  foldr oplusConf (Confidence 0) confs
aggregateConf Conservative confs =
  foldr minConf (Confidence 1) confs
aggregateConf Multiplicative confs =
  foldr mulConf (Confidence 1) confs
aggregateConf (Correlated delta) [c1, c2] =
  let indep = oplusConf c1 c2
      avg = Confidence ((getConfidence c1 + getConfidence c2) / 2)
      Confidence i = indep
      Confidence a = avg
  in Confidence ((1 - delta) * i + delta * a)
aggregateConf (Correlated _) _ =
  error "Correlated aggregation only defined for pairs"
```

### 5.4 Evaluation

```haskell
-- Evaluator.hs

module CLAIR.Evaluator where

import CLAIR.Types
import CLAIR.Confidence
import CLAIR.Justification
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map

-- | Runtime values
data Value
  = VInt Integer
  | VBool Bool
  | VString String
  | VPair Value Value
  | VLeft Value
  | VRight Value
  | VList [Value]
  | VClosure Env String Expr
  | VBelief (Belief Value)
  | VUnit
  deriving (Show)

-- | Environment
type Env = Map.Map String Value

-- | Interpreter state
data InterpreterState = IState
  { isEnv       :: Env
  , isWorld     :: World
  , isNextProv  :: Int
  , isNextJust  :: Int
  }

-- | World state for invalidation
data World = World
  { worldTime    :: Integer
  , worldInputs  :: Map.Map String Value
  , worldAssumptions :: Map.Map String Bool
  }

-- | The interpreter monad
type CLAIR a = StateT InterpreterState (Either CLAIRError) a

-- | Evaluate an expression
eval :: Expr -> CLAIR Value
eval expr = case expr of
  -- Variables
  EVar x -> do
    env <- gets isEnv
    case Map.lookup x env of
      Just v  -> pure v
      Nothing -> throwError (UndefinedVariable x)

  -- Lambda abstraction
  ELam x _ body -> do
    env <- gets isEnv
    pure (VClosure env x body)

  -- Application
  EApp f arg -> do
    fVal <- eval f
    argVal <- eval arg
    case fVal of
      VClosure env' x body -> do
        let env'' = Map.insert x argVal env'
        withEnv env'' (eval body)
      _ -> throwError (TypeError "Expected function")

  -- Let binding
  ELet x e body -> do
    v <- eval e
    withVar x v (eval body)

  -- Pairs
  EPair e1 e2 -> do
    v1 <- eval e1
    v2 <- eval e2
    pure (VPair v1 v2)

  EFst e -> do
    v <- eval e
    case v of
      VPair v1 _ -> pure v1
      _ -> throwError (TypeError "Expected pair")

  ESnd e -> do
    v <- eval e
    case v of
      VPair _ v2 -> pure v2
      _ -> throwError (TypeError "Expected pair")

  -- Sums
  EInl e -> VLeft <$> eval e
  EInr e -> VRight <$> eval e

  ECase e branches -> do
    v <- eval e
    matchBranches v branches

  -- Primitives
  EInt n -> pure (VInt n)
  EBool b -> pure (VBool b)
  EString s -> pure (VString s)

  -- Arithmetic
  EAdd e1 e2 -> binIntOp (+) e1 e2
  ESub e1 e2 -> binIntOp (-) e1 e2
  EMul e1 e2 -> binIntOp (*) e1 e2
  EDiv e1 e2 -> do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
      (VInt n1, VInt 0)  -> throwError DivisionByZero
      (VInt n1, VInt n2) -> pure (VInt (n1 `div` n2))
      _ -> throwError (TypeError "Expected integers")

  -- Comparison
  EEq e1 e2 -> binCmpOp (==) e1 e2
  ELt e1 e2 -> binCmpOp (<) e1 e2

  -- Boolean operations
  EAnd e1 e2 -> binBoolOp (&&) e1 e2
  EOr e1 e2 -> binBoolOp (||) e1 e2
  ENot e -> do
    v <- eval e
    case v of
      VBool b -> pure (VBool (not b))
      _ -> throwError (TypeError "Expected boolean")

  -- Conditionals
  EIf cond thenE elseE -> do
    condV <- eval cond
    case condV of
      VBool True  -> eval thenE
      VBool False -> eval elseE
      _ -> throwError (TypeError "Expected boolean condition")

  -- Fixed point (recursion)
  EFix f -> eval (EApp f (EFix f))

  -- === Belief Operations ===

  -- Create belief with value only (confidence 1.0)
  EBelief e -> do
    v <- eval e
    pure $ VBelief $ Belief
      { beliefValue = v
      , beliefConfidence = Confidence 1
      , beliefProvenance = PLiteral
      , beliefJustification = axiomJust
      , beliefInvalidation = mempty
      }

  -- Create belief with confidence
  EBeliefAt e c -> do
    v <- eval e
    conf <- evalConfidence c
    pure $ VBelief $ Belief
      { beliefValue = v
      , beliefConfidence = conf
      , beliefProvenance = PLiteral
      , beliefJustification = axiomJust
      , beliefInvalidation = mempty
      }

  -- Extract value from belief
  EVal e -> do
    v <- eval e
    case v of
      VBelief b -> pure (beliefValue b)
      _ -> throwError (TypeError "Expected belief")

  -- Extract confidence
  EConf e -> do
    v <- eval e
    case v of
      VBelief b -> pure (VConfidence (beliefConfidence b))
      _ -> throwError (TypeError "Expected belief")

  -- Derive new belief from existing beliefs
  EDerive beliefs rule combRule -> do
    bVals <- mapM eval beliefs
    bs <- mapM extractBelief bVals
    deriveFromBeliefs rule combRule bs

-- | Derive a new belief from premises
deriveFromBeliefs :: String -> CombinationRule -> [Belief Value] -> CLAIR Value
deriveFromBeliefs ruleName combRule premises = do
  -- Compute new confidence based on combination rule
  let premiseConfs = map beliefConfidence premises
  let newConf = aggregateConf combRule premiseConfs

  -- Build justification graph
  premiseJusts <- mapM (addToJustGraph . beliefJustification) premises
  let newJust = mkRuleJustification ruleName (map (\j -> (j, Support)) premiseJusts)

  -- Combine provenances
  let newProv = PDerived (map (const 0) premises)  -- simplified

  -- Combine invalidation conditions
  let newInv = foldMap beliefInvalidation premises

  -- The actual value computation depends on the rule
  -- For now, return unit (actual implementation would apply the rule)
  pure $ VBelief $ Belief
    { beliefValue = VUnit  -- Should be: applyRule ruleName (map beliefValue premises)
    , beliefConfidence = newConf
    , beliefProvenance = newProv
    , beliefJustification = newJust
    , beliefInvalidation = newInv
    }

-- Helper functions
extractBelief :: Value -> CLAIR (Belief Value)
extractBelief (VBelief b) = pure b
extractBelief _ = throwError (TypeError "Expected belief")

withVar :: String -> Value -> CLAIR a -> CLAIR a
withVar x v action = do
  oldEnv <- gets isEnv
  modify (\s -> s { isEnv = Map.insert x v (isEnv s) })
  result <- action
  modify (\s -> s { isEnv = oldEnv })
  pure result

withEnv :: Env -> CLAIR a -> CLAIR a
withEnv env action = do
  oldEnv <- gets isEnv
  modify (\s -> s { isEnv = env })
  result <- action
  modify (\s -> s { isEnv = oldEnv })
  pure result

binIntOp :: (Integer -> Integer -> Integer) -> Expr -> Expr -> CLAIR Value
binIntOp op e1 e2 = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VInt n1, VInt n2) -> pure (VInt (op n1 n2))
    _ -> throwError (TypeError "Expected integers")

binCmpOp :: (Integer -> Integer -> Bool) -> Expr -> Expr -> CLAIR Value
binCmpOp op e1 e2 = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VInt n1, VInt n2) -> pure (VBool (op n1 n2))
    _ -> throwError (TypeError "Expected integers")

binBoolOp :: (Bool -> Bool -> Bool) -> Expr -> Expr -> CLAIR Value
binBoolOp op e1 e2 = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VBool b1, VBool b2) -> pure (VBool (op b1 b2))
    _ -> throwError (TypeError "Expected booleans")
```

---

## 6. Key Implementation Challenges

### 6.1 Challenge 1: Justification DAG Acyclicity

The formal specification requires justification graphs to be acyclic (well-foundedness from Thread 2). How do we enforce this?

**Approach**: Check acyclicity on construction.

```haskell
-- | Add an edge to the justification graph, checking for cycles
addJustificationEdge :: JustificationId -> JustificationId -> EdgeType
                     -> JustificationGraph -> Either CLAIRError JustificationGraph
addJustificationEdge from to edgeType graph = do
  -- Check if adding this edge would create a cycle
  if canReach graph to from
    then Left (CyclicJustification from)
    else Right (insertEdge from to edgeType graph)

-- | Check if there's a path from src to dst
canReach :: JustificationGraph -> JustificationId -> JustificationId -> Bool
canReach graph src dst = go mempty src
  where
    go visited current
      | current == dst = True
      | current `Set.member` visited = False
      | otherwise =
          let visited' = Set.insert current visited
              children = getChildren graph current
          in any (go visited') children
```

### 6.2 Challenge 2: Defeat Evaluation Order

From Thread 2.10 and 2.12: when evaluating a belief with defeaters, the order matters:
1. First evaluate all support edges
2. Then apply undercuts (weaken inference)
3. Then compare against rebuts (competing conclusions)

**Approach**: Multi-pass evaluation.

```haskell
evaluateConfidenceWithDefeat :: JustificationGraph -> JustificationId -> CLAIR Confidence
evaluateConfidenceWithDefeat graph nodeId = do
  let node = lookupNode graph nodeId
  let edges = getEdges graph nodeId

  -- Partition edges by type
  let (supports, undercuts, rebuts) = partitionEdges edges

  -- Step 1: Compute base confidence from supports
  supportConfs <- mapM (evaluateConfidenceWithDefeat graph . fst) supports
  let baseConf = aggregateConf Independent supportConfs

  -- Step 2: Apply undercuts
  undercutConfs <- mapM (evaluateConfidenceWithDefeat graph . fst) undercuts
  let combinedUndercut = foldr oplusConf (Confidence 0) undercutConfs
  let afterUndercut = undercutConf baseConf combinedUndercut

  -- Step 3: Compare against rebuts
  rebutConfs <- mapM (evaluateConfidenceWithDefeat graph . fst) rebuts
  let combinedRebut = foldr oplusConf (Confidence 0) rebutConfs
  let finalConf = rebutConf afterUndercut combinedRebut

  pure finalConf
```

### 6.3 Challenge 3: Reinstatement

From Thread 2.12: when a defeater is itself defeated, the original belief should be reinstated. This emerges compositionally from bottom-up evaluation.

**Key insight**: The evaluation above already handles this! When we evaluate undercut confidences, we recursively evaluate their defeaters, so a weakened defeater has reduced undercutting power.

### 6.4 Challenge 4: Correlated Evidence Detection

From Thread 2.13: evidence from the same source should not be treated as independent.

**Approach**: Check provenance overlap.

```haskell
-- | Estimate dependency factor from provenance overlap
estimateDependency :: Provenance -> Provenance -> Rational
estimateDependency p1 p2 =
  let ancestors1 = collectAncestors p1
      ancestors2 = collectAncestors p2
      intersection = Set.intersection ancestors1 ancestors2
      union = Set.union ancestors1 ancestors2
  in if Set.null union
     then 0  -- No shared ancestry, independent
     else fromIntegral (Set.size intersection) / fromIntegral (Set.size union)
```

### 6.5 Challenge 5: Type Checking with Beliefs

CLAIR's type system includes `Belief<A>` types. How do we type check belief operations?

```haskell
-- Type checking for belief operations
typeCheck :: Env -> Expr -> Either TypeError Type
typeCheck env expr = case expr of
  -- ...

  EBelief e -> do
    t <- typeCheck env e
    pure (TBelief t)

  EVal e -> do
    t <- typeCheck env e
    case t of
      TBelief a -> pure a
      _ -> Left (ExpectedBelief t)

  EConf e -> do
    t <- typeCheck env e
    case t of
      TBelief _ -> pure TConfidence
      _ -> Left (ExpectedBelief t)

  EDerive beliefs rule combRule -> do
    ts <- mapM (typeCheck env) beliefs
    -- All must be belief types
    case sequence (map unwrapBelief ts) of
      Nothing -> Left (ExpectedBeliefs ts)
      Just innerTypes -> do
        -- Rule determines output type
        outType <- inferRuleOutputType rule innerTypes
        pure (TBelief outType)
```

---

## 7. Testing Strategy

### 7.1 Unit Tests

For each component:
- **Confidence operations**: Test all algebraic properties (boundedness, associativity, etc.)
- **Justification graphs**: Test acyclicity checking, edge addition, traversal
- **Evaluation**: Test each expression form with simple inputs

### 7.2 Integration Tests

- **Derivation chains**: Create beliefs, derive new beliefs, check confidence propagation
- **Defeat scenarios**: Test undercut, rebut, and reinstatement
- **Invalidation**: Test that invalid beliefs are detected

### 7.3 Property-Based Tests (QuickCheck)

```haskell
-- Confidence operations preserve bounds
prop_confidenceBounded :: Confidence -> Confidence -> Bool
prop_confidenceBounded c1 c2 =
  let result = oplusConf c1 c2
  in getConfidence result >= 0 && getConfidence result <= 1

-- Undercuts compose via oplus
prop_undercutCompose :: Confidence -> Confidence -> Confidence -> Bool
prop_undercutCompose c d1 d2 =
  undercutConf (undercutConf c d1) d2 == undercutConf c (oplusConf d1 d2)

-- Derivation only decreases confidence (for multiplication)
prop_derivationDecreases :: Confidence -> Confidence -> Bool
prop_derivationDecreases c1 c2 =
  let result = mulConf c1 c2
  in result <= c1 && result <= c2
```

### 7.4 Regression Tests

- Known examples from formal documents
- Edge cases discovered during development
- Examples from prior art (TMS, Subjective Logic)

---

## 8. What This Exploration Revealed

### 8.1 Key Insights

**Insight 1: The core interpreter is straightforward**

The basic evaluation of expressions is standard lambda calculus with products, sums, and primitives. The novel part is the belief operations, which have clear semantics from Threads 1-2.

**Insight 2: Confidence operations are well-defined**

All operations (×, min, ⊕, undercut, rebut) have been proven correct in Thread 8. Implementation is direct translation.

**Insight 3: Justification DAGs require careful handling**

The DAG structure with labeled edges and acyclicity invariant is the most complex part. But the design from Thread 2 is implementable.

**Insight 4: Evaluation order matters for defeat**

The three-phase evaluation (supports → undercuts → rebuts) must be respected. This is cleanly implementable with recursive descent.

**Insight 5: Lazy evaluation is problematic for CLAIR**

Laziness complicates confidence tracking (what's the confidence of an unevaluated thunk?). Strict evaluation is the right choice.

### 8.2 Remaining Questions

1. **Parser design**: What surface syntax should CLAIR use? The existing `syntax.md` provides guidance but isn't a formal grammar.

2. **Module system**: How do CLAIR modules interact? Imports, exports, visibility.

3. **Effects**: The syntax mentions `Effect<e, a>` types. How are effects implemented?

4. **Decisions**: The decision syntax is rich. How exactly are decisions evaluated and tracked?

5. **Extraction**: Can we extract the interpreter from Lean proofs for verified execution?

### 8.3 Scope for Reference Interpreter

For the **minimal viable reference interpreter**, I recommend:

**Include**:
- Core lambda calculus (λ, application, let, fix)
- Products and sums with pattern matching
- Base types (Int, Bool, String)
- Belief type with value, confidence, provenance, justification
- Basic belief operations (belief, val, conf, derive)
- Confidence propagation (multiply, min, oplus)
- Justification DAG tracking
- Simple invalidation (manual checking)

**Exclude initially**:
- Effect system
- Full decision syntax
- Modules and imports
- Refinement types
- Parser (use Haskell DSL for testing)

This gives a working core that demonstrates CLAIR's novel features without the complexity of a full language implementation.

---

## 9. Recommended Next Steps

### 9.1 Immediate (Task 7.1 Implementation)

1. **Set up Haskell project**: cabal/stack project with test framework
2. **Implement `CLAIR.Types`**: Core type definitions
3. **Implement `CLAIR.Confidence`**: All confidence operations with tests
4. **Implement `CLAIR.Justification`**: DAG operations with acyclicity
5. **Implement `CLAIR.Evaluator`**: Core evaluation with belief operations
6. **Write test suite**: Unit tests, property tests, integration tests

### 9.2 Follow-up Tasks

1. **Task 7.2 (Runtime representation)**: Design efficient runtime for beliefs
2. **Task 7.3 (Compilation)**: Explore LLVM/WASM compilation
3. **Task 7.4 (Serialization)**: Design belief serialization format

### 9.3 Connection to Thread 8

The Haskell reference interpreter should correspond to the Lean formalization:
- Types should match (modulo representation)
- Operations should have the same semantics
- Eventually: extract Lean code and compare against Haskell

---

## 10. Conclusion

**Task 7.1 is ready for implementation.**

The reference interpreter design is complete:
- **Language**: Haskell (clearer, faster iteration)
- **Evaluation**: Strict (simpler, matches epistemic tracking)
- **Confidence**: Rational (exact, matches specification)
- **Justification**: Hash-consed DAG with explicit IDs
- **Errors**: Either monad with typed errors
- **Invalidation**: Lazy with explicit triggers

The core challenge is implementing the justification DAG correctly, with acyclicity invariants and proper defeat evaluation order. The theoretical foundations from Threads 1-2 and 8 provide clear guidance.

**Estimated scope for minimal interpreter**: ~1000-1500 lines of Haskell

**Key deliverables**:
1. Working interpreter that evaluates CLAIR expressions
2. Belief tracking with confidence propagation
3. Justification DAG construction and traversal
4. Test suite verifying algebraic properties

---

## 11. References

### Implementation Prior Art

- **Doyle, J.** (1979). "A Truth Maintenance System." *Artificial Intelligence*, 12(3), 231-272.
- **de Kleer, J.** (1986). "An Assumption-based TMS." *Artificial Intelligence*, 28(2), 127-162.
- **Jøsang, A.** (2016). *Subjective Logic: A Formalism for Reasoning Under Uncertainty.* Springer.
- **Friedman, D. & Christiansen, D.** (2018). *The Little Typer.* MIT Press.
- **Brady, E.** (2013). "Idris, a general-purpose dependently typed programming language." *JFP*, 23(5), 552-593.

### CLAIR Formal Foundations

- `formal/syntax.md` — Language syntax
- `formal/derivation-calculus.md` — Derivation semantics
- `formal/turing-completeness.md` — Computational power
- `exploration/thread-1-confidence.md` — Confidence semantics
- `exploration/thread-2-justification.md` — Justification structure
- `exploration/thread-8-verification.md` — Lean formalization

---

*Thread 7.1 Status: Design complete. Ready for implementation. Core interpreter architecture defined. Recommended language: Haskell. Estimated size: 1000-1500 lines for minimal viable interpreter.*
