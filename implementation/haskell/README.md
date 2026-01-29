# CLAIR Reference Interpreter

A Haskell implementation of the CLAIR language: Comprehensible LLM AI Intermediate Representation.

## Overview

CLAIR is a language for confidence-weighted justified belief with:
- **Confidence values** in [0,1] with calibrated reliability semantics
- **Defeasible reasoning** via justification graphs with undercut and rebut
- **Stratified self-reference** with discounted Löb axiom to prevent bootstrapping
- **Belief revision** operators for updating confidence-weighted beliefs
- **Multi-agent aggregation** with provenance tracking

## Building

```bash
# Build the library and tests
cabal build

# Run tests
cabal test

# Run the REPL
cabal run clair-repl
```

## Usage

### REPL

```bash
cabal run clair-repl
```

In the REPL:
```
> belief("rain", 0.8, [], none, none)
Belief "rain" (Confidence 0.8) [] None None

> let b1 = belief("sun", 0.9, [], none, none)
> let b2 = belief("clouds", 0.7, [], none, none)
> aggregate([b1, b2])
Aggregated (Confidence 0.97) [b1, b2]
```

### Library

```haskell
import CLAIR.Confidence
import CLAIR.Syntax
import CLAIR.TypeChecker
import CLAIR.Evaluator

-- Create a belief
let b = belief (Name "rain") (Confidence 0.8) [] None None

-- Apply undercut
let u = undercut (Defeat 0.5) b
-- u now has confidence 0.8 * (1 - 0.5) = 0.4

-- Apply rebut
let r = rebut (Defeat 0.6) b (Confidence 0.3)
-- Normalized: 0.3 / (0.3 + 0.6) = 1/3
```

## Module Structure

- **CLAIR.Confidence**: Core confidence algebra (oplus, otimes, undercut, rebut)
- **CLAIR.Syntax**: Abstract syntax trees for CLAIR expressions
- **CLAIR.Parser**: Parse CLAIR surface syntax
- **CLAIR.TypeChecker**: Bidirectional type checking with confidence grades
- **CLAIR.Evaluator**: Small-step operational semantics
- **CLAIR.Pretty**: Pretty-printing for debugging

## Testing

```bash
# Run all tests
cabal test

# Run with coverage
cabal test --enable-coverage

# Run specific test suite
cabal test clair-test --test-options="--pattern Confidence"
```

## Implementation Status

- [x] Confidence algebra
- [x] Syntax and types
- [x] Parser for basic expressions
- [x] Type checker
- [ ] Evaluator (in progress)
- [ ] REPL (basic)
- [ ] Test suite (growing)

## License

MIT
