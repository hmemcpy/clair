# CLAIR Parser (Haskell)

A Haskell parser for CLAIR trace files with validation, DAG detection, and JSON export.

## CLAIR Format

```
b1 1.0 L0 @user "User asks about Python"
b2 0.95 L0 @self <b1 "Python is a programming language"
b3 0.90 L1 @self <b2 "It supports multiple paradigms"
```

Each line: `id confidence level source [justifications] "content"`

## Build

```bash
stack build
```

## Run

```bash
# Parse and validate
stack exec clair-parser -- -i input.clair

# Pretty print JSON
stack exec clair-parser -- -i input.clair -o output.json -p

# Validate only
stack exec clair-parser -- -i input.clair --validate
```

## Test

```bash
stack test
```

## Modules

- **Clair.Types** - Core data types (Belief, Confidence, Level, Source)
- **Clair.Parser** - Attoparsec-based parser
- **Clair.Validation** - DAG validation, cycle detection
- **Clair.JSON** - JSON export/import

## Features

- ✅ Parse CLAIR trace format
- ✅ Confidence bounds checking [0,1]
- ✅ Level validation (non-negative)
- ✅ DAG cycle detection
- ✅ Duplicate ID detection
- ✅ JSON export
- ✅ CLI interface

## Example

```haskell
import Clair.Parser
import Clair.Validation

main = do
  let input = "b1 1.0 L0 @user \"Hello\""
  case parseBelief input of
    Right b  -> print $ validateBelief b
    Left err -> putStrLn err
```
