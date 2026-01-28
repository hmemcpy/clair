# CLAIR Syntax Reference

This document provides a practical reference for CLAIR syntax.

## 1. Basic Structure

### Modules

```clair
module ModuleName where

-- Module-level metadata
program:
  intent: "description"
  confidence: 0.95
  assumes: [assumption1, assumption2]

-- Declarations
type MyType = ...
decision my_decision = ...
function_name : Type
function_name = ...
```

### Comments

```clair
-- Single line comment

{-
  Multi-line
  comment
-}
```

## 2. Types

### Base Types

```clair
Int                     -- Integer
Nat                     -- Natural number (>= 0)
Float                   -- Floating point
Bool                    -- Boolean
String                  -- Text
Bytes                   -- Raw bytes
Unit                    -- Unit type (like void)
```

### Compound Types

```clair
List<a>                 -- List of a
Option<a>               -- Optional value
Result<a, e>            -- Success a or error e
Tuple<a, b>             -- Pair
Map<k, v>               -- Key-value map
```

### Belief Types

```clair
Belief<a>               -- Belief about a value of type a

-- A Belief<Int> contains:
--   value: Int
--   confidence: Float in [0,1]
--   provenance: Provenance
--   justification: Justification
--   invalidation: Set<Condition>
```

### Refinement Types

```clair
{ x : Int | x > 0 }           -- Positive integer
{ s : String | length s > 0 } -- Non-empty string
{ t : Int | t >= 0 }          -- Natural (alternative syntax)
```

### Type Aliases

```clair
type UserId = { x : Int | x > 0 }
type NonEmptyString = { s : String | length s > 0 }
type Secret = { s : Bytes | length s >= 32 }
```

### Algebraic Data Types

```clair
type AuthMethod
  = JWT JWTConfig
  | Session SessionConfig
  | OAuth OAuthConfig

type Result<a, e>
  = Ok a
  | Err e

type Option<a>
  = Some a
  | None
```

### Effect Types

```clair
Effect<e, a>            -- Computation with effect e returning a

-- Common effects
IO                      -- Input/output
State<s>                -- Mutable state
Error<e>                -- Can fail with e
Async                   -- Asynchronous
```

## 3. Expressions

### Literals

```clair
42                      -- Int
3.14                    -- Float
true, false             -- Bool
"hello"                 -- String
[1, 2, 3]              -- List
(1, "two")             -- Tuple
```

### Let Bindings

```clair
let x = 42
let x : Int = 42        -- with type annotation

let result =
  let a = compute_a()
  let b = compute_b(a)
  combine(a, b)
```

### Functions

```clair
-- Definition
add : Int -> Int -> Int
add x y = x + y

-- Anonymous
\x -> x + 1
\x y -> x + y

-- Application
add 1 2
f(x)                    -- also valid
```

### Conditionals

```clair
if condition then
  true_branch
else
  false_branch

-- Pattern matching
case value of
  Pattern1 -> result1
  Pattern2 x -> result2 x
  _ -> default_result
```

### Do Notation (for effects)

```clair
do
  x <- action1
  y <- action2 x
  return (x + y)
```

## 4. Beliefs

### Creating Beliefs

```clair
-- Full form
let b : Belief<Int> =
  belief
    value: 42
    confidence: 0.95
    provenance: input("database")
    justification: axiom
    invalidation: {input_changed("database")}

-- Short form (high confidence, literal)
let b : Belief<Int> = belief 42

-- With just confidence
let b : Belief<Int> = belief 42 @ 0.9
```

### Accessing Belief Components

```clair
val b                   -- Extract value: Int
conf b                  -- Extract confidence: Float
prov b                  -- Extract provenance: Provenance
just b                  -- Extract justification: Justification
inv b                   -- Extract invalidation: Set<Condition>
```

### Deriving Beliefs

```clair
let result : Belief<Int> =
  derive a, b by (+)

-- With metadata
let result : Belief<Int> =
  derive a, b by (+)
    confidence: 0.9
    intent: "compute sum"
    why: "need total for report"
```

## 5. Decisions

### Decision Declaration

```clair
decision auth_method : d:auth:001
  question: "How should users authenticate?"

  constraints:
    c1: "Must be stateless"
    c2: "Must handle expiry"

  criteria:
    simplicity: weight 0.6
    security: weight 0.9

  options:
    jwt:
      satisfies: [c1, c2]
      scores: {simplicity: 0.8, security: 0.7}
      status: selected

    sessions:
      violates: c1 because "Requires server state"
      status: rejected

  selected: jwt
  rationale: "Satisfies all constraints, good balance"
  confidence: 0.91

  assumptions:
    - "Single service deployment"

  revisit_if:
    - assumption_false("Single service deployment")
    - constraint_added("asymmetric trust")
```

### Inline Decisions

```clair
let method : Belief<AuthMethod> =
  decide
    question: "Which algorithm?"
    options: [hs256, rs256]
    constraints: [available_key_type]
    criteria: [simplicity]
    selected: hs256
    rationale: "Simpler for single service"
```

## 6. Intents and Metadata

### Function-Level

```clair
verify_token : Secret -> Bytes -> Result<Claims, Error>
  intent: "Validate JWT and extract claims"
  confidence: 0.91
  assumes:
    - "Secret key is valid"
    - "Token is base64 encoded"
  realizes: secure_authentication

verify_token secret token = ...
```

### Block-Level

```clair
block parse
  intent: "Split token into parts"
  confidence: 0.98

  let parts = split token "."
  ...
```

### Expression-Level

```clair
let sig = compute_hmac key data
  intent: "Generate signature for verification"
  confidence: 0.95
  why: "Using HMAC-SHA256 per JWT spec"
```

## 7. Verification

### Postconditions

```clair
verify
  realizes: effect(stdout, write, greeting)
  postcondition: "greeting emitted exactly once"
```

### Assertions

```clair
assert (length parts == 3)
  why: "JWT must have exactly 3 parts"
  confidence: 1.0
```

## 8. Common Patterns

### Error Handling with Beliefs

```clair
validate : Bytes -> Result<Belief<Token>, Error>
validate input =
  case parse input of
    Err e -> Err e
    Ok token ->
      let validated = verify token
      if conf validated < 0.5 then
        Err (LowConfidence (conf validated))
      else
        Ok validated
```

### Propagating Confidence

```clair
-- Confidence flows through derivation
let a : Belief<Int> = belief 10 @ 0.9
let b : Belief<Int> = belief 20 @ 0.8
let c : Belief<Int> = derive a, b by (+)
-- c has confidence ~0.72 (0.9 * 0.8)
```

### Checking Invalidation

```clair
if is_invalid user_belief current_world then
  let refreshed = fetch_user(user_id)
  -- Use refreshed belief
else
  -- Use cached belief
```

## 9. Module Structure Example

```clair
module Auth where

-- Types
type Token = ...
type Claims = ...
type Error = ...

-- Decisions (module-level)
decision auth_method : d:auth:001
  ...

-- Functions
verify_token : Secret -> Bytes -> Result<Claims, Error>
  intent: "Main authentication entry point"
verify_token = ...

-- Internal helpers
parse_token : Bytes -> Result<TokenParts, Error>
  intent: "Parse raw bytes into token structure"
parse_token = ...

-- Exports (if needed)
export verify_token
```

## 10. Syntax Summary

| Construct | Syntax |
|-----------|--------|
| Module | `module Name where` |
| Type alias | `type Name = ...` |
| ADT | `type Name = A \| B x` |
| Refinement | `{ x : T \| pred }` |
| Function | `f : A -> B` / `f x = ...` |
| Belief | `Belief<T>` / `belief v @ c` |
| Derive | `derive a, b by rule` |
| Decision | `decision name : id ...` |
| Intent | `intent: "..."` |
| Confidence | `confidence: 0.95` |
| Let | `let x = e` |
| If | `if c then t else f` |
| Case | `case e of P -> r` |
| Do | `do { x <- a; y <- b; return z }` |
| Block | `block name ... ` |
