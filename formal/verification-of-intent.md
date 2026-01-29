# Verification of Intent

This document explores how we might verify that CLAIR implementations match their stated intents.

## 1. The Gap Between Tracking and Proving

CLAIR is a tracking system:
- Records intent: `intent: "validate JWT and extract claims"`
- Records implementation: the actual code
- Records confidence: `0.91`

But it doesn't prove: "The implementation actually does what the intent says."

**This is the gap.** Can we bridge it?

## 2. What Would Verification Mean?

### The Realizability Judgment

We introduced:
```
e ⊨ ι    "e realizes intent ι"
```

But what does this *mean*?

### Possible Interpretations

**Interpretation 1: Syntactic Matching**
```
e ⊨ ι  iff  ι is literally true of e's syntax

Example:
  intent: "function takes two arguments"
  check: count_args(e) == 2
```

This is trivial and not very useful.

**Interpretation 2: Behavioral Specification**
```
e ⊨ ι  iff  e satisfies the formal specification derived from ι

Example:
  intent: "returns positive number"
  spec: ∀ input. result(e, input) > 0
  check: prove or test the spec
```

This requires translating intent to formal spec.

**Interpretation 3: Semantic Entailment**
```
e ⊨ ι  iff  the meaning of e entails the meaning of ι

Example:
  intent: "sort the list"
  meaning(e): permutes input and orders elements
  check: meaning(e) ⊆ meaning("sort the list")
```

This requires formalizing "meaning" (hard).

**Interpretation 4: Probabilistic Satisfaction**
```
e ⊨_p ι  iff  e satisfies ι with probability p

Example:
  intent: "handle most error cases"
  check: P(e handles error | error occurs) > 0.95
```

This requires a probability model.

## 3. Levels of Verification

### Level 0: No Verification
```
Intent is just a string. We hope it matches. Trust the author.
```

### Level 1: Syntactic Checks
```
Intent parsed into checkable properties:
  intent: "pure function" → check: no side effects in syntax
  intent: "total function" → check: all cases covered
```

### Level 2: Type-Based Verification
```
Intent encoded in types:
  intent: "returns non-empty list" → return type: NonEmpty<A>
  intent: "input is positive" → param type: Pos
```

The type checker verifies intent.

### Level 3: Contract-Based Verification
```
Intent becomes preconditions/postconditions:
  intent: "sort the list"
  precondition: is_list(input)
  postcondition: is_sorted(output) ∧ is_permutation(output, input)
```

Checked at runtime or via static analysis.

### Level 4: Theorem Proving
```
Intent becomes a theorem to prove:
  intent: "correctly implements quicksort"
  theorem: ∀ xs. sort(xs) = quicksort_spec(xs)
  proof: by induction on xs
```

Full formal verification in Coq/Lean/etc.

### Level 5: Semantic Verification
```
Intent in natural language, verified by semantic analysis:
  intent: "authenticate users securely"
  analysis: NLP + formal methods + domain knowledge
```

This is AI-complete (as hard as general AI).

## 4. Practical Approach: Stratified Intent

Different intents get different verification:

```clair
function verify_token(token: Bytes) -> Result<Claims, Error>

  -- Level 4: Formally verified
  ensures: is_err(result) ∨ valid_jwt(token, result.claims)
  proof: verified_in("Auth.lean")

  -- Level 3: Contract checked at runtime
  requires: length(token) > 0
  ensures: is_ok(result) → claims_not_expired(result.claims, now())

  -- Level 2: Type-level
  -- Return type Result<Claims, Error> encodes success/failure

  -- Level 1: Syntactic
  -- No IO effects (pure function) - checkable from syntax

  -- Level 0: Informal
  intent: "Validate JWT and extract claims, rejecting expired or tampered tokens"
  -- This is documentation, not verified
```

## 5. Connecting Intent to Specification

### The Translation Problem

```
Natural language intent → Formal specification
```

This is hard because:
- Natural language is ambiguous
- Specifications require precision
- There may be multiple valid interpretations

### Structured Intent

Instead of free-form natural language, use structured intent:

```clair
intent:
  action: "validate"
  object: "JWT token"
  success_condition: "token is valid and not expired"
  failure_condition: "token is invalid, expired, or malformed"
  security_property: "reject tampered tokens"

-- This can be mechanically translated to:
spec:
  valid(token) ∧ ¬expired(token) → returns(Ok(claims))
  ¬valid(token) ∨ expired(token) ∨ malformed(token) → returns(Err(_))
  tampered(token) → returns(Err(_))
```

### Intent Templates

Define templates for common intents:

```clair
intent_template Sort<A: Ord>:
  action: "sort"
  input: List<A>
  output: List<A>
  spec:
    is_permutation(output, input)
    is_sorted(output)

intent_template Authenticate:
  action: "authenticate"
  input: Credential
  output: Result<Session, AuthError>
  spec:
    valid(input) → is_ok(output)
    ¬valid(input) → is_err(output)
    -- Plus security properties...
```

## 6. Refinement Types for Intent

### Intent as Refinement

```clair
-- Instead of:
verify_token : Bytes -> Result<Claims, Error>
  intent: "reject expired tokens"

-- Use refinement types:
verify_token : (token : Bytes)
             -> (r : Result<Claims, Error> |
                 is_ok(r) → ¬expired(token, now()))
```

The intent IS the type. Type checking IS verification.

### Liquid Haskell Style

```haskell
{-@ verify_token :: token:Bytes
                 -> {r:Result Claims Error |
                     isOk r => not (expired token)} @-}
verify_token :: Bytes -> Result Claims Error
verify_token token = ...
```

### Dependent Types Style (Lean/Idris)

```lean
def verify_token (token : Bytes) :
  { r : Result Claims Error // r.isOk → ¬expired token (now ()) } :=
  ...
```

## 7. The Confidence Connection

### Verification Affects Confidence

```clair
-- Unverified intent
intent: "sorts the list"
confidence: 0.85  -- we hope it does

-- Verified intent
intent: "sorts the list"
verified_by: "Sort.lean:theorem_sort_correct"
confidence: 1.0  -- proven!

-- Partially verified
intent: "sorts the list"
tested_by: ["quickcheck:1000 cases passed"]
confidence: 0.99  -- very likely
```

### Confidence Sources

```clair
type ConfidenceSource =
  | Proof (file: String, theorem: String)      -- confidence: 1.0
  | TypeChecked                                -- confidence: 1.0 (for type-level)
  | ContractChecked (method: Static | Runtime) -- confidence: 0.95-0.99
  | PropertyTested (cases: Nat, passed: Nat)   -- confidence: f(passed/cases)
  | CodeReviewed (reviewer: Agent)             -- confidence: 0.8-0.9
  | Unverified                                 -- confidence: as stated
```

## 8. What Can't Be Verified

### Gödel Strikes Again

Some intents are unverifiable:
- "This function always terminates" — undecidable in general
- "This code has no bugs" — too vague
- "This is secure against all attacks" — infinite attack surface

### Semantic Gap

Some intents require understanding we don't have:
- "Provides good user experience" — what is "good"?
- "Is efficient enough" — what is "enough"?
- "Handles edge cases appropriately" — which cases? what's appropriate?

### The Residual

Even with maximal verification, some intent remains informal:

```clair
verify_token
  -- Verified:
  type_safe: ✓
  contracts_hold: ✓
  theorem_proven: ∀ token. valid_jwt(token) → correct_claims(result)

  -- Unverified (informal intent):
  "good error messages for debugging"
  "reasonable performance"
  "follows team coding conventions"
```

## 9. Practical Recommendations

### For CLAIR Design

1. **Support multiple verification levels** — let users choose
2. **Make verification status explicit** — part of the belief metadata
3. **Integrate with existing verifiers** — Liquid Haskell, Dafny, Lean
4. **Provide intent templates** — for common patterns
5. **Track verification debt** — unverified intents are technical debt

### For CLAIR Users

1. **Start with types** — Level 2 is often enough
2. **Add contracts for critical code** — Level 3
3. **Prove security properties** — Level 4 for crypto, auth
4. **Accept informal intent** — Level 0 for documentation

### For Tooling

```clair
-- Tool: clair-verify

$ clair-verify auth.clair

Intent verification report:

verify_token:
  [✓] Type-level: return type encodes error cases
  [✓] Contract: requires length(token) > 0
  [✓] Contract: ensures valid → not expired
  [?] Property: "rejects tampered tokens" - tested 1000 cases, 0 failures
  [!] Unverified: "good error messages" - informal intent

Overall: 87% of intents machine-verified
         13% remain informal

Recommendation: Add theorem for tamper-rejection property
```

## 10. Connection to Beliefs

### Verification as Belief Strengthening

```clair
-- Before verification
let impl = verify_token
  confidence: 0.85
  justification: (authored_by: "smith", reviewed_by: "human")

-- After verification
let impl = verify_token
  confidence: 0.99
  justification: (authored_by: "smith",
                  reviewed_by: "human",
                  verified_by: "lean_proof")
```

Verification increases confidence and strengthens justification.

### Verification Doesn't Change Truth

Important: Verification doesn't make code *correct*. It provides *evidence* of correctness.

```clair
-- Verified but wrong (spec was wrong)
intent: "return n + 1"
spec: result == n + 1
impl: n + 2
proof: valid (proves impl matches spec)
but: spec doesn't match actual intent!

-- Confidence is high (proof exists)
-- Correctness is low (spec was wrong)
```

This is why we need both:
- **Verification**: evidence that impl matches spec
- **Validation**: evidence that spec matches intent

CLAIR tracks both.

## 11. Summary

| Level | What's Verified | Confidence Boost |
|-------|-----------------|------------------|
| 0 | Nothing | None |
| 1 | Syntax | Low (+0.05) |
| 2 | Types | Medium (+0.10) |
| 3 | Contracts | High (+0.15) |
| 4 | Theorems | Very High (+0.20) |
| 5 | Semantics | Maximal (but rarely achievable) |

The gap between "tracking intent" and "proving intent" cannot be fully closed (Gödel). But it can be narrowed through progressively stronger verification.

CLAIR's role: make the verification status explicit, integrate with verification tools, and track confidence accordingly.
