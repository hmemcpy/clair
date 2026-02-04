# C1: Query Pattern Catalog

## Research Question

What types of questions can humans ask of CLAIR traces, and how do these map to graph traversal operations? The auditability value proposition depends on whether traces can answer natural "why" questions effectively.

**Thesis Connection:** This explores the "human in the loop" value proposition. If CLAIR traces can't answer natural audit questions, the thesis is undermined. If there's a systematic mapping from questions to graph operations, the thesis is supported.

**Validation Criteria:**
- ≥8 distinct query patterns with examples
- Show graph traversal mapping for each pattern
- Counter-examples: questions CLAIR can't answer
- Thesis impact assessment
- Open questions for future work

---

## Background: Why Query Patterns Matter

### The Auditability Promise

CLAIR's value proposition includes:
- Humans can audit AI decisions by asking "why?"
- Traces preserve reasoning chains
- Answers are grounded in the DAG, not hallucinated

### The Graph Operations

A CLAIR trace is a DAG with:
- **Backward edges** (justifications): `b <- <b1, b2>`
- **Forward conditions** (invalidations): `b ?["condition"]`
- **Confidence scores**: `b .8`
- **Source tags**: `@user`, `@self`, `@file`
- **Levels**: `L0`, `L1`, `L2`

Every query must map to one or more of these operations.

---

## Query Pattern 1: "Why X?" (Backward Trace)

### Question Template

- "Why did you choose Chudnovsky algorithm?"
- "Why did you add a return statement?"
- "Why are you using JWT for authentication?"

### Graph Operation: Parent Walk

**Operation:** Traverse justification edges backward from target belief.

**Algorithm:**
```
function why(belief_id):
    path = []
    current = get_belief(belief_id)
    while current.has_justifications():
        path.append(current)
        current = current.justifications[0]  # follow first parent
    return path
```

### Example 1: Pi Calculation (from `examples/pi-calculation.md`)

**Query:** "Why Chudnovsky algorithm?"

**Trace segment:**
```clair
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
b8 .8 L0 @self <b7 ?["n<15"] "use Chudnovsky algorithm"
```

**Traversal:** `b8 <- b7 <- b3 <- b2 <- b1`

**Answer:**
> "I used Chudnovsky because the user requested PI to N decimal places, where N can be arbitrarily large. This requires arbitrary precision arithmetic. Chudnovsky algorithm was selected because it converges at ~14 digits per iteration, making it efficient for high precision (confidence .85 vs Leibniz .3 and Machin .5)."

**Debug view:**
```
[debug: b8 .8 <b7 | alternatives: none]
[debug: b7 .85 <b3 | alternatives: b5 .3 (Leibniz), b6 .5 (Machin)]
```

### Example 2: Debugging (from `exploration/ir/A1-problem-types.md`)

**Query:** "Why add a return statement?"

**Trace segment:**
```clair
b5 .9 L0 @self <b2 "function ends without explicit return statement"
b6 .95 L0 @self <b5 "Python functions return None by default if no return specified"
b7 .95 L0 @self <b6 "root cause: missing 'return result' at end of function"
b8 .9 L0 @self <b7 "add return statement after loop"
b9 .95 L0 @self <b8 "return result (the accumulated reversed string)"
```

**Traversal:** `b9 <- b8 <- b7 <- b6 <- b5`

**Answer:**
> "I added a return statement because the function ends without an explicit return. In Python, functions return None by default if no return is specified. The root cause is missing 'return result' at end of function. Adding 'return result' returns the accumulated reversed string."

### Multi-Parent Example

**Query:** "Why is JWT used for authentication?"

**Trace segment:**
```clair
b5 .8 L0 @self <b1 "need authentication (users can only access their todos)"
b7 .85 L0 @self <b5,b7 "use JWT token for stateless authentication"
```

**Traversal:** `b7 <- (b5, b7_secondary)` — multiple parents

**Answer:**
> "JWT is used because the system needs authentication (users can only access their todos) and JWT provides stateless authentication which scales better than session-based approaches."

**Key insight:** When a belief has multiple parents, the answer synthesizes all justification paths.

---

## Query Pattern 2: "Why Not Y?" (Alternative Exclusion)

### Question Template

- "Why not Leibniz series?"
- "Why not use bubble sort?"
- "Why not session-based authentication?"

### Graph Operation: Sibling Comparison

**Operation:** Find beliefs with same justifications, compare confidence scores.

**Algorithm:**
```
function why_not(alternative_id):
    target = get_belief(alternative_id)
    siblings = get_siblings_with_same_parents(target)
    winner = max(siblings, key=lambda b: b.confidence)
    return {
        "rejected": target,
        "winner": winner,
        "reason": winner.content,
        "confidence_gap": winner.confidence - target.confidence
    }
```

### Example 1: Algorithm Selection (from `examples/pi-calculation.md`)

**Query:** "Why not Leibniz series?"

**Trace segment:**
```clair
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b6 .5 L0 @self <b3 "Machin formula: moderate speed"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
```

**Comparison:**
```
Alternatives for b3 (need arbitrary precision):
- b5: "Leibniz series: slow, needs billions of terms" (.3)
- b6: "Machin formula: moderate speed" (.5)
- b7: "Chudnovsky: ~14 digits per iteration" (.85) ← WINNER
```

**Answer:**
> "Leibniz series was rejected because it's too slow for high precision — it needs billions of terms. Chudnovsky algorithm was chosen instead because it converges at ~14 digits per iteration (confidence .85 vs .3 for Leibniz)."

### Example 2: REST API Auth (from `exploration/ir/A1-problem-types.md`)

**Hypothetical query:** "Why not API key authentication?"

**If trace had included alternatives:**
```clair
b5 .8 L0 @self <b1 "need authentication (users can only access their todos)"
b5a .5 L0 @self <b5 "use API key authentication (simpler, less secure)"
b5b .7 L0 @self <b5 "use session-based auth (server-side state)"
b5c .9 L0 @self <b5b "use JWT (stateless, scales horizontally)"
```

**Answer:**
> "API key authentication was rejected because it's less secure for multi-user applications. JWT was chosen because it's stateless and scales horizontally better than session-based approaches (confidence .9 vs .5 for API keys)."

**Counter-example:** When trace doesn't include alternatives, "Why not Y?" can't be answered. The trace shows only the chosen path, not the rejected options.

**Implication:** For auditability, Thinkers should include rejected alternatives with low confidence (not just omit them).

---

## Query Pattern 3: "When Reconsider?" (Invalidation Check)

### Question Template

- "When should I reconsider this choice?"
- "What conditions would invalidate this decision?"
- "What edge cases might break this?"

### Graph Operation: Forward Condition Lookup

**Operation:** Retrieve invalidation conditions for target belief.

**Algorithm:**
```
function when_reconsider(belief_id):
    belief = get_belief(belief_id)
    if belief.has_invalidations():
        return belief.invalidations  // list of conditions
    else:
        return "No invalidation conditions specified"
```

### Example 1: Pi Calculation (from `examples/pi-calculation.md`)

**Query:** "When should I reconsider Chudnovsky?"

**Trace segment:**
```clair
b8 .8 L0 @self <b7 ?["n<15"] "use Chudnovsky algorithm"
```

**Retrieval:** `b8 ?["n<15"]`

**Answer:**
> "Reconsider Chudnovsky if n < 15 (for small values of N, simpler methods like Machin formula would suffice and Chudnovsky may be overkill)."

### Example 2: Sorting Algorithm (from `exploration/ir/A1-problem-types.md`)

**Trace segment:**
```clair
b10 .85 L0 @self <b2 ?["n<100"] "use insertion sort (simple and fast for small arrays)"
b12 .7 L0 @self <b2,b10,b11 "for general purpose: implement merge sort for clarity and stability"
b18 .9 L0 @self <b12 ?["n>10000"] "for large arrays: consider iterative merge sort to avoid stack overflow"
```

**Query:** "When should I reconsider merge sort?"

**Answer:**
> "Reconsider merge sort in two cases:
> 1. If n < 100, use insertion sort instead (simpler and faster for small arrays).
> 2. If n > 10000, use iterative merge sort instead of recursive to avoid stack overflow."

### Example 3: Multi-file Refactoring

**Hypothetical trace with invalidation:**
```clair
b25 .9 L0 @self <b6 ?["UserService tests fail"] "revert: Validator extraction broke behavior"
```

**Answer:**
> "Reconsider the Validator extraction if UserService tests fail — this indicates the refactoring changed behavior (regression)."

---

## Query Pattern 4: "What Assumptions?" (Premise Extraction)

### Question Template

- "What assumptions does this decision rely on?"
- "What's the basis for this belief?"
- "What would invalidate the entire chain?"

### Graph Operation: Leaf Node Extraction

**Operation:** Find all leaf nodes (beliefs with no justifications) in the justification subtree.

**Algorithm:**
```
function what_assumptions(belief_id):
    subtree = get_justification_subtree(belief_id)
    leaves = [b for b in subtree if not b.has_justifications()]
    return leaves
```

### Example 1: REST API Design

**Query:** "What assumptions does JWT authentication rely on?"

**Trace segment:**
```clair
b1 1.0 L0 @user "design a REST API for a todo list application"
b2 .95 L0 @self <b1 "need CRUD operations for todos"
b4 .85 L0 @self <b2 "users own their todos (multi-tenancy required)"
b5 .8 L0 @self <b1 "need authentication (users can only access their todos)"
b22 .9 L0 @self <b20,b21 "use JWT token for stateless authentication"
```

**Assumption extraction:**
```
b22 (JWT) <- b20,b21 <- b5,b7 <- b1 (user request), b4 (multi-tenancy)
```

**Leaves:**
- `b1`: User wants a REST API for todo list
- `b4`: Users own their todos (multi-tenancy required)

**Answer:**
> "JWT authentication relies on these assumptions:
> 1. The user wants a REST API for a todo list application (b1)
> 2. Users own their todos, requiring multi-tenancy (b4)
>
> If these assumptions change (e.g., no multi-tenancy needed), JWT might be overkill."

### Example 2: Mathematical Proof

**Query:** "What assumptions does the proof of √2 irrationality rely on?"

**Trace segment:**
```clair
b1 1.0 L0 @user "prove that sqrt(2) is irrational"
b2 1.0 L0 @self "rational number: can be expressed as p/q where p,q are integers with no common factors"
b3 1.0 L0 @self "irrational number: cannot be expressed as p/q (negation of rational)"
b8 .95 L0 @self <b6 "assume sqrt(2) = a/b where a,b are integers with no common factors"
```

**Leaves:**
- `b2`: Definition of rational numbers
- `b3`: Definition of irrational numbers

**Answer:**
> "The proof relies on these foundational assumptions:
> 1. Rational numbers can be expressed as p/q where p,q have no common factors
> 2. Irrational numbers are the negation of rational
>
> If these definitions change, the proof would not hold."

---

## Query Pattern 5: "What Alternatives?" (Sibling Enumeration)

### Question Template

- "What alternatives were considered?"
- "What other options did you evaluate?"
- "What was the decision space?"

### Graph Operation: Justification Grouping

**Operation:** Find all beliefs sharing the same justification parent(s).

**Algorithm:**
```
function what_alternatives(belief_id):
    target = get_belief(belief_id)
    parents = target.justifications
    siblings = get_all_beliefs_justified_by(parents)
    return siblings  // includes target
```

### Example 1: Pi Calculation

**Query:** "What algorithms were considered for PI calculation?"

**Trace segment:**
```clair
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b6 .5 L0 @self <b3 "Machin formula: moderate speed"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
```

**Alternatives (all justified by b3):**
1. Leibniz series (.3) - too slow
2. Machin formula (.5) - moderate speed
3. Chudnovsky (.85) - ~14 digits per iteration ← chosen

**Answer:**
> "I considered 3 algorithms:
> 1. **Leibniz series** (confidence .3): Rejected because it's too slow — needs billions of terms for high precision.
> 2. **Machin formula** (confidence .5): Moderate speed, but not as fast as Chudnovsky.
> 3. **Chudnovsky** (confidence .85): Chosen because it converges at ~14 digits per iteration."

### Example 2: Sorting Algorithm

**Trace segment:**
```clair
b5 .3 L0 @self <b2 "bubble sort: O(n²) but simple"
b6 .5 L0 @self <b2 "insertion sort: O(n²), good for small n"
b7 .6 L0 @self <b2 "merge sort: O(n log n), stable, needs extra space"
b8 .7 L0 @self <b2 "quick sort: O(n log n) average, O(n²) worst, unstable"
b9 .8 L0 @self <b2 "heap sort: O(n log n), unstable, in-place"
```

**Alternatives:**
- Bubble sort (.3) - too slow
- Insertion sort (.5) - good for small n
- Merge sort (.6) - stable but needs space
- Quick sort (.7) - average good but worst case bad
- Heap sort (.8) - in-place but unstable

**Answer:**
> "I considered 5 sorting algorithms with these trade-offs:
> 1. **Bubble sort** (.3): Simple but O(n²) — too slow
> 2. **Insertion sort** (.5): Good for small arrays only
> 3. **Merge sort** (.6): Stable, O(n log n), but needs extra space
> 4. **Quick sort** (.7): O(n log n) average but O(n²) worst case
> 5. **Heap sort** (.8): O(n log n), in-place, but unstable
>
> For general purpose, I'd use merge sort for stability, or heap sort for space efficiency."

---

## Query Pattern 6: "How Confident?" (Confidence Inspection)

### Question Template

- "How confident are you in this choice?"
- "What's the reliability of this decision?"
- "Is this a strong or weak preference?"

### Graph Operation: Confidence Retrieval

**Operation:** Retrieve confidence score and compare to thresholds.

**Algorithm:**
```
function how_confident(belief_id):
    belief = get_belief(belief_id)
    c = belief.confidence
    if c >= 0.9:
        level = "very confident"
    elif c >= 0.7:
        level = "confident"
    elif c >= 0.5:
        level = "moderately confident"
    else:
        level = "low confidence"
    return {confidence: c, level: level}
```

### Example 1: Debugging Diagnosis

**Query:** "How confident are you that the missing return is the bug?"

**Trace segment:**
```clair
b7 .95 L0 @self <b6 "root cause: missing 'return result' at end of function"
b13 .1 L0 @self <b1 "result variable is None"
b14 .1 L0 @self <b1 "string concatenation fails"
b15 .1 L0 @self <b1 "loop doesn't execute"
```

**Confidence analysis:**
- `b7` (missing return): .95 = "very confident"
- `b13-b15` (alternatives): .1 = "very low confidence"

**Answer:**
> "I am very confident (.95) that the missing return statement is the root cause. Alternative explanations (result variable is None, string concatenation fails, loop doesn't execute) all have very low confidence (.1), indicating they were considered and eliminated."

### Example 2: Algorithm Choice with Uncertainty

**Hypothetical trace:**
```clair
b5 .6 L0 @self <b2 "use merge sort: O(n log n) but complex"
b6 .55 L0 @self <b2 "use quick sort: O(n log n) average but O(n²) worst"
```

**Query:** "How confident are you in merge sort?"

**Answer:**
> "I am moderately confident (.6) in merge sort. Quick sort is close behind at .55 confidence. The decision is not strong — either would be acceptable depending on priorities (stability vs space)."

**Implication:** Confidence scores communicate uncertainty, which is important for human oversight.

---

## Query Pattern 7: "What Was Ruled Out?" (Rejection Analysis)

### Question Template

- "What did you consider and reject?"
- "What options didn't make the cut?"
- "What paths did you not take?"

### Graph Operation: Low-Confidence Sibling Filter

**Operation:** Find siblings with confidence < 0.5 (or below some threshold).

**Algorithm:**
```
function what_was_ruled_out(belief_id, threshold=0.5):
    target = get_belief(belief_id)
    siblings = get_siblings_with_same_parents(target)
    rejected = [s for s in siblings if s.confidence < threshold]
    return rejected
```

### Example 1: Algorithm Selection

**Query:** "What was ruled out for PI calculation?"

**Trace segment:**
```clair
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
```

**Rejected:**
- `b5` (Leibniz): .3 < 0.5 threshold

**Answer:**
> "I ruled out Leibniz series (confidence .3) because it's too slow for high precision — it needs billions of terms. Chudnovsky won at .85 confidence."

### Example 2: Creative Task (from A1)

**Query:** "What poetic forms were ruled out?"

**Trace segment:**
```clair
b6 .7 L0 @self <b4 "haiku: 5-7-5 syllables, very concise"
b7 .6 L0 @self <b4 "sonnet: 14 lines, rhyme scheme, formal structure"
b8 .8 L0 @self <b4 "free verse: no constraints, more expressive"
b9 .75 L0 @self <b6,b7,b8 "use free verse for flexibility"
```

**Answer:**
> "I ruled out haiku (.7) and sonnet (.6) in favor of free verse (.8). Haiku was too constrained (5-7-5 syllables), and sonnet's formal structure (rhyme scheme, 14 lines) felt too rigid for this topic."

---

## Query Pattern 8: "What Evidence Supports X?" (Evidence Chain)

### Question Template

- "What evidence supports this conclusion?"
- "What's the justification chain?"
- "How did you arrive at this?"

### Graph Operation: Justification Tree Expansion

**Operation:** Recursively expand all justification edges, showing the full tree.

**Algorithm:**
```
function what_evidence(belief_id):
    tree = {}
    def expand(belief):
        if belief.has_justifications():
            tree[belief.id] = [expand(j) for j in belief.justifications]
        else:
            tree[belief.id] = "axiom"  // leaf node
    expand(get_belief(belief_id))
    return tree
```

### Example 1: REST API Authorization

**Query:** "What evidence supports the authorization requirement?"

**Trace segment:**
```clair
b4 .85 L0 @self <b2 "users own their todos (multi-tenancy required)"
b14 .95 L0 @self <b13,b4 "must verify user owns this todo (authorization)"
b17 .9 L0 @self <b14,b15 "authorization required: user must own todo"
```

**Evidence tree:**
```
b17 (authorization required)
├── b14 (verify ownership)
│   ├── b13 (get specific todo)
│   └── b4 (users own todos)
│       └── b2 (CRUD operations)
│           └── b1 (user request)
└── b15 (update todo)
    └── b6 (primary resource: /todos)
```

**Answer:**
> "The authorization requirement is supported by this evidence chain:
> 1. User requested a REST API for todo list (b1)
> 2. This requires CRUD operations (b2)
> 3. Users own their todos → multi-tenancy required (b4)
> 4. Therefore, endpoints like GET/PUT /todos/{id} must verify ownership (b14, b17)
>
> The authorization requirement is NOT arbitrary — it follows directly from the multi-tenancy requirement."

### Example 2: Mathematical Proof

**Query:** "What evidence supports that √2 is irrational?"

**Trace segment:**
```clair
b21 .95 L0 @self <b20 "assumption (sqrt(2) is rational) leads to contradiction"
b22 .95 L0 @self <b21 "therefore: sqrt(2) is irrational"
```

**Evidence tree:**
```
b22 (therefore irrational)
└── b21 (contradiction from assumption)
    └── b20 (both a and b are even)
        ├── b12 (a is even)
        │   └── b11 (a² is even)
        │       └── b10 (a² = 2b²)
        │           └── b9 (2 = a²/b²)
        │               └── b8 (assume sqrt(2) = a/b)
        │                   └── b6 (assume sqrt(2) is rational)
        └── b18 (b is even)
            └── b17 (b² is even)
                └── b16 (2k² = b²)
                    └── b15 (4k² = 2b²)
                        └── b14 (a² = 4k²)
                            └── b13 (let a = 2k)
```

**Answer:**
> "The proof that √2 is irrational is supported by a contradiction chain:
> 1. Assume √2 is rational, so √2 = a/b where a,b have no common factors
> 2. Then 2 = a²/b², so a² = 2b²
> 3. This means a² is even, so a is even
> 4. Let a = 2k, then a² = 4k²
> 5. Substituting: 4k² = 2b², so 2k² = b²
> 6. This means b² is even, so b is even
> 7. But if both a and b are even, they share a factor of 2 — contradiction!
>
> Therefore the assumption (√2 is rational) must be false."

---

## Query Pattern 9: "Where Did This Come From?" (Provenance Check)

### Question Template

- "Where did this information come from?"
- "Is this from the user or inferred?"
- "What file did this come from?"

### Graph Operation: Source Tag Inspection

**Operation:** Retrieve source tags for belief and its justification chain.

**Algorithm:**
```
function where_from(belief_id):
    belief = get_belief(belief_id)
    sources = collect_sources_from_justifications(belief)
    return {
        direct: belief.source,
        chain: sources
    }
```

### Example 1: File Reading

**Query:** "Where did the config information come from?"

**Trace segment:**
```clair
b1 1.0 L0 @user "open config.yaml and summarize"
b2 1.0 L0 @file:config.yaml "database:\n  host: localhost..."
b3 .95 L0 @self <b1,b2 "3 sections: database, cache, logging"
```

**Sources:**
- `b1`: @user
- `b2`: @file:config.yaml
- `b3`: @self (derived from b1, b2)

**Answer:**
> "The config information comes from:
> - User request: 'open config.yaml and summarize' (b1, @user)
> - File content: config.yaml contains database, cache, logging sections (b2, @file:config.yaml)
> - Derived: The summary (b3) is inferred from both user request and file content."

### Example 2: Context-Based Belief

**Trace segment:**
```clair
b1 1.0 L0 @user "fix this bug"
b2 1.0 L0 @ctx "def reverse_string(s):\n    result = ''\n    # missing return"
```

**Sources:**
- `b1`: @user (user input)
- `b2`: @ctx (conversation context, code snippet)

**Answer:**
> "The bug diagnosis is based on:
> - User request: 'fix this bug' (b1, @user)
> - Context: The provided code snippet shows a function without return statement (b2, @ctx)"

---

## Query Pattern 10: "What's Missing?" (Gap Analysis)

### Question Template

- "What didn't you consider?"
- "What's missing from this trace?"
- "What questions remain unanswered?"

### Graph Operation: Unconnected Component Detection

**Operation:** Find beliefs not connected to main reasoning chain.

**Algorithm:**
```
function whats_missing(trace):
    main_chain = get_main_output_chain(trace)
    all_beliefs = trace.all_beliefs()
    unconnected = [b for b in all_beliefs if b not in main_chain]
    return unconnected
```

### Example 1: Missing Alternative Exploration

**Query:** "What alternatives weren't considered?"

**Trace (REST API):**
```clair
b5 .8 L0 @self <b1 "need authentication"
b22 .9 L0 @self <b20,b21 "use JWT token"
```

**Gap analysis:** No alternatives explored for authentication (no API keys, no sessions, no OAuth).

**Answer:**
> "The trace directly selects JWT without exploring alternatives. Not considered:
> - API key authentication
> - Session-based authentication
> - OAuth/OIDC
>
> This makes it hard to evaluate whether JWT is truly the best choice."

### Example 2: Missing Edge Case Handling

**Query:** "What edge cases weren't handled?"

**Trace (sorting):**
```clair
b16 .9 L0 @self <b1 "function signature: sort(arr: int[]) → int[]"
b17 .85 L0 @self <b16 "modify in-place (no return) or return new array (functional style)"
```

**Gap analysis:** No beliefs about:
- Empty arrays
- Single-element arrays
- Already sorted arrays
- Arrays with duplicate elements

**Answer:**
> "The trace doesn't address edge cases:
> - What if arr is empty?
> - What if arr has one element?
> - What if arr is already sorted?
> - What about duplicate elements?
>
> These should be explicit beliefs (or invalidation conditions) for robust code."

---

## Counter-Examples: Questions CLAIR Can't Answer

### Counter-Example 1: Temporal Questions

**Question:** "What did you think before you realized the bug?"

**Problem:** CLAIR traces are acyclic — no temporal ordering. The trace shows final beliefs, not the process of discovery.

**Workaround:** Add beliefs about the discovery process:
```clair
b5 .8 L0 @self ?["before seeing code"] "initial hypothesis: variable is None"
b7 .95 L0 @self <b6 ?["after analyzing code"] "actual cause: missing return"
```

But this is **artificial temporal metadata**, not natural trace structure.

### Counter-Example 2: Counterfactual Questions

**Question:** "What would happen if you chose bubble sort instead?"

**Problem:** The trace shows the chosen path, not the unexecuted alternative. CLAIR doesn't simulate "what if" scenarios.

**Workaround:** Compare beliefs:
```clair
b5 .3 L0 @self <b2 "bubble sort: O(n²) but simple"
b7 .85 L0 @self <b2 "merge sort: O(n log n), stable"
```

Answer: "Bubble sort would be slower (O(n²) vs O(n log n)) but simpler."

This works for **performance trade-offs**, but not for complex behavioral differences.

### Counter-Example 3: Intent Questions

**Question:** "Why did you write this specific poem line?"

**Problem:** Creative content is often opaque. The trace can say "stanza 1 is about autumn" but can't explain *why* that specific metaphor was chosen.

**Limitation:** CLAIR captures reasoning about structure, but not creative intent at the content level.

### Counter-Example 4: Unrecorded Alternatives

**Question:** "Why not GraphQL instead of REST?"

**Problem:** If the Thinker never considered GraphQL, there's no belief about it.

**Limitation:** CLAIR can't answer "Why not X?" if X was never in the decision space.

**Workaround:** Thinkers should explicitly consider and reject major alternatives:
```clair
b5a .3 L0 @self <b1 "GraphQL: flexible but overkill for simple todo API"
b5b .9 L0 @self <b1 "REST: simple, well-understood, sufficient"
```

### Counter-Example 5: Emotional/Subjective Questions

**Question:** "Do you like this approach?"

**Problem:** Confidence scores ≠ preferences. .9 confidence doesn't mean "I like it."

**Limitation:** CLAIR captures epistemic confidence (belief strength), not aesthetic preference.

---

## Cross-Query Analysis

### Query Mapping Summary

| Query Pattern | Graph Operation | Complexity | Answer Quality |
|---------------|-----------------|------------|----------------|
| "Why X?" | Parent walk (backward trace) | O(depth) | High (direct from trace) |
| "Why not Y?" | Sibling comparison | O(siblings) | Medium (requires alternatives) |
| "When reconsider?" | Invalidation lookup | O(1) | High (if conditions exist) |
| "What assumptions?" | Leaf extraction | O(subtree) | High (shows foundations) |
| "What alternatives?" | Justification grouping | O(siblings) | Medium (if alternatives recorded) |
| "How confident?" | Confidence retrieval | O(1) | High (explicit score) |
| "What ruled out?" | Low-confidence filter | O(siblings) | Medium (if rejections recorded) |
| "What evidence?" | Tree expansion | O(subtree) | High (full chain) |
| "Where from?" | Source inspection | O(1) | High (explicit tag) |
| "What's missing?" | Gap detection | O(trace) | Low (speculative) |

### Query Composition

**Complex queries can compose simple operations:**

**Question:** "Why JWT, how confident are you, and when should I reconsider?"

**Composition:**
1. "Why JWT?" → Parent walk: `b22 <- b5,b7 <- ...`
2. "How confident?" → Confidence: `.9`
3. "When reconsider?" → Invalidation: `b22 ?["stateless not needed"]`

**Answer:**
> "JWT was chosen because the system needs stateless authentication for multi-user todo API. I'm very confident (.9) in this choice. Reconsider if stateless scaling is not needed (e.g., single-user deployment)."

---

## Usability Assessment

### Readability at Different Trace Sizes

Based on the traces explored (5-32 beliefs):

| Trace Size | Readability | Effective Query Patterns |
|------------|-------------|-------------------------|
| **5-10 beliefs** (simple) | High | All 10 patterns work well |
| **10-20 beliefs** (moderate) | Medium-High | Most patterns work; "what's missing" harder |
| **20-30 beliefs** (complex) | Medium | "Why" and "what evidence" work well; global patterns harder |
| **30+ beliefs** (very complex) | Low-Medium | Need summarization; tree expansion becomes unwieldy |

### What Makes Queries Easy vs Hard

**Easy queries:**
- Local (single belief or small subtree)
- Explicit (confidence, source, invalidation)
- Backward (trace to root)

**Hard queries:**
- Global (entire trace analysis)
- Temporal (before/after)
- Speculative (what's missing, what if)

---

## Comparison with Alternatives

### CLAIR vs Chain-of-Thought

| Query Type | Chain-of-Thought | CLAIR |
|------------|------------------|-------|
| "Why X?" | Search text for keywords | Follow justification edges |
| "Why not Y?" | May not be mentioned | Compare sibling confidence |
| "When reconsider?" | Usually not mentioned | Explicit invalidation |
| "How confident?" | Qualitative ("I think") | Quantitative (.9) |
| "What alternatives?" | Buried in text | Explicit siblings |
| "What evidence?" | Linear narrative | Tree structure |

**CLAIR advantage:** Structure makes queries systematic, not search-based.

### CLAIR vs Decision Trees

| Query Type | Decision Tree | CLAIR |
|------------|---------------|-------|
| "Why X?" | Follow single path | Follow DAG (multiple parents) |
| "Why not Y?" | Not represented | Sibling comparison |
| "How confident?" | Not represented | Explicit confidence |
| "What evidence?" | Single path | Justification tree |

**CLAIR advantage:** DAG captures multiple justification paths; decision trees are single-path.

---

## Thesis Impact Assessment

### Supporting Evidence

1. **Systematic query mapping exists:** All 10 query patterns map to graph operations
2. **Natural questions work:** "Why", "why not", "when reconsider" all have clear answers
3. **Confidence is queryable:** Confidence scores enable "how confident" queries
4. **Justification chains are explorable:** Parent walks show reasoning trace

### Refining Evidence

1. **Not all questions can be answered:** Temporal, counterfactual, intent questions have limitations
2. **Quality depends on Thinker:** "Why not Y?" only works if alternatives are recorded
3. **Large traces are hard:** 30+ belief traces need summarization for usability
4. **Gap analysis is speculative:** "What's missing?" requires assumptions

### Undermining Evidence

1. **Temporal reasoning missing:** "What did you think before?" can't be answered naturally
2. **Unrecorded alternatives invisible:** "Why not X?" fails if X was never considered
3. **Creative intent opaque:** "Why this metaphor?" may not be explainable

### Thesis Assessment

**CLAIR supports auditability with operational constraints:**

1. **Works well for:**
   - "Why X?" (backward trace)
   - "Why not Y?" (if alternatives recorded)
   - "When reconsider?" (invalidation conditions)
   - "How confident?" (confidence scores)
   - "What assumptions?" (leaf extraction)

2. **Struggles with:**
   - Temporal questions (before/after)
   - Counterfactuals (what if)
   - Creative intent (why this specific content)
   - Unrecorded alternatives (why not X if X never considered)

3. **Needs:**
   - Thinker training on recording alternatives
   - Temporal metadata extensions for discovery processes
   - Trace summarization for large traces
   - Visualization tools for complex justification trees

**The thesis stands:** CLAIR traces enable effective audit queries, but the quality of answers depends on trace completeness and Thinker discipline.

---

## Recommendations for Spec

### 1. Add Query Examples to Spec

Add to `formal/clair-spec.md`:

```markdown
## Query Examples

Humans can query CLAIR traces for auditability:

- "Why X?" → Trace justification edges backward
- "Why not Y?" → Compare sibling confidence scores
- "When reconsider?" → Check invalidation conditions
- "How confident?" → Retrieve confidence score
- "What assumptions?" → Find leaf nodes in justification subtree
```

### 2. Recommend Alternative Recording

Add guideline:

```
Thinkers should record rejected alternatives with low confidence:
- Enables "Why not Y?" queries
- Shows decision space was explored
- Prevents "unrecorded alternative" counter-example
```

### 3. Add Invalidation Best Practices

Add guideline:

```
Beliefs about implementation choices should include invalidation conditions:
- When would this choice be wrong?
- What edge cases might break this?
- What conditions would trigger reconsideration?
```

---

## Open Questions

### Q1: How Should Large Traces Be Summarized?

**Problem:** 30+ belief traces are hard to query directly.

**Question:** Should CLAIR have a "summary" belief that aggregates key decisions? Or should this be done at query time?

### Q2: Should Temporal Metadata Be Added?

**Problem:** CLAIR can't naturally answer "what did you think before you realized X?"

**Question:** Should we add @step or @version annotations to enable temporal queries? Or is this outside CLAIR's scope?

### Q3: How to Handle "What If" Queries?

**Problem:** Counterfactuals require simulating unexecuted paths.

**Question:** Should CLAIR support "scenario" tags? E.g., `b5 .3 <b2 scenario="if_n_small" "bubble sort would work"`

### Q4: Can Queries Be Automated?

**Question:** Should there be a query language for CLAIR (e.g., `WHY b8`, `WHY_NOT b5`)? Or should queries remain natural language?

### Q5: Visualization Needs

**Question:** What visualization would help? Graph diagrams? Indented text? Interactive explorers?

---

## Future Work

1. **Query language design:** Formal syntax for CLAIR queries
2. **Visualization tools:** Interactive DAG explorers
3. **Empirical testing:** Can real users successfully audit traces?
4. **Summarization algorithms:** Automatic extraction of key decisions
5. **Temporal extensions:** @step/@version for discovery processes

---

## Conclusion

**Key findings:**
- ✅ **10 query patterns** mapped to graph operations
- ✅ **Natural questions work:** "Why", "why not", "when reconsider", "how confident"
- ✅ **Systematic mapping exists:** Each query → specific graph traversal
- ⚠️ **Quality depends on Thinker:** Alternatives must be recorded for "why not" queries
- ⚠️ **Temporal queries limited:** No natural "before/after" support
- ⚠️ **Large traces need summarization:** 30+ beliefs are hard to navigate

**Thesis connection:** **Supports the thesis with operational constraints.** CLAIR traces are queryable and support auditability, but the quality of answers depends on:
1. Thinker discipline (recording alternatives)
2. Trace completeness (invalidation conditions)
3. Trace size (summarization for large traces)

**Counter-examples identified:**
1. Temporal questions (discovery process)
2. Counterfactuals (what if scenarios)
3. Unrecorded alternatives (why not invisible options)
4. Creative intent (why specific content choices)
5. Subjective preferences (confidence ≠ aesthetic)

**Open questions:**
1. How to summarize large traces?
2. Should temporal metadata be added?
3. How to handle "what if" queries?
4. Can queries be automated with a formal language?
5. What visualization would help?

**The path forward:** Develop query tools and visualization to make auditability practical for real users. The theory is sound — implementation is needed.
