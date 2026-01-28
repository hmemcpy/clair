# Thread 2.11: Aggregation of Independent Evidence

> **Status**: Active exploration (Session 19)
> **Task**: 2.11 How do independent lines of evidence combine?
> **Question**: When multiple independent justifications support the same belief, how should their confidences combine to yield a final confidence?
> **Priority**: HIGH — Central gap in CLAIR's confidence propagation

---

## 1. The Problem

Thread 2 established that CLAIR needs an **aggregate** constructor for beliefs supported by multiple independent lines of evidence:

```clair
let conclusion = belief("climate change is real", 0.99, justified_by: [
  line1: justify(observation: temperature_records, confidence: 0.85),
  line2: justify(observation: ice_core_data, confidence: 0.80),
  line3: justify(observation: sea_level_rise, confidence: 0.75),
  line4: justify(theory: greenhouse_physics, confidence: 0.90)
])
```

These aren't premises combined by a single rule. They are **independent lines of evidence** that each, separately, support the conclusion. The question is: how do their confidences combine?

Thread 8 established three confidence operations:
- **Multiplication (×)**: For sequential/conjunctive derivation (e.g., modus ponens)
- **Minimum (min)**: For conservative combination
- **Probabilistic OR (⊕)**: For... what exactly?

The ⊕ operation was defined as:
```
a ⊕ b = a + b - a×b
```

But we never rigorously justified *why* this is the right operation for aggregation. This exploration digs into that question.

---

## 2. Clarifying the Question

### 2.1 What Is "Independent Evidence"?

Two pieces of evidence e₁ and e₂ are **independent** (in the epistemic sense) if:
- Learning e₁ doesn't change your estimate of how likely e₂ is
- Learning e₁ doesn't change how much e₂ supports the conclusion
- e₁ and e₂ don't share hidden common causes that explain both

**Example of independence**:
- Temperature records from ground stations (e₁)
- Satellite temperature measurements (e₂)

These use different measurement methods, different instruments, different error sources. If they agree, that's convergent confirmation.

**Example of non-independence (correlated evidence)**:
- Temperature reading from station A in city X
- Temperature reading from station B in city X

Both might share systematic bias from the urban heat island effect. They're not fully independent.

### 2.2 What Is Aggregation?

**Aggregation** is combining multiple independent supports for the same conclusion. It differs from:

1. **Conjunction (×)**: "Both premises are needed for the inference"
   - Example: "Socrates is a man AND all men are mortal → Socrates is mortal"
   - If either premise fails, the inference fails

2. **Disjunction (⊕)**: "At least one suffices"
   - Example: "Either route A or route B will get you there"
   - If either works, the conclusion holds

3. **Aggregation**: "Multiple independent supports, each making the conclusion more likely"
   - Example: "Three witnesses independently saw the suspect"
   - More witnesses = higher confidence (up to a limit)

### 2.3 Key Desiderata for Aggregation

What properties should the aggregation function satisfy?

**D1. Boundedness**: aggregate(c₁, ..., cₙ) ∈ [0,1]

**D2. Identity**: aggregate(c) = c (single evidence keeps its confidence)

**D3. Monotonicity**: Adding evidence should never decrease confidence
   - aggregate(c₁, c₂) ≥ max(c₁, c₂)

**D4. Commutativity**: Order doesn't matter
   - aggregate(c₁, c₂) = aggregate(c₂, c₁)

**D5. Associativity**: Grouping doesn't matter
   - aggregate(aggregate(c₁, c₂), c₃) = aggregate(c₁, aggregate(c₂, c₃))

**D6. Convergence to certainty**: As independent confirming evidence accumulates, confidence should approach (but perhaps never reach) 1
   - lim_{n→∞} aggregate(c, c, ..., c) = 1 for c > 0

**D7. Diminishing returns**: Each additional piece of evidence contributes less
   - The 10th witness adds less than the 1st witness

---

## 3. Prior Art Survey

### 3.1 Probability Theory: Independence and Bayes

In probability theory, if evidence e₁ and e₂ are conditionally independent given hypothesis H:

```
P(H | e₁, e₂) ∝ P(H) × P(e₁|H) × P(e₂|H) / [P(e₁) × P(e₂)]
```

The posterior odds approach:
```
O(H | e₁, e₂) = O(H) × LR(e₁) × LR(e₂)
```

where LR(e) = P(e|H)/P(e|¬H) is the likelihood ratio.

**Key insight**: Independent evidence multiplies *likelihood ratios*, not confidences directly.

But CLAIR's confidence isn't a probability in the strict sense. It's an epistemic commitment measure that doesn't normalize (P and ¬P can both have low confidence).

### 3.2 Subjective Logic: Cumulative Fusion

Audun Jøsang's Subjective Logic provides a principled treatment of evidence combination.

**Opinion representation**: ω = (b, d, u, a)
- b = belief mass (evidence for)
- d = disbelief mass (evidence against)
- u = uncertainty mass (no evidence either way)
- a = base rate (prior)
- Constraint: b + d + u = 1

**Cumulative fusion** for independent sources:
```
ω_A⊕B = (b_A⊕B, d_A⊕B, u_A⊕B, a_A⊕B)

where:
b_A⊕B = (b_A × u_B + b_B × u_A) / κ
d_A⊕B = (d_A × u_B + d_B × u_A) / κ
u_A⊕B = (u_A × u_B) / κ

κ = u_A + u_B - u_A × u_B  (normalization)
```

**Key properties**:
- Uncertainty decreases: u_A⊕B < min(u_A, u_B)
- Belief increases when both agree
- Handles conflicting evidence (when one believes, other disbelieves)

**If we map CLAIR confidence c to Subjective Logic opinion (c, 0, 1-c, 0.5)**:
- b = c (belief mass)
- d = 0 (no explicit disbelief)
- u = 1-c (uncertainty)
- a = 0.5 (neutral prior)

Then the cumulative fusion formula becomes:
```
b_combined = (c₁ × (1-c₂) + c₂ × (1-c₁)) / κ
           = (c₁ - c₁c₂ + c₂ - c₁c₂) / κ
           = (c₁ + c₂ - 2c₁c₂) / κ

where κ = (1-c₁) + (1-c₂) - (1-c₁)(1-c₂)
        = 2 - c₁ - c₂ - 1 + c₁ + c₂ - c₁c₂
        = 1 - c₁c₂
```

So:
```
b_combined = (c₁ + c₂ - 2c₁c₂) / (1 - c₁c₂)
```

Hmm, this is NOT the same as c₁ ⊕ c₂ = c₁ + c₂ - c₁c₂.

Let me verify with numbers:
- c₁ = 0.5, c₂ = 0.5
- CLAIR ⊕: 0.5 + 0.5 - 0.25 = 0.75
- SL fusion: (0.5 + 0.5 - 0.5) / (1 - 0.25) = 0.5 / 0.75 ≈ 0.667

They differ! This is important—our current ⊕ is NOT Subjective Logic's cumulative fusion.

### 3.3 Dempster-Shafer Theory

Dempster-Shafer theory uses **belief functions** rather than probabilities.

**Basic probability assignment** m: 2^Ω → [0,1] with Σ m(A) = 1

**Dempster's rule of combination** for independent sources:
```
m₁₂(A) = [Σ_{B∩C=A} m₁(B) × m₂(C)] / (1 - K)

where K = Σ_{B∩C=∅} m₁(B) × m₂(C)  (conflict measure)
```

The normalization factor (1-K) handles conflicting evidence by scaling out the conflict.

**Problem with D-S**: Zadeh's paradox shows counterintuitive results with high conflict:
- Source 1: 99% certain it's A
- Source 2: 99% certain it's B (where A and B are disjoint)
- D-S combination: certainty in A∩B = ∅, so all mass goes to whatever tiny overlap exists

For CLAIR, where we're combining confidence in the *same* proposition (not different hypotheses), this might be less problematic.

### 3.4 Independence vs. Reliability

A key distinction from the judgment aggregation literature:

**Condorcet's Jury Theorem**: If each juror is independently more likely than not to be correct, then majority voting becomes increasingly reliable as jury size grows.

Key assumption: **Independence**. If jurors copy each other, the theorem breaks.

**For CLAIR**: If multiple "evidence sources" actually derive from the same underlying source (e.g., multiple papers citing the same study), they shouldn't be treated as independent.

### 3.5 Fuzzy Logic Aggregation

In fuzzy logic, there are many aggregation operators:

**T-conorms** (for "or"):
- **Maximum**: max(a, b) — not suitable (adding evidence doesn't help)
- **Algebraic sum**: a + b - ab — this is our ⊕!
- **Bounded sum**: min(1, a + b) — can reach 1 quickly
- **Drastic sum**: if min(a,b)=0 then max(a,b) else 1

**Compensatory operators** (between t-norm and t-conorm):
- **Generalized mean**: ((aᵖ + bᵖ)/2)^(1/p)
- **OWA operators**: Ordered Weighted Averaging

The algebraic sum t-conorm (our ⊕) is indeed a standard choice for combining independent fuzzy memberships.

---

## 4. Analysis: What Is ⊕ Really?

### 4.1 The Probabilistic Interpretation

The formula a ⊕ b = a + b - ab has a clean probabilistic interpretation:

**Theorem**: If A and B are independent events with P(A) = a and P(B) = b, then:
```
P(A ∨ B) = P(A) + P(B) - P(A ∧ B) = a + b - ab
```

So ⊕ is **probability of disjunction for independent events**.

But wait—in aggregation, we're not asking "does at least one line of evidence support the conclusion?" We're asking "what's our confidence given all the evidence?"

### 4.2 Reinterpreting ⊕ for Aggregation

Here's a better interpretation:

**Model**: Each piece of evidence has a chance of being "successful" (actually supporting the conclusion). If confidence c represents this "success probability," then:
- Evidence 1 has probability c₁ of successfully supporting the conclusion
- Evidence 2 has probability c₂ of successfully supporting the conclusion
- If they're independent, at least one succeeds with probability c₁ ⊕ c₂

**But this interpretation has a problem**: It treats high confidence as "evidence more likely to be good," which conflates:
1. Strength of evidence (how much it supports)
2. Quality of evidence (how reliable it is)

These are different concepts that probably shouldn't be conflated.

### 4.3 The "Survival of Doubt" Interpretation

An alternative interpretation:

**Model**: Confidence c represents certainty. Uncertainty is (1-c).

When combining independent evidence:
- Each piece of evidence has independent uncertainty (1-c₁) and (1-c₂)
- For the conclusion to remain uncertain, ALL evidence must fail to convince
- Probability all evidence fails: (1-c₁) × (1-c₂) = 1 - c₁ - c₂ + c₁c₂
- Probability at least one convinces: 1 - (1-c₁)(1-c₂) = c₁ + c₂ - c₁c₂ = c₁ ⊕ c₂

**This interpretation supports ⊕ for aggregation!**

The formula says: "Combined confidence = probability that at least one line of evidence succeeds in establishing the conclusion."

### 4.4 Checking Desiderata

Does ⊕ satisfy our desiderata?

**D1. Boundedness**: ✓ (proven in Thread 8)
- 0 ≤ a ⊕ b ≤ 1 for a, b ∈ [0,1]

**D2. Identity**: ✓
- a ⊕ 0 = a + 0 - 0 = a

**D3. Monotonicity**: ✓
- a ⊕ b = a + b - ab ≥ max(a, b) since ab ≤ min(a,b) ≤ max(a,b) for a,b ∈ [0,1]
- Actually, a + b - ab ≥ a iff b - ab ≥ 0 iff b(1-a) ≥ 0. ✓
- Similarly for ≥ b.

**D4. Commutativity**: ✓
- a ⊕ b = a + b - ab = b + a - ba = b ⊕ a

**D5. Associativity**: ✓ (proven in Thread 8)
- (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)

**D6. Convergence to certainty**: ✓
- If a > 0, then a ⊕ a = 2a - a² = a(2-a) > a
- Iterating: lim_{n→∞} (⊕ⁿ a) = 1

**D7. Diminishing returns**: ✓
- The marginal gain from adding a with current aggregate c is: (c ⊕ a) - c = a - ca = a(1-c)
- This decreases as c increases (more existing evidence → less marginal gain)

All desiderata satisfied!

---

## 5. When Is ⊕ Appropriate?

### 5.1 Requirements for Using ⊕

The ⊕ operation is appropriate when:

1. **Independence**: Evidence sources are genuinely independent
2. **Same target**: All evidence supports the same proposition
3. **Positive support**: All evidence is supporting (not defeating)
4. **Uncertainty interpretation**: Confidence measures "probability of successful support"

### 5.2 When ⊕ Is NOT Appropriate

**Case 1: Correlated evidence**

If evidence sources share a common cause or influence each other, using ⊕ overcounts.

Example: Two news articles reporting the same event, both citing the same original source. These aren't independent—they should count as ~1 piece of evidence, not 2.

This is Task 2.13's domain.

**Case 2: Conflicting evidence**

If some evidence supports and some refutes, aggregation alone won't work. Need the rebut operation from Thread 2.10.

**Case 3: Quality vs. quantity confusion**

If confidence represents "how strongly this evidence supports" rather than "probability this evidence is reliable," then high-confidence weak evidence would dominate, which is wrong.

---

## 6. Comparison: ⊕ vs. Alternative Aggregation Rules

### 6.1 Maximum (Optimistic Aggregation)

```
aggregate_max(c₁, c₂) = max(c₁, c₂)
```

**Properties**:
- Idempotent: max(c, c) = c
- Doesn't increase with redundant evidence
- "Only the best evidence matters"

**Use case**: When evidence sources are redundant or you only trust the most reliable one.

**CLAIR verdict**: Not suitable for independent evidence aggregation (fails D6, D7).

### 6.2 Bounded Sum (Aggressive Aggregation)

```
aggregate_bounded(c₁, c₂) = min(1, c₁ + c₂)
```

**Properties**:
- Can reach 1 quickly (two 0.5 pieces → 1.0)
- No diminishing returns below saturation
- Linear increase

**Problem**: Reaches certainty too easily. Two moderately confident pieces shouldn't yield total certainty.

**CLAIR verdict**: Too aggressive. Doesn't model diminishing returns.

### 6.3 Averaging (Consensus Aggregation)

```
aggregate_avg(c₁, c₂) = (c₁ + c₂) / 2
```

**Properties**:
- Always between inputs
- Doesn't increase confidence overall
- Models "consensus view"

**Use case**: When sources might be biased in different directions, and you want a balanced view.

**CLAIR verdict**: Not suitable for independent supporting evidence. Fails D3, D6.

### 6.4 Geometric Mean (Multiplicative Consensus)

```
aggregate_geom(c₁, c₂) = √(c₁ × c₂)
```

**Properties**:
- Penalizes disagreement more than average
- Still always between inputs
- One low confidence drags down result

**Use case**: When you need all evidence to be strong for high confidence.

**CLAIR verdict**: Not suitable for aggregation. Fails D3.

### 6.5 Probabilistic OR (Our ⊕)

```
aggregate_prob(c₁, c₂) = c₁ + c₂ - c₁ × c₂
```

**Properties**:
- Always at least as high as max
- Diminishing returns
- Approaches but never reaches 1
- Models independent survival of doubt

**CLAIR verdict**: Suitable for independent evidence aggregation.

### 6.6 Summary Table

| Operation | D3 Mono | D6 Conv | D7 Dimin | When to use |
|-----------|---------|---------|----------|-------------|
| max | ✗ | ✗ | ✗ | Redundant sources |
| bounded sum | ✓ | ✓ | ✗ | Never (too aggressive) |
| average | ✗ | ✗ | N/A | Consensus of biased sources |
| geometric mean | ✗ | ✗ | N/A | Need unanimous strong evidence |
| **⊕ (prob OR)** | ✓ | ✓ | ✓ | **Independent evidence** |

---

## 7. The Independence Assumption

### 7.1 How Critical Is Independence?

**Very critical.** The ⊕ formula assumes evidence is probabilistically independent. If not:

**Overestimation risk**: Two correlated sources treated as independent overcounts evidence.
- If Alice and Bob always agree, treating them as two independent witnesses is wrong.
- Correct: count as roughly one witness with slightly higher reliability.

**Underestimation risk** (less common): If evidence is negatively correlated (when one is high, other tends to be low), treating as independent might undercount.

### 7.2 What To Do About Correlation

**Option A: Detect and merge correlated evidence**

Before aggregating, identify correlated sources and merge them into a single "effective" evidence with adjusted confidence.

How to merge? Possible approaches:
- Average the confidences
- Take max
- Apply correlation discount factor

**Option B: Use full Subjective Logic fusion**

The full Subjective Logic framework handles dependent evidence through different fusion operators:
- Cumulative fusion (independent)
- Averaging fusion (dependent but equally reliable)
- Weighted belief fusion (dependent, different weights)

**Option C: Explicit correlation modeling**

Track correlation coefficients between evidence sources. Adjust the combination formula:

```
aggregate_correlated(c₁, c₂, ρ) = ???
```

Where ρ ∈ [-1, 1] is the correlation coefficient.

This is the domain of **Task 2.13**. For now, we note that ⊕ requires independence.

---

## 8. N-ary Aggregation

### 8.1 Extending to Multiple Sources

For n independent evidence sources:

```
aggregate(c₁, c₂, ..., cₙ) = 1 - ∏ᵢ(1 - cᵢ)
```

This is just iterated ⊕, which by associativity equals:
```
c₁ ⊕ c₂ ⊕ ... ⊕ cₙ
```

### 8.2 Properties of N-ary Aggregation

**Theorem (N-ary Boundedness)**: For any cᵢ ∈ [0,1]:
```
0 ≤ 1 - ∏ᵢ(1 - cᵢ) ≤ 1
```

**Proof**: Each (1-cᵢ) ∈ [0,1], so product is in [0,1], so 1 - product is in [0,1]. ∎

**Theorem (Convergence Rate)**: For n identical confidences c:
```
aggregate(c, c, ..., c) = 1 - (1-c)ⁿ
```

As n → ∞, this approaches 1 exponentially fast.

**Example**: c = 0.3, n = 10
```
1 - (0.7)^10 = 1 - 0.028 = 0.972
```

Ten weak pieces of independent evidence yield high combined confidence!

### 8.3 Is This Reasonable?

This might seem too optimistic. But consider:

**Scenario**: Ten independent witnesses each claim they saw the suspect at the scene. Each is 30% reliable (often makes mistakes, sometimes lies).

The aggregate formula says: probability that ALL ten are wrong = 0.7^10 ≈ 2.8%. So we're 97.2% confident the suspect was there.

Is this right? If the witnesses are **truly independent** (didn't collude, didn't influence each other, no common error source), then yes—it's extremely unlikely ALL ten would be wrong by chance.

If they're NOT independent (maybe they all read the same misleading newspaper account), then the calculation is wrong. But that's a failure of the independence assumption, not the aggregation rule.

---

## 9. Practical Considerations

### 9.1 When to Aggregate vs. When to Derive

**Aggregation** (use ⊕):
- Multiple independent sources
- Each source alone supports the conclusion
- Sources don't depend on each other

**Derivation** (use ×):
- Sequential inference chain
- Each step depends on the previous
- Modus ponens, transitive closure, etc.

**Example**:
```clair
-- Derivation (multiplicative)
let premise1 = belief("All men are mortal", 0.99)
let premise2 = belief("Socrates is a man", 0.95)
let conclusion = derive premise1, premise2 by modus_ponens
-- confidence = 0.99 × 0.95 = 0.94

-- Aggregation (⊕)
let evidence1 = belief("Historical records show Socrates died", 0.8)
let evidence2 = belief("No human has lived >200 years", 0.95)
let conclusion2 = aggregate evidence1, evidence2
-- confidence = 0.8 ⊕ 0.95 = 0.8 + 0.95 - 0.76 = 0.99
```

### 9.2 Combining Aggregation with Defeat

When aggregated evidence faces defeat:

```
A = aggregate(e₁, e₂, e₃)  -- base confidence from aggregation
D undercuts A              -- defeater weakens A

A_final = A × (1 - D)
```

Aggregation happens first (combining evidence), then defeat applies to the aggregate.

### 9.3 Aggregation in the DAG

In CLAIR's justification DAG:

```
           conclusion
               |
          [aggregate]
         /    |    \
        j₁   j₂   j₃    (support edges)

Confidence propagation:
  c = j₁.conf ⊕ j₂.conf ⊕ j₃.conf
```

This naturally fits the DAG structure. The `aggregate` node combines its support edges using ⊕.

---

## 10. Formalization

### 10.1 Lean 4 Definition (Building on Thread 8)

```lean
/-- N-ary aggregation of independent evidence -/
def aggregate (confs : List Confidence) : Confidence :=
  ⟨1 - confs.foldl (fun acc c => acc * (1 - c.val)) 1, aggregate_bounded confs⟩

/-- Aggregation preserves bounds -/
theorem aggregate_bounded (confs : List Confidence) :
    0 ≤ 1 - confs.foldl (fun acc c => acc * (1 - c.val)) 1 ∧
    1 - confs.foldl (fun acc c => acc * (1 - c.val)) 1 ≤ 1 := by
  constructor
  · -- Product of [0,1] values is in [0,1], so 1 - product ≥ 0
    have h : 0 ≤ confs.foldl (fun acc c => acc * (1 - c.val)) 1 := by
      induction confs with
      | nil => simp
      | cons c cs ih =>
        simp [List.foldl]
        exact mul_nonneg ih (sub_nonneg_of_le c.property.2)
    have h2 : confs.foldl (fun acc c => acc * (1 - c.val)) 1 ≤ 1 := by
      induction confs with
      | nil => simp
      | cons c cs ih =>
        simp [List.foldl]
        calc confs.foldl _ _ * (1 - c.val)
          ≤ 1 * 1 := by nlinarith [ih, c.property.1, c.property.2]
          _ = 1 := by ring
    linarith
  · -- 1 - product ≤ 1 since product ≥ 0
    have h : 0 ≤ confs.foldl (fun acc c => acc * (1 - c.val)) 1 := sorry -- as above
    linarith
```

### 10.2 Key Theorems

```lean
/-- Aggregation is monotonic: adding evidence never decreases confidence -/
theorem aggregate_monotonic (c : Confidence) (cs : List Confidence) :
    (aggregate cs).val ≤ (aggregate (c :: cs)).val := by
  sorry -- Proof via product inequality

/-- Aggregation with constant confidence converges to 1 -/
theorem aggregate_limit (c : Confidence) (hc : c.val > 0) :
    Filter.Tendsto (fun n => aggregate (List.replicate n c)) Filter.atTop (nhds 1) := by
  -- 1 - (1-c)^n → 1 as n → ∞
  sorry

/-- Two-element aggregation equals ⊕ -/
theorem aggregate_two (c₁ c₂ : Confidence) :
    aggregate [c₁, c₂] = c₁ ⊕ c₂ := by
  simp [aggregate, oplus]
  ring
```

### 10.3 Integration with JustificationNode

From Thread 2's proposal:
```lean
inductive JustificationNode where
  -- ... existing constructors ...
  | aggregate :
      (lines : List JustificationRef) →
      (combinationRule : CombinationRule) →
      JustificationNode

inductive CombinationRule where
  | independent  -- Use ⊕ (probabilistic OR)
  | correlated : CorrelationModel → CombinationRule  -- Task 2.13
  | weighted : List Weight → CombinationRule  -- Weighted combination
```

---

## 11. What I Don't Know

### 11.1 Theoretical Gaps

1. **Optimal aggregation under uncertainty about independence**: If we're not sure whether evidence is independent, what's the robust combination rule?

2. **Calibration preservation**: If individual confidences are well-calibrated, is the aggregate well-calibrated?

3. **Information loss**: Does aggregating (e₁ ⊕ e₂) lose information compared to keeping e₁ and e₂ separate?

### 11.2 Design Questions

1. **Should aggregation be explicit or implicit?**: In the DAG, do we mark certain nodes as "aggregate" or infer from structure?

2. **What's the default for unlabeled combination?**: If a belief has multiple supports without explicit labels, use × or ⊕?

3. **How to verify independence?**: Can CLAIR detect when evidence sources are likely correlated?

### 11.3 Connections to Other Threads

1. **Thread 2.13 (Correlated evidence)**: How to extend beyond the independence assumption
2. **Thread 5 (Belief revision)**: How does aggregation interact with evidence retraction?
3. **Thread 6 (Multi-agent)**: Is inter-agent evidence combination similar to aggregation?

---

## 12. Conclusions

### 12.1 Core Answer

**How do independent lines of evidence combine?**

Using **probabilistic OR (⊕)**:
```
aggregate(c₁, c₂, ..., cₙ) = 1 - ∏ᵢ(1 - cᵢ)
                           = c₁ ⊕ c₂ ⊕ ... ⊕ cₙ
```

**Interpretation**: Combined confidence is the probability that at least one piece of evidence successfully establishes the conclusion, assuming each piece has independent chance of success equal to its confidence.

### 12.2 Key Insights

1. **⊕ is the right operation for independent aggregation** — satisfies all desiderata (boundedness, monotonicity, diminishing returns, convergence)

2. **Distinct from conjunction (×)** — aggregation increases confidence; conjunction can decrease it

3. **Independence assumption is critical** — correlated evidence requires different treatment (Task 2.13)

4. **N-ary aggregation is straightforward** — just iterated ⊕ or equivalently 1 - ∏(1-cᵢ)

5. **"Survival of doubt" interpretation** — aggregate confidence = probability that not all evidence fails

### 12.3 Connection to Prior Art

| Approach | CLAIR Correspondence |
|----------|---------------------|
| Probability (independent disjunction) | Direct match: ⊕ = P(A∨B) |
| Subjective Logic cumulative fusion | Similar spirit, different formula |
| Dempster-Shafer combination | Related but more general |
| Fuzzy logic algebraic sum | Exact match |
| Condorcet jury theorem | Same independence requirement |

### 12.4 Task Status

**Task 2.11: SUBSTANTIALLY EXPLORED**

What's settled:
- ⊕ is appropriate for independent evidence
- Mathematical properties verified
- Interpretation clarified
- Integration with DAG structure defined

What remains for related tasks:
- **Task 2.13**: Correlated evidence (non-independent case)
- **Task 8**: Lean 4 formalization of aggregation
- **Task 5**: Interaction with belief revision (evidence retraction)

---

## 13. References

### Primary Sources

- **Jøsang, A.** (2016). *Subjective Logic: A Formalism for Reasoning Under Uncertainty.* Springer.
  - Chapters on cumulative fusion and dependent evidence

- **Shafer, G.** (1976). *A Mathematical Theory of Evidence.* Princeton.
  - Dempster-Shafer theory foundations

- **Klement, E.P., Mesiar, R., Pap, E.** (2000). *Triangular Norms.* Springer.
  - T-norms and t-conorms, including algebraic sum

### Secondary Sources

- **Pearl, J.** (1988). *Probabilistic Reasoning in Intelligent Systems.* Morgan Kaufmann.
  - Independence and Bayesian combination

- **List, C. & Pettit, P.** (2002). "Aggregating Sets of Judgments." *Economics and Philosophy.*
  - Judgment aggregation, impossibility results

- **Clemen, R.T. & Winkler, R.L.** (1999). "Combining Probability Distributions from Experts."
  *Risk Analysis.* — Expert opinion aggregation

### Online Resources

- [Wikipedia: Dempster-Shafer Theory](https://en.wikipedia.org/wiki/Dempster%E2%80%93Shafer_theory)
- [Wikipedia: Condorcet's Jury Theorem](https://en.wikipedia.org/wiki/Condorcet%27s_jury_theorem)
- [Stanford Encyclopedia: Evidence](https://plato.stanford.edu/entries/evidence/)

---

*Thread 2.11 Status: Substantially explored. ⊕ is the correct operation for independent evidence aggregation. Mathematical properties proven. "Survival of doubt" interpretation established. Independence assumption clarified as critical. Ready for Lean formalization. Task 2.13 (correlated evidence) identified as important follow-up.*
