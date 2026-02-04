# R2: Stratification Mapping — Lean Proofs to IR Model

## Research Question

How do the Lean stratification proofs (from `formal/lean/CLAIR/Belief/Stratified.lean`) map to practical implications for CLAIR as an IR? Which theorems constrain valid traces, which inform Thinker behavior, and which are irrelevant to the new model?

**Thesis Connection:** Stratification was designed to prevent self-reference paradoxes through Tarski's hierarchy and Löb discount. This mapping connects the formal theory to practical IR operations, testing whether the theoretical foundation supports, undermines, or refines the viability thesis.

**Validation Criteria:**
- Map all stratification proofs to IR implications
- Classify by relevance and constraint type
- Identify gaps between formalization and spec
- Connect to D5 findings
- Open questions

---

## Overview: Stratification Proofs in Lean

### Source Files

| File | Purpose | Status |
|------|---------|--------|
| `formal/lean/CLAIR/Belief/Stratified.lean` | Stratified beliefs, Löb discount, anti-bootstrapping | Fully proven |
| `formal/lean/CLAIR/Belief/DAG.lean` | DAG structure, acyclicity, grounding | Partially proven (some `sorry`) |

### Key Concepts Formalized

1. **Tarski's Hierarchy** — Level-n beliefs can only reference level-m beliefs where m < n
2. **Löb Discount** — Confidence penalty for meta-beliefs: c → c²
3. **Anti-Bootstrapping** — No finite meta-chain can increase confidence
4. **Well-Foundedness** — All chains terminate at level 0

---

## Part 1: Stratified.lean Theorems → IR Implications

### Theorem 1: `no_self_introspection`

**Formal Statement:**
```lean
theorem no_self_introspection (n : Nat) : ¬(n < n) := Nat.lt_irrefl n
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | Critical |
| **Constraint Type** | Validity |
| **Trace Constraint** | A belief cannot reference itself at the same level |
| **Practical Meaning** | Prevents direct self-justification loops like `b1: "X is true because b1 says so"` |

**Example Violation (Invalid):**
```clair
b1 .9 L0 @self <b1 "I am certain"  ; INVALID: self-reference at same level
```

**Connection to DAG.lean:**
- The `Acyclic` property in `DAG.lean` (line 163) formalizes this for the full DAG
- `no_self_introspection` is the *single-node* version of acyclicity

**D5 Finding Support:**
- D5 Example 1 (self-correction) shows valid meta-reasoning: L0 → L1 → L0
- The L1 belief ("b2 is wrong") references L0, not itself — valid

**Verdict:** ✅ **Applies directly** — this is a fundamental validity constraint for all CLAIR traces.

---

### Theorem 2: `no_circular_introspection`

**Formal Statement:**
```lean
theorem no_circular_introspection {m n : Nat} (h : m < n) : ¬(n < m) := by
  intro h'
  exact Nat.lt_irrefl m (Nat.lt_trans h h')
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | Critical |
| **Constraint Type** | Validity |
| **Trace Constraint** | No circular meta-reasoning: if belief A at level n references belief B at level m < n, then B cannot (transitively) reference A |
| **Practical Meaning** | Prevents "I believe you believe me believe..." cycles |

**Example Violation (Invalid):**
```clair
b1 .9 L0 @self "X is true"
b2 .8 L1 @self <b1 "I believe b1"
b3 .7 L0 @self <b2 "b2 is wrong"  ; INVALID: L0 referencing L1 which references L0
```

**Connection to DAG.lean:**
- The `Acyclic` property (line 163) prohibits circular reachability
- `no_circular_introspection` is the *meta-level* version

**D5 Finding Support:**
- D5 identified that LLMs accidentally create L1→L0→L1 cycles when misusing levels
- This theorem formally proves why such cycles are invalid

**Verdict:** ✅ **Applies directly** — critical for multi-level traces.

---

### Theorem 3: `no_confidence_bootstrap`

**Formal Statement:**
```lean
theorem no_confidence_bootstrap (c : Confidence) (k : Nat) :
    (loebChain c k : ℝ) ≤ (c : ℝ) := by
  induction k with
  | zero => simp only [loebChain]; rfl
  | succ k ih =>
    calc (loebChain c (k + 1) : ℝ)
      _ ≤ (loebChain c k : ℝ) := loebChain_decreasing c k
      _ ≤ (c : ℝ) := ih

def loebChain (c : Confidence) : Nat → Confidence
  | 0 => c
  | k + 1 => loebDiscount (loebChain c k)
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | Critical |
| **Constraint Type** | Validity + Operational |
| **Trace Constraint** | No finite chain of meta-reasoning can increase confidence above the base level |
| **Practical Meaning** | Prevents "I'm reliable" → "my beliefs are trustworthy" → ... bootstrapping |

**Example: Confidence Decrease Through Levels**
```clair
b1 .9 L0 @self "the code is correct"
b2 .81 L1 @self <b1 "I believe b1"      ; .9² = .81
b3 .65 L2 @self <b2 "I believe b2"      ; .81² ≈ .65
b4 .43 L3 @self <b3 "I believe b3"      ; .65² ≈ .43
```

**Operational Guidance for Thinkers:**
- If you have .9 confidence at L0, the maximum at L1 is .81, L2 is .65, L3 is .43
- Thinkers should not increase confidence when adding meta-levels

**Connection to D5:**
- D5 Counter-Example 3 identified that this creates "incentive to stay at L0"
- The theorem proves the confidence penalty is mathematically unavoidable

**Verdict:** ✅ **Applies directly** — this is the core protection against confidence inflation.

---

### Theorem 4: `loebDiscount_strict_lt`

**Formal Statement:**
```lean
theorem loebDiscount_strict_lt (c : Confidence) (h0 : 0 < (c : ℝ)) (h1 : (c : ℝ) < 1) :
    (loebDiscount c : ℝ) < (c : ℝ) := by
  simp only [loebDiscount, Subtype.coe_mk]
  have : (c : ℝ) * (c : ℝ) < (c : ℝ) * 1 := by
    apply mul_lt_mul_of_pos_left h1 h0
  linarith

def loebDiscount (c : Confidence) : Confidence :=
  ⟨(c : ℝ) * (c : ℝ), mul_mem' c c⟩
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | High |
| **Constraint Type** | Operational |
| **Trace Constraint** | Meta-beliefs (with Löb discount) are **strictly** less confident than their source for 0 < c < 1 |
| **Practical Meaning** | The confidence penalty is real and unavoidable |

**Edge Cases:**
- `c = 0`: `loebDiscount 0 = 0` (theorem `loebDiscount_zero`, line 172)
- `c = 1`: `loebDiscount 1 = 1` (theorem `loebDiscount_one`, line 167)

**Connection to D5:**
- D5 found that Löb discount is **too aggressive** for comparative meta-beliefs
- This theorem shows the strict decrease is mathematically correct for endorsement meta-beliefs
- The issue is that natural language uses comparative ("X > Y") not endorsement ("I believe X")

**Verdict:** ✅ **Applies with refinement** — the theorem is correct, but D5 shows it doesn't match natural meta-reasoning patterns.

---

### Theorem 5: `loebChain_decreasing`

**Formal Statement:**
```lean
theorem loebChain_decreasing (c : Confidence) (k : Nat) :
    (loebChain c (k + 1) : ℝ) ≤ (loebChain c k : ℝ) := by
  simp only [loebChain]
  exact loebDiscount_le (loebChain c k)
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | High |
| **Constraint Type** | Operational |
| **Trace Constraint** | Confidence decreases monotonically through each meta-level |
| **Practical Meaning** | Each level jump applies another squaring: c → c² → c⁴ → c⁸ → ... |

**Example: Exponential Decay**
```clair
; Starting at c = 0.9
L0: 0.9     (c)
L1: 0.81    (c²)
L2: 0.6561  (c⁴)
L3: 0.4305  (c⁸)
L4: 0.1853  (c¹⁶)
```

**Connection to D5:**
- D5 found that LLMs avoid levels because of this penalty
- The theorem proves the exponential decay is unavoidable

**Operational Implication:**
- Thinkers should use levels sparingly — 3+ levels reduces confidence dramatically
- Most traces should stay at L0-L1

**Verdict:** ✅ **Applies directly** — provides quantitative guidance for level usage.

---

### Theorem 6: `introspectWithLoeb_confidence`

**Formal Statement:**
```lean
theorem introspectWithLoeb_confidence (h : m < n) (b : StratifiedBelief m α) :
    (introspectWithLoeb h b).confidence = loebDiscount b.confidence := rfl
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | High |
| **Constraint Type** | Operational |
| **Trace Constraint** | When using `introspectWithLoeb` (recommended for meta-beliefs), confidence is automatically squared |
| **Practical Meaning** | The Thinker doesn't choose the meta-confidence — it's computed from the base confidence |

**Connection to Spec:**
- The spec grammar (line 21) allows explicit confidence: `belief := id confidence level ...`
- The Lean theorem shows confidence **should** be computed, not chosen
- **Gap identified:** Spec doesn't specify whether confidence is chosen or computed

**Operational Guidance:**
```clair
; If b1 has confidence 0.9 and Thinker wants a meta-belief:
; Correct (computed):
b2 .81 L1 @self <b1 "I believe b1"  ; .9²

; Incorrect (chosen higher):
b2 .95 L1 @self <b1 "I believe b1"  ; Violates theorem!
```

**Verdict:** ✅ **Applies directly** — spec v0.2 should clarify that meta-confidence is computed.

---

### Theorem 7: Level-Preserving Operations

**Formal Statements:**
```lean
; Derivation (level-preserving)
def derive₂ (f : α → β → γ)
    (b₁ : StratifiedBelief n α) (b₂ : StratifiedBelief n β) : StratifiedBelief n γ

; Aggregation (level-preserving)
def aggregate (b₁ b₂ : StratifiedBelief n α) (combine : α → α → α) :
    StratifiedBelief n α

; Defeat (level-preserving)
def applyUndercut (b : StratifiedBelief n α) (d : Confidence) : StratifiedBelief n α
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | Medium |
| **Constraint Type** | Descriptive |
| **Trace Constraint** | Derivation, aggregation, and defeat stay at the same level |
| **Practical Meaning** | These operations don't require level changes |

**Example: All at L0**
```clair
b1 .9 L0 @self "X is true"
b2 .8 L0 @self "Y is true"
b3 .72 L0 @self <b1,b2 "therefore Z"  ; derivation stays at L0
```

**Connection to D5:**
- D5 found that most reasoning naturally stays at L0
- The theorem confirms this is valid — levels are only needed for meta-reasoning

**Verdict:** ✅ **Applies** — confirms that L0-only traces are valid.

---

## Part 2: DAG.lean Theorems → IR Implications

### Theorem 8: `Acyclic` (Well-Defined)

**Formal Statement:**
```lean
def Acyclic (doc : CLAIRDocument) : Prop :=
  ∀ b : BeliefId, ¬ Reachable doc b b

inductive Reachable (doc : CLAIRDocument) : BeliefId → BeliefId → Prop where
  | step : ∀ {a b : BeliefId}, justifies doc a b → Reachable doc a b
  | trans : ∀ {a b c : BeliefId}, Reachable doc a b → Reachable doc b c → Reachable doc a c
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | Critical |
| **Constraint Type** | Validity |
| **Trace Constraint** | No belief is transitively reachable from itself |
| **Practical Meaning** | The justification graph must be a DAG (directed acyclic graph) |

**Example Violation (Invalid):**
```clair
b1 .9 L0 @self <b3 "X"
b2 .8 L0 @self <b1 "Y"
b3 .7 L0 @self <b2 "Z"  ; INVALID: b1 → b2 → b3 → b1 forms a cycle
```

**Connection to Spec:**
- Spec line 147: "Graph must be acyclic (no belief can transitively justify itself)"
- DAG.lean formalizes this as `Acyclic`

**Validation Tools:**
- Cycle detection algorithms (DFS, topological sort)
- Required for trace validators

**Verdict:** ✅ **Applies directly** — fundamental validity constraint.

---

### Theorem 9: `FullyGrounded` (Well-Defined)

**Formal Statement:**
```lean
inductive Grounded (doc : CLAIRDocument) : BeliefId → Prop where
  | axiom : ∀ (id : BeliefId) (b : BeliefNode), b ∈ doc.nodes → b.id = id →
      b.isAxiom = true → Grounded doc id
  | derived : ∀ (id : BeliefId) (b : BeliefNode), b ∈ doc.nodes → b.id = id →
      (∀ e ∈ b.justifications, Grounded doc e.premise) →
      Grounded doc id

def FullyGrounded (doc : CLAIRDocument) : Prop :=
  ∀ b ∈ doc.nodes, Grounded doc b.id
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | High |
| **Constraint Type** | Validity |
| **Trace Constraint** | Every belief is either an axiom or all its premises are grounded |
| **Practical Meaning** | No "floating" beliefs — all trace back to sources |

**Example Violation (Invalid):**
```clair
b1 .9 L0 @self <b99 "X"  ; INVALID: b99 doesn't exist
```

**Connection to Spec:**
- Spec line 148: "All referenced IDs must exist"
- DAG.lean `valid_refs` field (line 120) enforces this

**Validation Tools:**
- Reference existence check
- "Orphan detection" for beliefs with invalid justifications

**Verdict:** ✅ **Applies directly** — ensures trace coherence.

---

### Theorem 10: `ValidCLAIRDocument` (Partially Proven)

**Formal Statement:**
```lean
structure ValidCLAIRDocument extends CLAIRDocument where
  acyclic : Acyclic toCLAIRDocument
  grounded : FullyGrounded toCLAIRDocument
```

**IR Model Implication:**
| Aspect | Detail |
|--------|--------|
| **Relevance** | Critical |
| **Constraint Type** | Validity |
| **Trace Constraint** | A valid CLAIR document is acyclic AND fully grounded |
| **Practical Meaning** | This is the complete validity checklist |

**Connection to D5:**
- D5 found that LLMs produce invalid traces (circular levels, missing references)
- `ValidCLAIRDocument` provides the formal checklist for validation tools

**Validation Checklist:**
1. ✅ Acyclic: no reachable-from-self cycles
2. ✅ Grounded: all references exist
3. ✅ Confidence in [0,1] (from `Confidence` type)
4. ✅ Levels respected (from `Stratified.lean`)

**Verdict:** ✅ **Applies directly** — defines validity for trace validators.

---

## Part 3: Gaps Between Formalization and Spec

### Gap 1: Löb Discount Not in Spec Grammar

**Issue:** The spec grammar (line 21) allows explicit confidence:
```
belief := id confidence level source justifications? invalidations? content
```

**Lean Theorem:** `introspectWithLoeb_confidence` (Theorem 6) shows confidence should be **computed** via Löb discount for meta-beliefs.

**Impact:** Thinkers can manually specify meta-confidence that violates the Löb discount:
```clair
b1 .9 L0 @self "X is true"
b2 .95 L1 @self <b1 "I believe b1"  ; Should be .81, but .95 is syntactically valid
```

**Recommendation for Spec v0.2:**
- Add constraint: "Meta-beliefs (L1+) must have confidence ≤ source²"
- Or remove explicit confidence from meta-beliefs: compute automatically

---

### Gap 2: No Distinction Between Endorsement and Comparative Meta-Beliefs

**Issue:** The Lean formalization assumes endorsement meta-beliefs ("I believe X"), but D5 found natural language uses comparative ("X > Y") and qualitative ("X is limited").

**Lean Theorem:** `loebDiscount_strict_lt` (Theorem 4) proves c² < c for all 0 < c < 1.

**D5 Finding:** Comparative meta-beliefs can have **higher** confidence than alternatives:
```clair
b1 .6 L0 @self "use async/await"
b2 .5 L0 @self "use thread pool"
b3 .7 L1 @self <b1,b2 "async has higher concurrency than thread pool"
; Intuition: .7 > .6, but theorem would require max .5² = .25
```

**Recommendation for Spec v0.2:**
- Distinguish meta-belief types: `endorsement` (Löb discount) vs `comparative` (no discount)
- Or relax Löb discount: c → √c instead of c → c²

---

### Gap 3: DAG.lean Has `sorry` Proofs

**Issue:** Two theorems in DAG.lean use `sorry` (incomplete proofs):
```lean
theorem acyclic_implies_wellFounded (doc : CLAIRDocument) (h : Acyclic doc) :
    WellFoundedJustification doc := by
  sorry  -- Full proof requires more infrastructure

theorem wellFounded_axioms_implies_grounded (doc : CLAIRDocument)
    (hwf : WellFoundedJustification doc)
    (hax : doc.axioms.length > 0) :
    FullyGrounded doc := by
  sorry  -- Full proof requires more infrastructure
```

**Impact:** The formalization claims acyclicity implies well-foundedness, but this isn't fully proven.

**Relevance to IR Model:** Low — the `Acyclic` and `Grounded` properties are well-defined and can be validated separately. The `sorry` proofs don't affect IR validity constraints.

**Recommendation:** Complete these proofs for rigor, or remove if they're not needed for the IR model.

---

### Gap 4: No Formalization of Invalidation Conditions

**Issue:** The spec defines invalidations (`?["condition"]`) and DAG.lean includes them in `BeliefNode`, but there's no formal semantics for:
- When invalidations trigger
- How invalidations affect confidence
- Whether invalidations are required or optional

**Impact:** D5 found that LLMs forget to add invalidations ("invalidation amnesia"). Without formal semantics, there's no way to validate whether invalidations are complete.

**Recommendation for Spec v0.2:**
- Define invalidation semantics: what happens when `?["condition"]` is true?
- Add invalidation completeness guidelines (when are they required?)
- Consider formalizing in Lean

---

## Part 4: Connection to D5 Findings

### D5 Finding 1: "Meta-Beliefs Occur Naturally"

**Lean Support:** Theorems `no_self_introspection` and `no_circular_introspection` prove that meta-beliefs are a valid (and necessary) part of the system — they just can't create cycles.

**IR Implication:** The formalization confirms D5's observation that self-correction, comparison, and qualification are legitimate use cases for levels.

---

### D5 Finding 2: "Löb Discount is Too Aggressive"

**Lean Support:** Theorem `loebDiscount_strict_lt` proves the strict decrease is mathematically correct for **endorsement** meta-beliefs.

**IR Implication:** The issue isn't the theorem — it's that natural language uses comparative meta-beliefs, which aren't covered by the formalization. This is a **gap in Lean**, not a mistake.

**Recommendation:** Extend Lean formalization to cover comparative meta-beliefs with a different discount function.

---

### D5 Finding 3: "LLMs Cannot Produce Stratified Traces Reliably"

**Lean Support:** Theorems provide clear validation rules that can be automated. The issue isn't the formalization — it's the lack of tools.

**IR Implication:** Spec v0.2 should reference these theorems as validation rules for automated tools:
- Level checker: ensure no L1 → L0 references
- Confidence checker: ensure meta-beliefs respect Löb discount
- Cycle detector: ensure `Acyclic` property

---

### D5 Finding 4: "Stratification Creates Incentive to Stay at L0"

**Lean Support:** Theorem `loebChain_decreasing` proves the exponential decay is unavoidable.

**IR Implication:** This is a **feature, not a bug** — it prevents confidence bootstrapping. The incentive to stay at L0 is intentional.

**Recommendation:** Spec should emphasize that levels are for specific use cases (self-correction tracking, meta-reasoning auditing), not for everyday reasoning.

---

## Part 5: Summary Table

| Theorem | Relevance | Constraint Type | IR Implication | D5 Connection |
|---------|-----------|-----------------|----------------|---------------|
| `no_self_introspection` | Critical | Validity | No same-level self-reference | Supports meta-belief validity |
| `no_circular_introspection` | Critical | Validity | No circular meta-reasoning | Explains L1→L0→L1 cycle failure |
| `no_confidence_bootstrap` | Critical | Validity + Operational | Meta-chains can't inflate confidence | Proves "incentive to stay at L0" |
| `loebDiscount_strict_lt` | High | Operational | Meta-beliefs strictly less confident | Shows Löb discount is too aggressive |
| `loebChain_decreasing` | High | Operational | Exponential decay through levels | Quantifies confidence penalty |
| `introspectWithLoeb_confidence` | High | Operational | Meta-confidence is computed, not chosen | Gap: spec allows manual choice |
| Level-preserving ops | Medium | Descriptive | Derivation/aggregation/defeat stay at level | Confirms L0-only is valid |
| `Acyclic` | Critical | Validity | No reachable-from-self cycles | Validation tool requirement |
| `FullyGrounded` | High | Validity | All references exist | Orphan detection requirement |
| `ValidCLAIRDocument` | Critical | Validity | Acyclic + grounded | Complete validity checklist |

---

## Part 6: Recommendations for Spec v0.2

### 1. Add "Stratification" Section

Based on the Lean theorems, add to `formal/clair-spec.md`:

```markdown
## Stratification (Self-Reference Safety)

### Rules

1. **Level constraint**: A belief at level N can only justify beliefs at level ≥ N
2. **No circularity**: If L(n) references L(m) where m < n, then L(m) cannot transitively reference L(n)
3. **Löb discount**: Meta-beliefs MUST have confidence ≤ source² (endorsed meta-beliefs)
4. **Level preservation**: Derivation, aggregation, and defeat stay at the same level
```

### 2. Add "Validity Constraints" Section

```markdown
## Validity Constraints

A CLAIR trace is valid if it satisfies:

1. **Acyclicity**: No belief is reachable from itself via justification edges
2. **Grounding**: All referenced belief IDs exist in the trace
3. **Confidence bounds**: All confidence values are in [0, 1]
4. **Stratification**: Level constraints are respected (see above)
5. **Löb compliance**: Meta-beliefs respect confidence discount (c² for endorsement)
```

### 3. Add "Meta-Belief Patterns" Section

From D5 + Lean:

```markdown
## Meta-Belief Patterns

### When to Use Levels

Use L1+ for:
- **Revision**: "b2 was wrong because..."
- **Comparison**: "async beats thread pool because..."
- **Qualification**: "b1 is limited by..."
- **Grounding**: "b1 assumes..."

Use L0 for:
- Ground-level claims about the problem
- Algorithmic reasoning
- System design decisions
- Most everyday reasoning

### Confidence Rules

- **Endorsement meta-beliefs**: "I believe b1" → max confidence = conf(b1)²
- **Comparative meta-beliefs**: "b1 > b2" → no Löb discount (TBD: formalization needed)
- **Qualitative meta-beliefs**: "b1 is limited" → no Löb discount (TBD: formalization needed)
```

### 4. Add "Validation" Section

```markdown
## Validation

Tools should check:

1. **Cycle detection**: DFS to detect reachable-from-self violations
2. **Reference existence**: All <id> references must exist
3. **Level constraints**: No L1 → L0 justification edges
4. **Löb discount**: Meta-beliefs must have confidence ≤ source²
5. **Confidence bounds**: All values in [0, 1]
```

---

## Part 7: Open Questions

1. **Comparative Meta-Belief Formalization:** Can we extend Lean to cover comparative ("X > Y") and qualitative ("X is limited") meta-beliefs with a different discount function?

2. **Invalidation Semantics:** Should invalidations be formalized in Lean? What are the formal semantics for when invalidations trigger and how they affect confidence?

3. **Automatic Level Inference:** Can we build tools that detect meta-beliefs post-hoc and assign levels automatically based on content patterns ("b1 is wrong" → L1)?

4. **L0-Only CLAIR:** If 90%+ of traces use only L0, can we define a "CLAIR Lite" that omits levels entirely? How would this affect validity constraints?

5. **Confidence Calibration for Meta-Beliefs:** How do we calibrate confidence for comparative meta-beliefs? The Löb discount (c → c²) assumes endorsement, but comparison is different.

6. **Tooling:** Can we build automated validators that check all validity constraints (acyclicity, grounding, Löb compliance) and suggest corrections?

7. **Empirical Studies:** Do humans actually query meta-reasoning ("Why did you change your mind?") in practice, or is stratification a theoretical concern?

---

## Conclusion

### Mapping Summary

| Component | Lean Status | IR Model Status | Gap |
|-----------|-------------|-----------------|-----|
| Level constraint | Fully proven | Specified in spec | None |
| Löb discount | Fully proven | NOT in spec grammar | Critical |
| Anti-bootstrapping | Fully proven | Not referenced | Add to spec |
| Acyclicity | Well-defined | Specified in spec | None |
| Grounding | Well-defined | Specified in spec | None |
| Comparative meta-beliefs | NOT formalized | Not in spec | Extend Lean + spec |
| Invalidation semantics | Defined but not proven | Specified in spec | Prove semantics |

### Thesis Impact

**Thesis:** CLAIR is a viable IR between Thinker and Assembler LLMs — it preserves *why* decisions were made, enables auditing, and doesn't lose essential information at the boundary.

**How R2 Supports the Thesis:**

1. **Structural Validity is Well-Defined:** The Lean theorems provide a complete formalization of what makes a CLAIR trace valid (acyclic, grounded, stratified).

2. **Confidence Algebra is Sound:** All stratification theorems are proven, confirming that confidence propagation is mathematically correct.

3. **Gaps are Fixable:** The identified gaps (Löb discount not in grammar, no comparative meta-belief formalization) are **operational**, not fundamental. They can be addressed in spec v0.2.

4. **Validation is Automatable:** The theorems provide clear rules for building automated validators.

**How R2 Refines the Thesis:**

1. **Stratification is Complex:** The Löb discount is mathematically correct but doesn't match natural language patterns (comparative/qualitative meta-beliefs).

2. **Tooling is Essential:** LLMs cannot reliably produce stratified traces without validation tools. The Lean theorems provide the rules for these tools.

3. **Meta-Beliefs Are Optional:** Most traces don't need levels. Stratification should be positioned as an "advanced feature" for specific use cases.

**Verdict:** **SUPPORTS WITH REFINEMENT** — The Lean formalization confirms CLAIR's structural validity and mathematical soundness. The gaps are operational (spec wording, tooling) not fundamental. Stratification is theoretically sound but operationally complex — it should be optional and supported by validation tools.

**Thesis Status:** **VIABLE** — CLAIR is a valid IR with well-defined structural constraints. Stratification adds value for specific use cases (self-correction tracking, meta-reasoning auditing) but requires spec improvements and tooling to be practical.
