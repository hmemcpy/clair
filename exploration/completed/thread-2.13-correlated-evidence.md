# Thread 2.13: Correlated Evidence in Aggregation

> **Status**: Active exploration (Session 20)
> **Task**: 2.13 How does aggregation handle correlated (not independent) evidence?
> **Question**: When evidence sources are not independent, how should their confidences combine? What happens if we incorrectly treat correlated evidence as independent?
> **Priority**: HIGH — The independence assumption in ⊕ is critical; violation leads to overcounting

---

## 1. The Problem

Thread 2.11 established that **independent** evidence combines via probabilistic OR (⊕):

```
aggregate(c₁, c₂, ..., cₙ) = 1 - ∏ᵢ(1 - cᵢ)
```

This formula assumes **genuine probabilistic independence**: each evidence source's "success" (correctly supporting the conclusion) is uncorrelated with the others.

But in practice, evidence is often **correlated**:

### 1.1 Examples of Correlated Evidence

**Case 1: Shared source**
- News article A reports that X happened
- News article B reports that X happened
- But both A and B cite the same Reuters wire report

If treated as independent, we'd get: c_A ⊕ c_B. But if both derive from the same source, they're really just one piece of evidence with slightly higher confidence (due to two outlets finding it plausible enough to republish).

**Case 2: Common cause**
- Witness A saw the suspect near the crime scene
- Witness B saw the suspect near the crime scene
- But both were at the same location, looking at the same angle

Their observations are correlated by position. If neither would have noticed except from that angle, they provide less independent confirmation than two witnesses at different locations.

**Case 3: Social influence**
- 10 people believe proposition P
- But they all learned about P from the same viral post
- Their beliefs are correlated by shared information exposure

Treating them as 10 independent witnesses massively overcounts the evidence.

**Case 4: Methodological correlation**
- Study A shows drug is effective (using method M)
- Study B shows drug is effective (using method M)
- Both use the same potentially biased methodology

The evidence is correlated because errors in method M would affect both identically.

### 1.2 The Overcounting Problem

If we naively apply ⊕ to correlated evidence:

```
True situation: 2 correlated sources, effective evidence = ~1.3 sources
Naive application: c₁ ⊕ c₂ (treating as 2 independent sources)
Result: Overconfidence
```

Example with numbers:
- c₁ = c₂ = 0.7, correlation ρ = 0.8 (highly correlated)
- Independent treatment: 0.7 ⊕ 0.7 = 0.91
- Correct treatment: should be closer to 0.7 (single source) than to 0.91

### 1.3 Why This Matters for CLAIR

CLAIR aims to accurately track epistemic state. If its aggregation mechanism overcounts correlated evidence, it will:

1. **Report overconfidence** — believing things more strongly than warranted
2. **Fail calibration** — reported confidence won't match true reliability
3. **Make poor decisions** — when decisions depend on confidence thresholds

This is not a niche edge case. Most real-world evidence is at least partially correlated.

---

## 2. Survey of Prior Art

### 2.1 Probability Theory: Correlated Variables

For two random variables with correlation coefficient ρ ∈ [-1, 1]:

**Independent (ρ = 0)**:
```
P(A ∨ B) = P(A) + P(B) - P(A)P(B) = a ⊕ b
```

**Perfectly correlated (ρ = 1)**:
```
P(A ∨ B) = max(P(A), P(B)) = max(a, b)
```
(They always succeed or fail together.)

**Perfectly anti-correlated (ρ = -1)**:
```
P(A ∨ B) = min(1, P(A) + P(B)) = min(1, a + b)
```
(When one succeeds, the other fails.)

**General case**:
No simple closed form in terms of marginals and ρ alone. The joint distribution matters.

**Key insight**: Correlation interpolates between ⊕ (ρ=0) and max (ρ=1).

### 2.2 Copula Theory

Copulas describe dependence structure separately from marginal distributions.

**Sklar's Theorem**: Every joint distribution F(x,y) can be written as:
```
F(x,y) = C(F_X(x), F_Y(y))
```
where C is a copula function mapping [0,1]² → [0,1].

**Common copulas**:
- **Product copula**: C(u,v) = uv — independence
- **Minimum copula (Fréchet upper)**: C(u,v) = min(u,v) — perfect positive correlation
- **Maximum copula (Fréchet lower)**: C(u,v) = max(0, u+v-1) — perfect negative correlation

For survival (complement) probabilities:
```
P(A' ∧ B') = Ĉ(1-a, 1-b)  where Ĉ is survival copula
P(A ∨ B) = 1 - Ĉ(1-a, 1-b)
```

**Gaussian copula** (common in finance):
```
C_ρ(u,v) = Φ₂(Φ⁻¹(u), Φ⁻¹(v); ρ)
```
where Φ₂ is bivariate normal CDF with correlation ρ, and Φ⁻¹ is inverse normal CDF.

**Relevance to CLAIR**: Copulas provide a mathematically principled way to model evidence correlation. But they require knowing the dependence structure, which CLAIR typically won't have.

### 2.3 Subjective Logic: Dependent Evidence

Jøsang's Subjective Logic explicitly addresses evidence dependence.

**Key distinction**:
- **Aleatory dependence**: Correlation in underlying random variables
- **Epistemic dependence**: Correlation in sources' knowledge/beliefs

**Subjective Logic operators**:
1. **Cumulative fusion (⊙)**: For independent sources
2. **Averaging fusion**: For dependent sources with equal weight
3. **Weighted belief fusion**: For dependent sources with different weights

**Averaging fusion formula** (for completely dependent sources):
```
ω_avg = (ω₁ ⊕ ω₂) / 2  (simplified)
```
More precisely:
```
b_avg = (b₁×u₂ + b₂×u₁ + 2b₁×b₂) / (u₁ + u₂ + 2×(b₁×u₂ + b₂×u₁ + b₁×b₂))
d_avg = (d₁×u₂ + d₂×u₁ + 2d₁×d₂) / (same denominator)
u_avg = 2u₁×u₂ / (same denominator)
```

**Key insight**: SL treats full dependence as "averaging" opinions rather than accumulating them.

**For CLAIR**: If two sources are fully dependent (ρ=1), the combined confidence should be something like their average or weighted combination, NOT their ⊕.

### 2.4 Dempster-Shafer: Dependency Handling

Classical Dempster's rule assumes independence. For dependent sources:

**Discounting approach** (Shafer 1976):
Before combining, discount sources based on reliability:
```
m'(A) = α × m(A)     for A ≠ Ω
m'(Ω) = 1 - α × (1 - m(Ω))
```
This reduces their effective weight.

**Coarsening approach**: Merge correlated sources into single "super-source" with combined mass function.

**Cautious rule** (Smets 1993):
```
m₁,₂(A) = ⋀_{B∧C=A} min(m₁(B), m₂(C))
```
Idempotent: m ⋀ m = m. Suitable when evidence might be dependent.

### 2.5 Bayesian Networks: Conditional Independence

Bayesian networks encode conditional independence structure:

```
           C (common cause)
          / \
         v   v
        A     B
```

Given C, A and B are independent: P(A,B|C) = P(A|C)×P(B|C)

But marginally (not conditioning on C), A and B are correlated.

**For CLAIR**: Could represent justification DAG with explicit conditional independence structure. But this requires knowing the causal/dependency graph.

### 2.6 Witness Reliability in Legal Theory

Jurisprudence has long grappled with correlated testimony:

**Corroboration requirements**:
- Some evidence types (e.g., accomplice testimony) require independent corroboration
- Courts discount "hearsay" because it chains from the same original source

**Independence factors considered**:
- Different vantage points
- No communication before testifying
- Different methods of observation

**Key principle**: "Independence" is evaluated, not assumed.

### 2.7 Meta-Analysis: Combining Study Results

In meta-analysis, combining correlated studies requires adjustment:

**Fixed effects model** (assumes homogeneity):
```
θ_combined = Σ(wᵢ × θᵢ) / Σwᵢ   where wᵢ = 1/Var(θᵢ)
```

**Random effects model** (allows heterogeneity):
Adds between-study variance τ² to account for correlation.

**Key adjustment**: Studies from the same lab, using the same method, or measuring the same population get reduced effective weight.

---

## 3. Analysis: What Correlation Means for CLAIR

### 3.1 Modeling Correlation

Let's define what "correlated evidence" means formally.

**Definition (Evidence Success)**:
For evidence e supporting conclusion P with confidence c, define random variable X_e:
- X_e = 1 with probability c (evidence "successfully supports" P)
- X_e = 0 with probability 1-c (evidence "fails to support" P)

**Definition (Independent Evidence)**:
Evidence e₁, e₂ are independent iff:
```
P(X_{e₁}=1 ∧ X_{e₂}=1) = P(X_{e₁}=1) × P(X_{e₂}=1) = c₁ × c₂
```

**Definition (Correlated Evidence)**:
Evidence e₁, e₂ with correlation coefficient ρ satisfy:
```
Cov(X_{e₁}, X_{e₂}) = ρ × √(c₁(1-c₁)) × √(c₂(1-c₂))
```
which gives:
```
P(X_{e₁}=1 ∧ X_{e₂}=1) = c₁c₂ + ρ√(c₁c₂(1-c₁)(1-c₂))
```

### 3.2 The General Aggregation Formula

For two correlated sources with correlation ρ:

```
P(at least one succeeds) = 1 - P(both fail)
                         = 1 - P(X₁=0 ∧ X₂=0)
                         = 1 - [(1-c₁)(1-c₂) + Cov(X₁=0, X₂=0)]
```

Since Cov(X₁=0, X₂=0) = Cov(1-X₁, 1-X₂) = Cov(X₁, X₂) = ρσ₁σ₂:

```
aggregate_ρ(c₁, c₂) = c₁ + c₂ - c₁c₂ - ρ√(c₁c₂(1-c₁)(1-c₂))
                    = (c₁ ⊕ c₂) - ρ√(c₁c₂(1-c₁)(1-c₂))
```

**Simplification**: Let σ = √(c₁c₂(1-c₁)(1-c₂)). Then:
```
aggregate_ρ(c₁, c₂) = (c₁ ⊕ c₂) - ρσ
```

### 3.3 Boundary Cases

**ρ = 0 (independent)**:
```
aggregate₀(c₁, c₂) = c₁ ⊕ c₂  ✓
```

**ρ = 1 (perfectly correlated)**:
Need to check if this gives max(c₁, c₂).

For c₁ = c₂ = c:
```
aggregate₁(c, c) = 2c - c² - √(c²(1-c)²)
                 = 2c - c² - c(1-c)
                 = 2c - c² - c + c²
                 = c  ✓
```

For unequal confidences, it's more complex. Let's verify c₁=0.3, c₂=0.7:
```
σ = √(0.3 × 0.7 × 0.7 × 0.3) = √(0.0441) = 0.21
c₁ ⊕ c₂ = 0.3 + 0.7 - 0.21 = 0.79
aggregate₁ = 0.79 - 1 × 0.21 = 0.58
```

Hmm, this gives 0.58, not max(0.3, 0.7) = 0.7. Let me reconsider.

**Reanalysis**: For ρ=1 (perfectly correlated), both succeed or fail together. So:
```
P(at least one succeeds) = P(both succeed) = min(c₁, c₂)?
```

No, that's not quite right either. With perfect correlation, their joint success probability is constrained by the minimum marginal.

Actually, for Bernoulli random variables with perfect correlation (ρ=1), we have:
- If c₁ ≤ c₂: X₁=1 implies X₂=1, so P(X₁=1 ∧ X₂=1) = c₁
- P(at least one) = P(X₂=1) = c₂ (since X₁=1 only when X₂=1)

Wait, I need to be more careful. Perfect correlation ρ=1 means X₁ and X₂ are maximally positively related given their marginals.

For Bernoulli(c₁) and Bernoulli(c₂) with c₁ ≤ c₂:
- Perfect correlation means P(X₁=1, X₂=0) = 0 (if the more likely one fails, so does the less likely one)
- So P(X₁=1, X₂=1) = c₁
- P(X₁=0, X₂=1) = c₂ - c₁
- P(X₁=0, X₂=0) = 1 - c₂

Then:
```
P(at least one) = 1 - P(both=0) = 1 - (1 - c₂) = c₂ = max(c₁, c₂) ✓
```

So for ρ=1: aggregate(c₁, c₂) = max(c₁, c₂).

Let me re-derive the formula more carefully...

### 3.4 Corrected Derivation

For Bernoulli random variables X ~ Ber(p) and Y ~ Ber(q) with correlation ρ:

The joint distribution is determined by ρ and the marginals:
```
P(X=1, Y=1) = pq + ρ√(pq(1-p)(1-q))
P(X=1, Y=0) = p(1-q) - ρ√(pq(1-p)(1-q))
P(X=0, Y=1) = (1-p)q - ρ√(pq(1-p)(1-q))
P(X=0, Y=0) = (1-p)(1-q) + ρ√(pq(1-p)(1-q))
```

These must all be ≥ 0, which constrains valid ρ values given p,q.

```
P(X=1 ∨ Y=1) = 1 - P(X=0, Y=0)
             = 1 - [(1-p)(1-q) + ρσ]   where σ = √(pq(1-p)(1-q))
             = p + q - pq - ρσ
             = (p ⊕ q) - ρσ
```

Let's verify with p=q=c, ρ=1:
```
σ = √(c²(1-c)²) = c(1-c)
aggregate = 2c - c² - 1×c(1-c) = 2c - c² - c + c² = c ✓
```

And p=0.3, q=0.7, ρ=1:
```
σ = √(0.21 × 0.21) = 0.21
aggregate = (0.3 + 0.7 - 0.21) - 0.21 = 0.79 - 0.21 = 0.58
```

But we calculated max should give 0.7. What's wrong?

The issue is that ρ=1 is not achievable for all (p,q) pairs. The maximum achievable correlation is:
```
ρ_max = √(min(p,q) × min(1-p,1-q)) / √(pq(1-p)(1-q))
      = min(p,q) × min(1-p,1-q) / [pq(1-p)(1-q)]^{1/2}
```

For p=0.3, q=0.7:
```
σ = √(0.3 × 0.7 × 0.7 × 0.3) = 0.21
ρ_max for "same direction" = such that P(X=1,Y=0) ≥ 0
p(1-q) - ρσ ≥ 0
0.3 × 0.3 - ρ × 0.21 ≥ 0
ρ ≤ 0.09/0.21 ≈ 0.43
```

So ρ=1 is NOT achievable when p ≠ q! The maximal positive correlation is constrained.

**Key insight**: For Bernoulli variables with different marginals, perfect correlation (ρ=1) is impossible. The achievable range is [-ρ_min, ρ_max] where these depend on p,q.

### 3.5 Reformulating the Problem

Rather than using correlation coefficient ρ (which has constraints), let's use a **dependency parameter** δ ∈ [0,1]:

- δ = 0: fully independent → use ⊕
- δ = 1: fully dependent → use... what?

**Definition (Dependency-Adjusted Aggregation)**:
```
aggregate_δ(c₁, c₂) = (1-δ) × (c₁ ⊕ c₂) + δ × f(c₁, c₂)
```

where f is the aggregation for fully dependent sources.

**What is f?**

For fully dependent evidence from the same underlying source:
- It's really ONE piece of evidence, observed twice
- Combined confidence ≈ some measure of the single underlying source

Candidates for f:
1. **Max**: f(c₁,c₂) = max(c₁,c₂) — the stronger report dominates
2. **Average**: f(c₁,c₂) = (c₁+c₂)/2 — equally weight both observations
3. **Weighted average**: based on perceived reliability
4. **Root mean square**: √((c₁²+c₂²)/2) — rewards consensus

**Argument for max**: If sources are truly identical (same underlying truth), they should give the same confidence. Differences come from noise. The "true" confidence is likely the higher one (assuming low noise) or we're uncertain about which is correct.

**Argument for average**: If we're uncertain which source is more reliable, average is a safe default.

**I'll adopt a convention**: For fully dependent evidence, use **weighted average** with equal weights by default:
```
f(c₁, c₂) = (c₁ + c₂) / 2
```

This gives:
```
aggregate_δ(c₁, c₂) = (1-δ)(c₁ ⊕ c₂) + δ(c₁ + c₂)/2
```

### 3.6 Properties of Dependency-Adjusted Aggregation

**Theorem (Boundedness)**:
For c₁, c₂ ∈ [0,1] and δ ∈ [0,1]:
```
aggregate_δ(c₁, c₂) ∈ [0,1]
```

**Proof**:
- c₁ ⊕ c₂ ∈ [0,1] (proven Thread 8)
- (c₁ + c₂)/2 ∈ [0,1]
- Convex combination of [0,1] values is in [0,1]. ∎

**Theorem (Interpolation)**:
- aggregate₀(c₁, c₂) = c₁ ⊕ c₂ (independent case)
- aggregate₁(c₁, c₂) = (c₁ + c₂)/2 (fully dependent case)

**Theorem (Monotonicity in confidence)**:
For fixed δ:
```
c₁ ≤ c₁' ⟹ aggregate_δ(c₁, c₂) ≤ aggregate_δ(c₁', c₂)
```

**Proof**:
Both ⊕ and average are monotonic in each argument. ∎

**Theorem (Monotonicity in dependency)**:
For c₁ ⊕ c₂ ≥ (c₁+c₂)/2 (which holds when both > 0):
```
δ ≤ δ' ⟹ aggregate_δ(c₁, c₂) ≥ aggregate_{δ'}(c₁, c₂)
```

**Proof**:
```
aggregate_δ = (1-δ)(c₁⊕c₂) + δ·avg
d/dδ [aggregate] = -(c₁⊕c₂) + avg = avg - (c₁⊕c₂) ≤ 0
```
when c₁⊕c₂ ≥ avg. Since c₁⊕c₂ = c₁+c₂-c₁c₂ ≥ (c₁+c₂)/2 iff c₁+c₂ ≥ 2c₁c₂, which holds for c₁,c₂ ∈ [0,1]. ∎

**Corollary**: More dependency → less combined confidence (overcounting is reduced).

---

## 4. When to Use What

### 4.1 Decision Tree for Aggregation

```
Are evidence sources e₁, e₂ independent?
│
├── Yes → Use c₁ ⊕ c₂
│
├── No → How dependent are they?
│   │
│   ├── Fully dependent (δ=1)
│   │   └── Same source, same methodology
│   │   → Use (c₁ + c₂) / 2
│   │
│   ├── Partially dependent (0 < δ < 1)
│   │   └── Shared influences, overlapping methods
│   │   → Use aggregate_δ(c₁, c₂) = (1-δ)(c₁⊕c₂) + δ·avg
│   │
│   └── Unknown dependency
│       → Conservative: assume δ = 0.5 or δ = max plausible
│
└── Unknown → Ask or assume conservatively
```

### 4.2 Detecting Dependency

In CLAIR, how might we detect or represent evidence dependency?

**Explicit annotation** (metadata):
```clair
let e1 = evidence("Study A shows X", 0.8, source: pubmed_123)
let e2 = evidence("Study B shows X", 0.7, source: pubmed_456)
let shared_method = declares_dependency(e1, e2, reason: "same methodology")

aggregate [e1, e2] with dependency: 0.3
```

**Provenance-based detection**:
If e1.provenance and e2.provenance share ancestors in the DAG, they may be correlated.

```
If e1 justifies C and e2 justifies C:
  shared_ancestors = ancestors(e1) ∩ ancestors(e2)
  if shared_ancestors ≠ ∅:
    δ = estimate_dependency(shared_ancestors)
```

**Heuristic rules**:
- Same author → high dependency (δ ≥ 0.7)
- Same methodology → medium dependency (δ ≈ 0.5)
- Same time period → low dependency (δ ≈ 0.2)
- Same field/community → low dependency (δ ≈ 0.1-0.3)

### 4.3 Conservative Defaults

When dependency is unknown, CLAIR should be conservative:

**Option 1: Pessimistic assumption**
Assume moderate dependency (δ = 0.5) unless proven independent.

**Option 2: Sensitivity analysis**
Compute aggregate for range of δ values, report range:
```
confidence: 0.75 to 0.91 depending on evidence independence
```

**Option 3: Flag uncertainty**
```clair
let combined = aggregate [e1, e2] with dependency: unknown
// combined.meta.independence_assumed = true
// combined.confidence includes epistemic uncertainty about dependency
```

---

## 5. N-ary Correlated Aggregation

### 5.1 The General Case

For n evidence sources with dependency structure:

**Full independence**:
```
aggregate(c₁,...,cₙ) = 1 - ∏(1-cᵢ)
```

**Full dependence** (all from same source):
```
aggregate(c₁,...,cₙ) = (1/n) Σcᵢ  (simple average)
```

**Partial dependence**:
Requires a dependency matrix or structure.

### 5.2 Dependency Matrix Approach

Let D be an n×n dependency matrix where Dᵢⱼ = δᵢⱼ ∈ [0,1] is the dependency between eᵢ and eⱼ.

**Properties of D**:
- Symmetric: Dᵢⱼ = Dⱼᵢ
- Diagonal: Dᵢᵢ = 1 (self-dependency is complete)
- Transitivity: If Dᵢⱼ = 1 and Dⱼₖ = 1, then Dᵢₖ should be 1

**Effective sample size**:
Define the "effective number of independent sources":
```
n_eff = n / (1 + (n-1)·δ̄)
```
where δ̄ is the average off-diagonal dependency.

Example: n=10 sources with average pairwise dependency δ̄=0.5:
```
n_eff = 10 / (1 + 9×0.5) = 10 / 5.5 ≈ 1.8
```
So 10 partially correlated sources count as roughly 1.8 independent sources.

**Adjusted aggregation**:
Use n_eff in place of n for the aggregate formula.

### 5.3 Clustering Approach

**Idea**: Group highly correlated sources into clusters, aggregate within clusters, then aggregate across clusters.

```
Step 1: Cluster sources by dependency (δ > threshold → same cluster)
Step 2: Within each cluster, use average (fully dependent assumption)
Step 3: Across clusters, use ⊕ (independence assumption)
```

**Example**:
Sources: e₁, e₂, e₃, e₄, e₅
Clusters: {e₁, e₂}, {e₃}, {e₄, e₅}

```
c_cluster1 = (c₁ + c₂) / 2 = (0.8 + 0.7) / 2 = 0.75
c_cluster2 = c₃ = 0.6
c_cluster3 = (c₄ + c₅) / 2 = (0.5 + 0.6) / 2 = 0.55

c_final = c_cluster1 ⊕ c_cluster2 ⊕ c_cluster3
        = 1 - (1-0.75)(1-0.6)(1-0.55)
        = 1 - 0.25 × 0.4 × 0.45
        = 1 - 0.045
        = 0.955
```

Compare to naive (all independent):
```
c_naive = 1 - (0.2)(0.3)(0.4)(0.5)(0.4) = 1 - 0.0048 = 0.9952
```

The clustered approach gives lower (more conservative) confidence, appropriately accounting for correlation.

---

## 6. Integration with CLAIR DAG

### 6.1 Extending the Aggregate Node

From Thread 2's proposal, extend the aggregate constructor:

```lean
inductive CombinationRule where
  | independent              -- Use ⊕
  | dependent                -- Use average
  | correlated : DependencyModel → CombinationRule

structure DependencyModel where
  pairwise : Option (Array (Nat × Nat × Float))  -- Explicit (i,j,δᵢⱼ) triples
  uniform : Option Float                          -- All pairs have same δ
  clusters : Option (Array (Array Nat))           -- Cluster indices
```

### 6.2 Confidence Computation

```lean
def aggregateConfidence (confs : Array Confidence) (rule : CombinationRule) : Confidence :=
  match rule with
  | .independent => probOr confs  -- 1 - ∏(1-cᵢ)
  | .dependent => average confs    -- (Σcᵢ)/n
  | .correlated model =>
      match model.uniform with
      | some δ => interpolate (probOr confs) (average confs) δ
      | none => clusterAggregate confs model
```

### 6.3 Provenance-Based Dependency Detection

```lean
def estimateDependency (j1 j2 : JustificationRef) (graph : JustificationGraph) : Float :=
  let ancestors1 := graph.ancestors j1
  let ancestors2 := graph.ancestors j2
  let shared := ancestors1 ∩ ancestors2
  let total := ancestors1 ∪ ancestors2
  if total.isEmpty then 0.0  -- No shared ancestry → independent
  else (shared.size.toFloat / total.size.toFloat)  -- Jaccard-like similarity
```

---

## 7. What I Don't Know

### 7.1 Theoretical Gaps

1. **Optimal δ estimation**: Given provenance overlap, what's the right dependency estimate? The Jaccard formula above is a heuristic.

2. **Negative correlation**: When might evidence be negatively correlated (one failing increases chance the other succeeds)? How to model this?

3. **Transitive dependency**: If A depends on B and B depends on C, what's the A-C dependency? Is dependency transitive? (Probably not strictly.)

4. **Dependency vs. redundancy**: Correlated evidence provides less NEW information. How to quantify "information gain" from additional evidence?

5. **Calibration with correlation**: If individual confidences are calibrated, is the correlated aggregate calibrated?

### 7.2 Design Questions

1. **Default behavior**: Should CLAIR assume independence (optimistic) or moderate dependency (conservative) by default?

2. **Annotation burden**: Requiring explicit dependency annotations is burdensome. Can we infer it automatically from provenance?

3. **Sensitivity reporting**: Should CLAIR report confidence ranges based on independence uncertainty?

4. **Dependency types**: Are there semantically distinct types of dependency (methodological, social, causal) that should be handled differently?

### 7.3 Connections to Other Threads

1. **Thread 5 (Belief Revision)**: How does correlation affect belief revision? If we retract one correlated evidence, do the others become more/less valuable?

2. **Thread 6 (Multi-Agent)**: Agent beliefs may be correlated (shared training, common sources). How to aggregate across agents?

3. **Thread 8 (Formalization)**: Can we formalize dependency-adjusted aggregation in Lean?

---

## 8. Conclusions

### 8.1 Core Answers

**How does aggregation handle correlated evidence?**

The ⊕ formula assumes independence. For correlated evidence, we need a dependency-adjusted aggregation:

```
aggregate_δ(c₁, c₂) = (1-δ)(c₁ ⊕ c₂) + δ(c₁ + c₂)/2
```

where δ ∈ [0,1] is the dependency parameter:
- δ = 0: independent (use ⊕)
- δ = 1: fully dependent (use average)
- 0 < δ < 1: interpolate

**What happens if we incorrectly treat correlated evidence as independent?**

Overcounting. The aggregate confidence will be higher than warranted, leading to overconfidence and poor calibration.

### 8.2 Key Insights

1. **Independence is the optimistic assumption** — treating correlated sources as independent always yields higher confidence than appropriate.

2. **Average is the conservative extreme** — for fully dependent sources, averaging (not ⊕) is appropriate.

3. **Dependency can sometimes be inferred from provenance** — shared ancestors in the justification DAG suggest correlation.

4. **N-ary aggregation is harder** — full dependency structure requires a matrix or clustering approach.

5. **Conservative defaults are safer** — when dependency is unknown, assuming some correlation is more robust than assuming independence.

### 8.3 Design Recommendations for CLAIR

1. **Extend CombinationRule** to include correlation options:
   - `independent`: use ⊕
   - `dependent`: use average
   - `correlated δ`: interpolate

2. **Add dependency inference** based on provenance overlap in the DAG.

3. **Warn on possible overcounting** when aggregating sources with shared provenance ancestry without explicit dependency annotation.

4. **Report confidence ranges** when dependency is uncertain:
   ```
   confidence: 0.75 [0.68 if dependent, 0.91 if independent]
   ```

5. **Default to moderate caution**: If no dependency information, assume δ = 0.3 rather than 0.

### 8.4 Task Status

**Task 2.13: SUBSTANTIALLY EXPLORED**

What's settled:
- Correlation reduces effective sample size
- Interpolation formula aggregate_δ = (1-δ)(c₁⊕c₂) + δ·avg
- Properties verified (boundedness, monotonicity)
- Integration with DAG structure sketched

What remains:
- Optimal δ estimation from provenance
- Handling negative correlation (rare but possible)
- Formal verification in Lean
- Empirical validation of heuristics

### 8.5 Prior Art Summary

| Approach | Key Insight | CLAIR Application |
|----------|-------------|-------------------|
| Copula theory | Dependency structure separate from marginals | Could model joint distributions |
| Subjective Logic | Averaging fusion for dependent sources | Inspires δ=1 → average |
| D-S cautious rule | Idempotent combination for unknown dependency | Conservative default |
| Meta-analysis | Adjust weights for study correlation | Effective sample size |
| Legal corroboration | Independence must be established | Don't assume independence |

---

## 9. References

### Primary Sources

- **Jøsang, A.** (2016). *Subjective Logic*. Springer.
  - Chapter 12: Fusion of dependent opinions

- **Nelsen, R.B.** (2006). *An Introduction to Copulas*. Springer.
  - Formal treatment of dependency structures

- **Klement, E.P., Mesiar, R., Pap, E.** (2000). *Triangular Norms*. Springer.
  - T-norms and t-conorms for aggregation

### Secondary Sources

- **Smets, P.** (1993). "Belief Functions: The Disjunctive Rule of Combination and the Generalized Bayesian Theorem." *IJAR*.
  - Cautious combination rule

- **Borenstein, M., et al.** (2009). *Introduction to Meta-Analysis*. Wiley.
  - Handling dependent studies

- **Good, I.J.** (1950). *Probability and the Weighing of Evidence*. Griffin.
  - Classical treatment of evidence combination

### Online Resources

- [Wikipedia: Copula (probability theory)](https://en.wikipedia.org/wiki/Copula_(probability_theory))
- [Stanford Encyclopedia: Evidence](https://plato.stanford.edu/entries/evidence/)

---

*Thread 2.13 Status: Substantially explored. Dependency-adjusted aggregation formula derived: aggregate_δ = (1-δ)(c₁⊕c₂) + δ·avg. Properties verified. Integration with DAG sketched. Conservative defaults recommended when dependency unknown. Ready for Lean formalization.*
