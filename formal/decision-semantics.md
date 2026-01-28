# Decision Semantics

This document formalizes how decisions work in CLAIR—the mechanism for choosing among alternatives while preserving rationale.

## 1. What Is a Decision?

In traditional programming, when multiple valid approaches exist, one is chosen and the alternatives disappear:

```python
# Why JWT? Why not sessions? Why HS256 not RS256?
# This information is lost.
def authenticate(token):
    return verify_jwt_hs256(token)
```

In CLAIR, a **decision** is a first-class construct that:
- Records all options considered
- Captures the criteria used to select
- Preserves the rationale
- Tracks conditions for revisiting

## 2. Formal Definition

### Decision Structure

```
Decision<τ> = {
  id          : DecisionId,
  question    : String,                    -- what are we deciding?
  options     : List<Option<τ>>,           -- alternatives considered
  constraints : List<Constraint>,          -- hard requirements
  criteria    : List<Criterion>,           -- soft preferences
  selected    : Option<τ>,                 -- the choice
  rationale   : String,                    -- why this choice
  confidence  : [0,1],                     -- confidence in choice
  revisit_if  : List<Condition>            -- when to reconsider
}

Option<τ> = {
  id          : OptionId,
  value       : τ,                         -- the actual value/approach
  description : String,
  satisfies   : List<ConstraintId>,        -- which constraints it meets
  scores      : Map<CriterionId, Score>,   -- how it scores on criteria
  status      : Selected | Rejected | Viable
  rejection   : Option<String>             -- why rejected (if rejected)
}

Constraint = {
  id          : ConstraintId,
  description : String,
  predicate   : τ → Bool,                  -- hard requirement
  source      : Provenance                 -- where this constraint came from
}

Criterion = {
  id          : CriterionId,
  description : String,
  weight      : [0,1],                     -- importance
  scorer      : τ → Score                  -- how to evaluate
}
```

## 3. Decision Semantics

### Making a Decision

```
decide<τ>(
  question: String,
  options: List<Option<τ>>,
  constraints: List<Constraint>,
  criteria: List<Criterion>
) → Belief<τ>
```

**Step 1: Filter by constraints**
```
viable = options.filter(opt =>
  constraints.all(c => c.predicate(opt.value)))
```

**Step 2: Score by criteria**
```
scored = viable.map(opt => {
  opt with scores = criteria.map(c =>
    (c.id, c.weight * c.scorer(opt.value)))
})
```

**Step 3: Select best**
```
selected = scored.maxBy(opt => sum(opt.scores.values))
```

**Step 4: Compute confidence**
```
-- Confidence based on how much the winner dominates alternatives
margin = score(selected) - score(secondBest)
confidence = sigmoid(margin / threshold)
```

**Step 5: Construct belief**
```
Belief<τ> = {
  value: selected.value,
  confidence: confidence,
  provenance: decided(decision_id),
  justification: choice(options, criteria, rationale),
  invalidation: revisit_conditions
}
```

## 4. Decision Typing

```
─────────────────────────────────────────────────────────────────── [T-Decide]
Γ ⊢ options : List<Option<τ>>
Γ ⊢ constraints : List<Constraint>
Γ ⊢ criteria : List<Criterion>
viable(options, constraints) ≠ ∅
──────────────────────────────────────────────────────────────────────────────
Γ ⊢ decide(question, options, constraints, criteria) : Belief<τ>
```

The decision is well-typed if:
1. Options are of compatible type
2. At least one option satisfies all constraints
3. (Optionally) criteria are applicable to the type

## 5. Decision Confidence

Confidence in a decision reflects:

1. **Dominance**: How much better is the selected option?
2. **Constraint satisfaction**: Are all constraints clearly met?
3. **Coverage**: Were relevant alternatives considered?
4. **Stability**: Would small changes alter the decision?

### Confidence Formula

```
conf(decision) = dominance · satisfaction · coverage · stability

where:
  dominance = score(selected) / score(secondBest)  -- clamped to [0,1]
  satisfaction = min(margin by which constraints are satisfied)
  coverage = |considered| / |reasonable alternatives|
  stability = 1 - sensitivity to criterion weight changes
```

### Low Confidence Signals

```
if conf(decision) < threshold:
  flag for human review
  record: "Decision confidence is low because: ..."
```

## 6. Revisitation Conditions

A decision should be revisited when:

### Constraint Changes
```
revisit_if constraint_added(c) where ¬selected.satisfies(c)
revisit_if constraint_removed(c) where rejected_option.failed_only(c)
```

### Criteria Changes
```
revisit_if criterion_weight_changed(c, Δ) where Δ > threshold
revisit_if criterion_added(c) where secondBest.scores_better(c)
```

### New Options
```
revisit_if option_discovered(opt) where
  viable(opt) ∧ score(opt) > score(selected)
```

### Assumption Invalidation
```
revisit_if assumption_invalidated(a) where
  selected.depends_on(a)
```

## 7. Decision Composition

Decisions can depend on other decisions:

```
decision db_choice:
  question: "Which database?"
  selected: postgresql

decision orm_choice:
  question: "Which ORM?"
  depends_on: db_choice
  options:
    - sqlalchemy (if db_choice = postgresql)
    - prisma (if db_choice = postgresql or mysql)
  selected: sqlalchemy
  revisit_if: db_choice.changed
```

### Dependency Graph

```
         ┌─────────────┐
         │ db_choice   │
         └──────┬──────┘
                │
    ┌───────────┼───────────┐
    │           │           │
    ▼           ▼           ▼
┌────────┐ ┌────────┐ ┌────────┐
│orm     │ │caching │ │backup  │
│choice  │ │choice  │ │choice  │
└────────┘ └────────┘ └────────┘
```

When `db_choice` is revisited, all dependent decisions are flagged.

## 8. Decision Records

A decision record is the serializable form:

```yaml
decision:
  id: d:auth:001
  timestamp: 2024-01-15T10:30:00Z
  question: "How should users authenticate?"

  constraints:
    - id: c1
      description: "Must be stateless"
      source: requirements.md:L42
    - id: c2
      description: "Must handle token expiry"
      source: security_review

  criteria:
    - id: cr1
      description: "Implementation simplicity"
      weight: 0.6
    - id: cr2
      description: "Security strength"
      weight: 0.9

  options:
    - id: opt1
      value: jwt_hs256
      satisfies: [c1, c2]
      scores: {cr1: 0.8, cr2: 0.7}
      status: selected

    - id: opt2
      value: jwt_rs256
      satisfies: [c1, c2]
      scores: {cr1: 0.5, cr2: 0.9}
      status: viable
      rejection: "Unnecessary complexity for single-service"

    - id: opt3
      value: session_based
      satisfies: [c2]
      scores: {cr1: 0.9, cr2: 0.6}
      status: rejected
      rejection: "Violates stateless constraint (c1)"

  selected: opt1
  rationale: >
    JWT with HS256 selected. Satisfies all constraints.
    RS256 would provide stronger security but adds complexity
    unnecessary for single-service deployment.

  confidence: 0.87

  revisit_if:
    - multi_service_deployment
    - security_requirements_increase
    - constraint_added(asymmetric_trust)

  assumptions:
    - id: a1
      description: "Single service verifies tokens"
      status: active
    - id: a2
      description: "Shared secret is secure"
      status: active
```

## 9. Querying Decisions

```
-- Why was this option selected?
query(d:auth:001, "why selected?")
→ "JWT with HS256 selected because:
    - Satisfies all constraints (stateless, handles expiry)
    - Simpler than RS256 (scored 0.8 vs 0.5 on simplicity)
    - Single-service assumption makes shared secret acceptable"

-- What alternatives were considered?
query(d:auth:001, "alternatives?")
→ [jwt_rs256 (viable, not selected: complexity),
   session_based (rejected: violates stateless)]

-- What would change this decision?
query(d:auth:001, "revisit conditions?")
→ [multi_service_deployment,
   security_requirements_increase,
   new constraint requiring asymmetric trust]

-- What depends on this decision?
query(d:auth:001, "dependents?")
→ [d:auth:002 (token_format),
   d:auth:003 (key_rotation)]
```

## 10. Decision Diff

When code changes, compare decisions:

```
diff(d:auth:001@v1, d:auth:001@v2):

  UNCHANGED:
    - question
    - constraints [c1, c2]

  CHANGED:
    - criteria:
        + cr3: "Multi-service support" (weight: 0.8)
    - selected:
        - jwt_hs256
        + jwt_rs256
    - rationale:
        - "Single-service assumption"
        + "Now deploying to multiple services"
    - confidence:
        0.87 → 0.82

  INVALIDATED ASSUMPTIONS:
    - a1: "Single service verifies tokens" → FALSE
```

## 11. Relationship to TMS

Decisions in CLAIR are related to TMS as follows:

| TMS Concept | CLAIR Decision |
|-------------|----------------|
| Node | Option |
| Justification | Rationale + Criteria |
| IN/OUT | Selected/Rejected |
| Assumption | Assumption with status |
| Dependency | revisit_if |

Key difference: TMS maintains consistency automatically. CLAIR flags for review but doesn't automatically switch decisions (that would be surprising).

## 12. Implementation Sketch

```python
@dataclass
class Decision(Generic[T]):
    id: DecisionId
    question: str
    options: List[Option[T]]
    constraints: List[Constraint]
    criteria: List[Criterion]
    selected: Option[T]
    rationale: str
    confidence: float
    revisit_if: List[Condition]
    assumptions: List[Assumption]

    def to_belief(self) -> Belief[T]:
        return Belief(
            value=self.selected.value,
            confidence=self.confidence,
            provenance=Provenance.decided(self.id),
            justification=Justification.choice(
                options=self.options,
                criteria=self.criteria,
                rationale=self.rationale
            ),
            invalidation=self.revisit_if
        )

    def check_invalidation(self, world: WorldState) -> List[str]:
        """Check if any revisit conditions are triggered."""
        triggered = []
        for cond in self.revisit_if:
            if cond.evaluate(world):
                triggered.append(cond.description)
        for assumption in self.assumptions:
            if not assumption.holds(world):
                triggered.append(f"Assumption violated: {assumption.description}")
        return triggered
```
