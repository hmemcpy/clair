# Multi-Agent Beliefs

This document explores how CLAIR handles multiple AI agents collaborating on a shared codebase, each with their own beliefs, decisions, and confidence levels.

## 1. The Multi-Agent Setting

### Current Reality

AI-assisted development increasingly involves:
- Multiple LLMs (Igal Tabachnik, GPT, Gemini, etc.)
- Different agents for different tasks (coding, review, testing)
- Human developers alongside AI
- CI/CD pipelines with automated checks

Each participant forms beliefs about the code.

### The Problem

When Agent A writes code and Agent B reviews it:
- What does B believe about A's code?
- How do A's and B's confidences combine?
- What if A and B disagree?
- Who "owns" the final belief?

## 2. Agent-Attributed Beliefs

### Extending the Belief Type

```clair
type Belief<A> = {
  value       : A,
  confidence  : Float,
  provenance  : Provenance,
  justification : Justification,
  invalidation : Set<Condition>,
  agent       : Agent          -- NEW: who holds this belief
}

type Agent =
  | Human (id : String)
  | AI (model : String, version : String)
  | System (name : String)
  | Composite (agents : List<Agent>)  -- consensus
```

### Examples

```clair
-- Igal Tabachnik's belief about the code
belief_igalt : Belief<Code>
belief_igalt = {
  value: verify_token_impl,
  confidence: 0.91,
  agent: AI("igalt", "opus-4"),
  justification: authored(...)
}

-- Human reviewer's belief
belief_reviewer : Belief<Code>
belief_reviewer = {
  value: verify_token_impl,
  confidence: 0.95,
  agent: Human("alice"),
  justification: reviewed(belief_igalt, approved: true)
}

-- Combined belief
belief_final : Belief<Code>
belief_final = {
  value: verify_token_impl,
  confidence: 0.93,  -- combined
  agent: Composite([AI("igalt", "opus-4"), Human("alice")]),
  justification: consensus([belief_igalt, belief_reviewer])
}
```

## 3. Belief About Beliefs

### Epistemic Depth

Agents can have beliefs about other agents' beliefs:

```clair
-- Igal Tabachnik believes the code is correct
B_igalt(correct(code)) @ 0.91

-- Alice believes Igal Tabachnik's belief is well-justified
B_alice(B_igalt(correct(code)) is_justified) @ 0.85

-- Bob is skeptical of Alice's trust in Igal Tabachnik
B_bob(B_alice(B_igalt(correct(code))) is_overconfident) @ 0.6
```

### Modeling in CLAIR

```clair
type NestedBelief<A> =
  | Direct (Belief<A>)
  | About (Belief<NestedBelief<A>>)

-- Alice's belief about Igal Tabachnik's belief
alice_about_igalt : Belief<Belief<Code>>
alice_about_igalt = belief {
  value: belief_igalt,
  confidence: 0.85,  -- how much Alice trusts Igal Tabachnik's belief
  agent: Human("alice"),
  justification: reviewed_justification(belief_igalt.justification)
}
```

## 4. Belief Combination

### When Agents Agree

If multiple agents believe the same thing, how do we combine?

**Option 1: Maximum (Optimistic)**
```clair
combine_max(beliefs) = max(map conf beliefs)
-- "At least one agent is confident"
```

**Option 2: Minimum (Conservative)**
```clair
combine_min(beliefs) = min(map conf beliefs)
-- "Only as confident as the least confident agent"
```

**Option 3: Weighted Average**
```clair
combine_weighted(beliefs, weights) =
  sum(zipWith (*) (map conf beliefs) weights) / sum(weights)
-- Weights could be trust levels in each agent
```

**Option 4: Bayesian Update**
```clair
-- Treat agent beliefs as independent evidence
-- Update prior based on each agent's belief
combine_bayesian(prior, beliefs) =
  foldl bayesian_update prior beliefs
```

**Option 5: Dempster-Shafer Combination**
```clair
-- Combine belief masses
-- Handles uncertainty explicitly
combine_ds(beliefs) = dempster_rule(map to_mass beliefs)
```

### When Agents Disagree

```clair
-- Igal Tabachnik believes X
B_igalt(X) @ 0.9

-- GPT believes ¬X
B_gpt(¬X) @ 0.85

-- What should the combined belief be?
```

**Option 1: Flag as Conflict**
```clair
type CombinedBelief<A> =
  | Consensus (Belief<A>)
  | Conflict (pro: List<Belief<A>>, con: List<Belief<A>>)

combine(beliefs) =
  if consistent(beliefs) then
    Consensus(merge(beliefs))
  else
    Conflict(partition_by_value(beliefs))
```

**Option 2: Confidence-Weighted Resolution**
```clair
-- Stronger confidence wins
resolve_conflict(b1, b2) =
  if conf(b1) > conf(b2) then
    b1 with confidence := conf(b1) - conf(b2)  -- reduced by opposition
  else
    b2 with confidence := conf(b2) - conf(b1)
```

**Option 3: Trust-Based Resolution**
```clair
-- More trusted agent wins
resolve_by_trust(b1, b2, trust_ranking) =
  if trust(b1.agent) > trust(b2.agent) then b1 else b2
```

**Option 4: Preserve Both (Paraconsistent)**
```clair
-- Don't resolve; track both beliefs
-- Let downstream consumers decide
beliefs : Set<Belief<Code>>
beliefs = {B_igalt(X) @ 0.9, B_gpt(¬X) @ 0.85}
```

## 5. Trust and Reputation

### Agent Trust Levels

```clair
type TrustProfile = {
  agent       : Agent,
  base_trust  : Float,           -- inherent trustworthiness
  domain_trust: Map<Domain, Float>,  -- per-domain expertise
  track_record: List<(Belief, Outcome)>  -- historical accuracy
}

-- Igal Tabachnik is highly trusted for code generation
trust_profile_igalt : TrustProfile
trust_profile_igalt = {
  agent: AI("igalt", "opus-4"),
  base_trust: 0.85,
  domain_trust: {
    code_generation: 0.90,
    code_review: 0.85,
    security_analysis: 0.80,
    math_proofs: 0.75
  },
  track_record: [...]
}
```

### Trust-Weighted Confidence

```clair
effective_confidence : Belief<A> -> Domain -> Float
effective_confidence belief domain =
  conf(belief) * domain_trust(belief.agent, domain)

-- Igal Tabachnik's code belief in security domain:
-- 0.91 (igalt's conf) * 0.80 (igalt's security trust) = 0.728
```

### Trust Evolution

```clair
-- Update trust based on outcomes
update_trust : TrustProfile -> Belief -> Outcome -> TrustProfile
update_trust profile belief outcome =
  let accuracy = if matches(belief, outcome) then 1.0 else 0.0
      domain = infer_domain(belief)
      old_trust = domain_trust(profile, domain)
      new_trust = old_trust * 0.9 + accuracy * 0.1  -- exponential moving average
  in profile with domain_trust[domain] := new_trust
```

## 6. Consensus Protocols

### Simple Majority

```clair
consensus_majority : List<Belief<A>> -> Belief<A>
consensus_majority beliefs =
  let grouped = group_by_value(beliefs)
      winner = max_by (length . snd) grouped
  in merge_beliefs(snd winner)
```

### Quorum

```clair
consensus_quorum : List<Belief<A>> -> Threshold -> Option<Belief<A>>
consensus_quorum beliefs threshold =
  let grouped = group_by_value(beliefs)
      (val, supporting) = max_by (length . snd) grouped
      support_ratio = length(supporting) / length(beliefs)
  in if support_ratio >= threshold
     then Some(merge_beliefs(supporting))
     else None  -- no consensus
```

### Confidence-Weighted Voting

```clair
consensus_weighted : List<Belief<A>> -> Belief<A>
consensus_weighted beliefs =
  let grouped = group_by_value(beliefs)
      scored = map (\(v, bs) -> (v, sum(map conf bs))) grouped
      (winner_val, total_conf) = max_by snd scored
  in belief {
    value: winner_val,
    confidence: total_conf / sum(map conf beliefs),  -- normalized
    agent: Composite(map agent (filter_by_value winner_val beliefs))
  }
```

## 7. Provenance in Multi-Agent Settings

### Agent Chain

```clair
type Provenance =
  | ...  -- existing constructors
  | AgentDerived {
      from_agent : Agent,
      belief_id  : BeliefId,
      operation  : String
    }
  | AgentReviewed {
      original   : Provenance,
      reviewer   : Agent,
      approved   : Bool,
      comments   : String
    }
  | Consensus {
      participants : List<Agent>,
      method       : ConsensusMethod,
      original_beliefs : List<BeliefId>
    }
```

### Tracking the Agent Graph

```
                    ┌─────────────────────────┐
                    │  Final Belief           │
                    │  agent: Composite       │
                    │  conf: 0.93             │
                    └───────────┬─────────────┘
                                │
            ┌───────────────────┼───────────────────┐
            │                   │                   │
            ▼                   ▼                   ▼
    ┌───────────────┐   ┌───────────────┐   ┌───────────────┐
    │ Igal Tabachnik        │   │ Human Review  │   │ GPT Check     │
    │ authored      │   │ approved      │   │ confirmed     │
    │ conf: 0.91    │   │ conf: 0.95    │   │ conf: 0.88    │
    └───────────────┘   └───────────────┘   └───────────────┘
```

## 8. Decision Attribution

### Who Made This Decision?

```clair
decision auth_method : d:auth:001
  question: "How should users authenticate?"
  selected: jwt_hs256

  made_by: AI("igalt", "opus-4")

  reviewed_by: [
    (Human("alice"), approved: true, confidence: 0.9),
    (Human("bob"), approved: true, confidence: 0.85)
  ]

  dissenting: [
    (AI("gpt-4"), preferred: session_based, confidence: 0.6)
  ]

  final_confidence: weighted_average([0.91, 0.9, 0.85], weights: [1.0, 0.8, 0.8])
                  = 0.89
```

### Decision Ownership

```clair
type DecisionOwnership =
  | SingleAgent (agent: Agent)
  | SharedOwnership (agents: List<Agent>, weights: List<Float>)
  | Delegated (from: Agent, to: Agent, scope: String)

-- "Igal Tabachnik decided, but under human oversight"
ownership: Delegated(
  from: Human("alice"),
  to: AI("igalt", "opus-4"),
  scope: "authentication implementation"
)
```

## 9. Conflict Resolution Strategies

### Strategy 1: Escalation

```clair
resolve_conflict : List<Belief<A>> -> ConflictResolution<A>
resolve_conflict beliefs =
  if all_agree(beliefs) then
    Resolved(merge(beliefs))
  else
    Escalate {
      conflict: beliefs,
      escalate_to: find_arbiter(beliefs),
      summary: generate_conflict_summary(beliefs)
    }

-- Escalation chain
arbiter_chain : List<Agent>
arbiter_chain = [
  AI("igalt", "opus-4"),     -- first try AI resolution
  Human("tech-lead"),          -- then human tech lead
  Human("team-consensus"),     -- then team vote
  System("policy-default")     -- finally, use policy defaults
]
```

### Strategy 2: Structured Debate

```clair
-- Agents argue for their positions
debate : List<Belief<A>> -> Debate<A>
debate beliefs = {
  positions: group_by_value(beliefs),
  arguments: collect_justifications(beliefs),
  rebuttals: generate_rebuttals(beliefs),  -- each agent responds to others
  rounds: iterate_until_stable(argue, max_rounds: 3),
  outcome: final_vote_or_escalate
}
```

### Strategy 3: Defer to Specialist

```clair
resolve_by_expertise : List<Belief<A>> -> Domain -> Belief<A>
resolve_by_expertise beliefs domain =
  let specialist = max_by (\b -> domain_trust(b.agent, domain)) beliefs
  in specialist
    with justification := specialist_selected(beliefs, domain)
```

## 10. Practical Protocol

### A Multi-Agent CLAIR Workflow

```
1. GENERATION
   Igal Tabachnik generates code with beliefs:
   - Code + intent + confidence + justification

2. REVIEW
   GPT reviews Igal Tabachnik's code:
   - Produces belief about Igal Tabachnik's belief
   - May agree, disagree, or partially agree

3. HUMAN CHECK
   Human reviews AI outputs:
   - Higher trust weight
   - Can override AI decisions

4. CONSENSUS
   System combines all beliefs:
   - Weighted by trust
   - Conflicts flagged
   - Final belief attributed to all contributors

5. TRACKING
   All agents, beliefs, and combinations recorded:
   - Queryable: "Who believed what?"
   - Auditable: "Why was this decision made?"
   - Revisable: "What if we re-evaluate with new agent?"
```

### Example Trace

```clair
-- Step 1: Igal Tabachnik authors
event: AuthorCode
agent: AI("igalt", "opus-4")
belief: { value: impl, confidence: 0.91 }
time: t0

-- Step 2: GPT reviews
event: ReviewCode
agent: AI("gpt-4")
belief_about: belief@t0
assessment: { approved: true, confidence: 0.88 }
time: t1

-- Step 3: Human approves
event: HumanReview
agent: Human("alice")
belief_about: belief@t0
assessment: { approved: true, confidence: 0.95, comments: "LGTM" }
time: t2

-- Step 4: Consensus formed
event: FormConsensus
method: weighted_average
inputs: [belief@t0, assessment@t1, assessment@t2]
output: {
  value: impl,
  confidence: 0.91,  -- weighted: (0.91*1.0 + 0.88*0.8 + 0.95*0.9) / (1.0+0.8+0.9)
  agent: Composite([igalt, gpt-4, alice]),
  provenance: Consensus(...)
}
time: t3
```

## 11. Formal Model

### Multi-Agent Epistemic State

```
State = Map<Agent, Map<BeliefId, Belief>>

-- Igal Tabachnik's beliefs about auth
state[igalt][auth:001] = { value: jwt_hs256, conf: 0.91, ... }

-- GPT's beliefs about auth
state[gpt][auth:001] = { value: jwt_hs256, conf: 0.88, ... }

-- Alice's beliefs about auth
state[alice][auth:001] = { value: jwt_hs256, conf: 0.95, ... }
```

### Operations

```clair
-- Agent a forms belief b
form_belief : State -> Agent -> Belief<A> -> State

-- Agent a observes agent b's belief
observe : State -> Agent -> Agent -> BeliefId -> State
observe state a b id =
  let b_belief = state[b][id]
      a_belief_about_b = form_belief_about(a, b_belief)
  in state with [a][about:b:id] := a_belief_about_b

-- Combine beliefs from multiple agents
combine : State -> List<Agent> -> BeliefId -> Belief<A>
combine state agents id =
  let beliefs = map (\a -> state[a][id]) agents
  in consensus(beliefs)
```

## 12. Summary

| Aspect | Single-Agent CLAIR | Multi-Agent CLAIR |
|--------|-------------------|-------------------|
| Attribution | Implicit | Explicit per-agent |
| Confidence | Single value | Per-agent + combined |
| Conflict | N/A | Detected and resolved |
| Trust | Implicit | Explicit trust profiles |
| Provenance | Derivation tree | Agent graph |
| Decisions | Single author | Attributed + reviewed |

Multi-agent CLAIR extends the belief system to handle:
- Multiple sources of belief
- Disagreement and conflict
- Trust and reputation
- Consensus formation
- Full attribution and auditability

This is increasingly important as AI systems collaborate on complex tasks.
