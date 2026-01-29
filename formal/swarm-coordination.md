# Swarm Coordination in CLAIR

This document explores how multiple CLAIR agents coordinate, handle disagreement, and reach consensus.

## 1. What is a Belief Swarm?

### Definition

A **belief swarm** is a set of agents working on shared beliefs:

```clair
type Swarm = {
  agents      : Set<Agent>,
  shared_beliefs : Map<BeliefId, List<AgentBelief>>,
  coordination : CoordinationProtocol,
  consensus    : ConsensusRule
}

type AgentBelief = {
  agent  : Agent,
  belief : Belief<Any>,
  time   : Timestamp
}
```

### Properties of Swarms

1. **No central authority** — agents are peers (or have explicit hierarchy)
2. **Partial views** — each agent may see different information
3. **Asynchronous** — agents operate at different speeds
4. **Potentially conflicting** — agents may disagree

## 2. Disagreement Types

### Type 1: Value Disagreement

Agents believe different values for the same thing:

```clair
-- Claude believes the function should use HS256
B_claude(auth_algorithm = HS256) @ 0.91

-- GPT believes it should use RS256
B_gpt(auth_algorithm = RS256) @ 0.87
```

### Type 2: Confidence Disagreement

Agents agree on value but disagree on confidence:

```clair
-- Both believe the code is correct, but...
B_claude(code_correct) @ 0.95  -- Claude is very confident
B_gpt(code_correct) @ 0.60     -- GPT is less sure
```

### Type 3: Justification Disagreement

Agents agree on value and confidence, but for different reasons:

```clair
B_claude(use_jwt) @ 0.9
  justification: "stateless requirement"

B_gpt(use_jwt) @ 0.9
  justification: "industry standard practice"
```

### Type 4: Scope Disagreement

Agents disagree about what the question even is:

```clair
B_claude(need_authentication) @ 0.95
  scope: "API endpoints"

B_gpt(need_authentication) @ 0.30
  scope: "internal services"  -- different interpretation!
```

## 3. Consensus Mechanisms

### 3.1 Voting-Based Consensus

**Simple Majority**
```clair
majority : List<AgentBelief<A>> -> Option<A>
majority beliefs =
  let votes = group_by val beliefs
      counts = map (\(v, bs) -> (v, length bs)) votes
      (winner, count) = maximum_by snd counts
  in if count > length beliefs / 2
     then Some winner
     else None  -- no majority
```

**Supermajority (2/3)**
```clair
supermajority : List<AgentBelief<A>> -> Option<A>
supermajority beliefs =
  let votes = group_by val beliefs
      counts = map (\(v, bs) -> (v, length bs)) votes
      (winner, count) = maximum_by snd counts
  in if count >= (2 * length beliefs) / 3
     then Some winner
     else None
```

**Confidence-Weighted Voting**
```clair
weighted_vote : List<AgentBelief<A>> -> A
weighted_vote beliefs =
  let votes = group_by val beliefs
      scores = map (\(v, bs) -> (v, sum (map conf bs))) votes
  in fst (maximum_by snd scores)
```

### 3.2 Trust-Based Consensus

```clair
type TrustNetwork = Map<(Agent, Agent), Float>
-- trust[a][b] = how much agent a trusts agent b

trust_weighted : TrustNetwork -> Agent -> List<AgentBelief<A>> -> A
trust_weighted network observer beliefs =
  let weighted = map (\ab -> (val ab.belief,
                              conf ab.belief * network[observer][ab.agent]))
                     beliefs
      scores = group_and_sum weighted
  in fst (maximum_by snd scores)
```

### 3.3 Bayesian Consensus

Treat each agent's belief as evidence:

```clair
bayesian_consensus : Prior<A> -> List<AgentBelief<A>> -> Posterior<A>
bayesian_consensus prior beliefs =
  foldl bayesian_update prior (map to_evidence beliefs)

-- Each agent contributes evidence weighted by their reliability
to_evidence : AgentBelief<A> -> Evidence<A>
to_evidence ab = Evidence {
  value: val ab.belief,
  strength: conf ab.belief * reliability(ab.agent)
}
```

### 3.4 Dempster-Shafer Consensus

Handles uncertainty explicitly:

```clair
type MassFunction<A> = Map<Set<A>, Float>
-- m({a,b}) = 0.3 means "30% belief that it's either a or b"

dempster_combine : MassFunction<A> -> MassFunction<A> -> MassFunction<A>
dempster_combine m1 m2 =
  let raw = { (X ∩ Y, m1(X) * m2(Y)) | X ∈ dom(m1), Y ∈ dom(m2) }
      conflict = sum { v | (∅, v) ∈ raw }
      normalized = { (k, v / (1 - conflict)) | (k, v) ∈ raw, k ≠ ∅ }
  in normalized

swarm_consensus_ds : List<AgentBelief<A>> -> MassFunction<A>
swarm_consensus_ds beliefs =
  let masses = map to_mass_function beliefs
  in foldl1 dempster_combine masses
```

## 4. Coordination Protocols

### 4.1 Sequential Review

```
Agent₁ produces → Agent₂ reviews → Agent₃ reviews → ... → Final
```

```clair
sequential_review : List<Agent> -> Belief<A> -> Belief<A>
sequential_review [] belief = belief
sequential_review (reviewer : rest) belief =
  let reviewed = reviewer.review(belief)
  in if reviewed.approved
     then sequential_review rest (strengthen belief reviewed)
     else escalate belief reviewed
```

### 4.2 Parallel Consensus

```
                    ┌─── Agent₁ ───┐
                    │              │
Input ──────────────┼─── Agent₂ ───┼───► Consensus ───► Output
                    │              │
                    └─── Agent₃ ───┘
```

```clair
parallel_consensus : List<Agent> -> Task<A> -> Belief<A>
parallel_consensus agents task =
  let beliefs = parallel_map (\a -> a.solve(task)) agents
      conflicts = find_conflicts beliefs
  in if null conflicts
     then merge_agreeing beliefs
     else resolve_conflicts conflicts
```

### 4.3 Hierarchical Consensus

```
                    Arbiter
                       │
         ┌─────────────┼─────────────┐
         │             │             │
      Leader₁       Leader₂       Leader₃
         │             │             │
    ┌────┴────┐   ┌────┴────┐   ┌────┴────┐
    │    │    │   │    │    │   │    │    │
   A₁   A₂   A₃  A₄   A₅   A₆  A₇   A₈   A₉
```

```clair
hierarchical_consensus : Hierarchy -> Task<A> -> Belief<A>
hierarchical_consensus h task =
  -- Level 1: Workers produce beliefs
  let worker_beliefs = parallel_map (\w -> w.solve task) (workers h)

  -- Level 2: Leaders aggregate their teams
      leader_beliefs = map (\l ->
        l.aggregate (filter (belongs_to l) worker_beliefs))
        (leaders h)

  -- Level 3: Arbiter makes final decision
  in (arbiter h).decide leader_beliefs
```

### 4.4 Byzantine Fault Tolerant Consensus

Handle malicious or faulty agents:

```clair
-- BFT requires n ≥ 3f + 1 agents to tolerate f faulty ones

bft_consensus : List<Agent> -> Task<A> -> Belief<A>
bft_consensus agents task =
  -- Phase 1: All agents broadcast their beliefs
  let beliefs = broadcast_all agents task

  -- Phase 2: All agents broadcast what they received
      echoes = broadcast_all agents (received_beliefs)

  -- Phase 3: Commit if 2f+1 matching echoes
      committed = filter (has_enough_echoes (2*f+1)) beliefs

  in if length committed >= f + 1
     then strongest committed
     else no_consensus
```

## 5. Conflict Resolution Strategies

### Strategy 1: Confidence Arbitration

Higher confidence wins (with adjustment):

```clair
confidence_arbitration : List<AgentBelief<A>> -> Belief<A>
confidence_arbitration beliefs =
  let sorted = sort_by_conf_desc beliefs
      winner = head sorted
      opposition = sum (map conf (filter (disagrees_with winner) sorted))
  in winner.belief with
       confidence := conf winner.belief - opposition * 0.5
       justification := ArbitratedBy(Confidence, beliefs)
```

### Strategy 2: Expertise Arbitration

Domain expert wins:

```clair
expertise_arbitration : Domain -> List<AgentBelief<A>> -> Belief<A>
expertise_arbitration domain beliefs =
  let expert = maximum_by (expertise_in domain . agent) beliefs
  in expert.belief with
       justification := ArbitratedBy(Expertise(domain), beliefs)
```

### Strategy 3: Dialectical Resolution

Agents argue until convergence:

```clair
dialectical_resolution : List<Agent> -> Belief<A> -> Belief<A> -> Belief<A>
dialectical_resolution judges belief1 belief2 =
  loop rounds = 0:
    -- Each side presents arguments
    let args1 = arguments_for belief1 against belief2
        args2 = arguments_for belief2 against belief1

    -- Judges evaluate
        scores = map (\j -> j.evaluate args1 args2) judges
        verdict = majority scores

    in case verdict of
      Clear winner -> winner
      Undecided ->
        if rounds >= max_rounds
        then fallback_to_confidence belief1 belief2
        else loop (rounds + 1)
```

### Strategy 4: Synthesis

Create a new belief that incorporates both:

```clair
synthesis : Belief<A> -> Belief<A> -> Option<Belief<A>>
synthesis b1 b2 =
  -- Try to find a belief that satisfies constraints from both
  let constraints1 = extract_constraints b1
      constraints2 = extract_constraints b2
      combined = constraints1 ∪ constraints2
  in if satisfiable combined
     then Some (solve_for combined)
     else None  -- genuinely incompatible
```

### Strategy 5: Decomposition

Split the problem:

```clair
decomposition : Belief<A> -> Belief<A> -> (Belief<A>, Belief<A>, Conflict<A>)
decomposition b1 b2 =
  -- Find what they agree on, disagree on
  let agreed = common_ground b1 b2
      b1_only = b1 - agreed
      b2_only = b2 - agreed
      conflict = Conflict { positions: [b1_only, b2_only] }
  in (agreed, b1 with value := b1_only, conflict)

-- Accept agreed parts, escalate conflict
```

## 6. Swarm Dynamics

### Belief Propagation

When one agent updates, propagate to others:

```clair
propagate : Swarm -> Agent -> Belief<A> -> Swarm
propagate swarm agent new_belief =
  -- Notify connected agents
  let connections = neighbors swarm agent
      updates = map (\neighbor ->
        neighbor.consider new_belief) connections
  in apply_updates swarm updates
```

### Convergence

Does the swarm reach stable consensus?

```clair
type SwarmState = Map<Agent, Belief<A>>

converged : SwarmState -> SwarmState -> Bool
converged old new =
  all (\a -> distance (old[a]) (new[a]) < epsilon) (keys old)

iterate_until_convergence : Swarm -> Task<A> -> SwarmState
iterate_until_convergence swarm task =
  loop state = initial_state swarm task:
    let new_state = swarm_step swarm state
    in if converged state new_state
       then new_state
       else loop new_state
```

### Deadlock Detection

```clair
detect_deadlock : Swarm -> SwarmState -> List<SwarmState> -> Bool
detect_deadlock swarm current history =
  -- Cycle detection
  current ∈ history ||
  -- Oscillation detection
  is_oscillating (take 10 (current : history))

handle_deadlock : Swarm -> SwarmState -> Belief<A>
handle_deadlock swarm state =
  -- Options: random tiebreak, escalate, timeout
  case swarm.deadlock_policy of
    RandomTiebreak -> pick_random (current_beliefs state)
    Escalate -> escalate_to swarm.arbiter state
    Timeout -> strongest (current_beliefs state)
```

## 7. Practical Example: Code Review Swarm

```clair
-- Define the swarm
code_review_swarm : Swarm
code_review_swarm = Swarm {
  agents: [
    AI("claude", role: author),
    AI("gpt-4", role: reviewer),
    AI("gemini", role: reviewer),
    Human("alice", role: approver)
  ],

  coordination: Sequential [
    Phase { agent: author, action: produce },
    Phase { agents: reviewers, action: parallel_review },
    Phase { agent: approver, action: final_decision }
  ],

  consensus: WeightedByRole {
    author: 0.4,
    reviewer: 0.3,
    approver: 1.0  -- veto power
  }
}

-- Run the swarm
review_code : Code -> Swarm -> ReviewResult
review_code code swarm =
  -- Phase 1: Author produces belief about code
  let author_belief = (author swarm).analyze code

  -- Phase 2: Reviewers evaluate
      reviewer_beliefs = parallel_map
        (\r -> r.review code author_belief)
        (reviewers swarm)

  -- Phase 3: Check for consensus among reviewers
      reviewer_consensus = consensus (reviewer_beliefs)

  -- Phase 4: If reviewers agree, go to approver
  in case reviewer_consensus of
    Consensus belief ->
      let final = (approver swarm).decide belief
      in ReviewResult {
        outcome: final.approved,
        confidence: combined_confidence [author_belief, reviewer_consensus, final],
        trace: [author_belief, reviewer_beliefs, final]
      }

    Conflict positions ->
      -- Escalate to approver with conflict info
      let resolution = (approver swarm).resolve_conflict positions
      in ReviewResult {
        outcome: resolution.decision,
        confidence: resolution.confidence,
        conflict_resolved: positions,
        trace: [author_belief, reviewer_beliefs, resolution]
      }
```

## 8. Formal Properties

### Safety: No False Consensus

```clair
-- If consensus is reached, at least one honest agent believed it
theorem no_false_consensus:
  ∀ swarm result.
    consensus_reached swarm result →
    ∃ agent ∈ honest(swarm). believed agent result
```

### Liveness: Eventually Decide

```clair
-- Under reasonable conditions, swarm eventually decides
theorem eventual_decision:
  ∀ swarm task.
    connected swarm ∧
    bounded_delay swarm ∧
    honest_majority swarm →
    ◇ (decided swarm task)  -- eventually decides
```

### Agreement: Honest Agents Agree

```clair
-- If two honest agents decide, they decide the same
theorem agreement:
  ∀ swarm a1 a2 v1 v2.
    honest a1 ∧ honest a2 ∧
    decided a1 v1 ∧ decided a2 v2 →
    v1 = v2
```

## 9. Summary

| Scenario | Recommended Approach |
|----------|---------------------|
| All agents roughly equal | Confidence-weighted voting |
| Clear expertise hierarchy | Expertise arbitration |
| Untrusted agents possible | BFT consensus |
| Need to explain decision | Dialectical resolution |
| Beliefs partially compatible | Synthesis or decomposition |
| Time-critical | Hierarchical with timeout |

### When Consensus Fails

Not all disagreements can be resolved:

```clair
type ConsensusResult<A> =
  | Agreed (Belief<A>)
  | MajorityWithDissent (Belief<A>, dissenting: List<AgentBelief<A>>)
  | NoConsensus (positions: List<AgentBelief<A>>)
  | Deadlock (history: List<SwarmState>)

-- CLAIR tracks all of these, not just success
```

The value of CLAIR: even when consensus fails, we know *why* and *who* disagreed.
