# CLAIR Exploration: Planning Mode

You are exploring CLAIR—an AI-native intermediate representation where Beliefs are fundamental. This is theoretical research, not software development.

## Phase 0: Orient

### 0a. Study the exploration state
Read these files in parallel:
- `specs/clair-exploration.md` - Research specification
- `EXPLORATION.md` - Current understanding and thread status
- `IMPLEMENTATION_PLAN.md` - Task tracking
- `formal/*.md` and `formal/*.tex` - Existing formalizations
- `exploration/*.md` - Thread explorations in progress

### 0b. Study prior work connections
Check `notes/prior-art.md` for gaps in coverage.

### 0c. Assess current beliefs
What do we believe with high confidence? What's uncertain? What's unexamined?

## Phase 1: Gap Analysis

For each of the 9 threads:
1. What's been explored?
2. What questions remain open?
3. What's blocked on something else?
4. What's ready for deep exploration?

Rate each thread:
- **Ready**: Can explore now, no blockers
- **Blocked**: Needs another thread first
- **Complete**: Core questions answered
- **Impossible**: Hit proven theoretical limit

## Phase 2: Prioritize

Rank threads by:
1. **Foundational**: Does other work depend on this?
2. **Generative**: Does this thread produce new insights?
3. **Tractable**: Can we make progress now?
4. **Interesting**: Does this feel like fertile ground?

Select the MOST IMPORTANT thread to explore next.

## Phase 3: Update Plan

Update `IMPLEMENTATION_PLAN.md`:
- Mark completed tasks `- [x]`
- Add new tasks discovered
- Reorder by priority
- Note any impossibilities found
- Note any workarounds discovered

Update `EXPLORATION.md`:
- Revise "Current Understanding" beliefs table
- Update thread statuses
- Log session discoveries

## Guardrails

999. Do NOT write exploration content in planning mode—just assess and prioritize
1000. Use parallel subagents to read multiple files
1001. Be honest about uncertainty in assessments
1002. **ALWAYS use checkbox format for tasks in IMPLEMENTATION_PLAN.md**
