#!/bin/bash

# CLAIR Exploration Loop
# Usage:
#   ./loop.sh           # Auto mode: plan first, then explore
#   ./loop.sh plan      # Planning mode only
#   ./loop.sh build     # Exploration mode only
#   ./loop.sh 10        # Auto mode, max 10 iterations
#   ./loop.sh build 5   # Exploration mode, max 5 iterations

set -e

MODE="plan"
AUTO_MODE=true
PLAN_MAX_ITERATIONS=3
MAX_ITERATIONS=0
ITERATION=0
CONSECUTIVE_FAILURES=0

# Colors
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
NC='\033[0m'

for arg in "$@"; do
  if [[ "$arg" == "plan" ]]; then
    MODE="plan"
    AUTO_MODE=false
  elif [[ "$arg" == "build" ]]; then
    MODE="build"
    AUTO_MODE=false
  elif [[ "$arg" =~ ^[0-9]+$ ]]; then
    MAX_ITERATIONS=$arg
  fi
done

PROMPT_FILE="PROMPT_${MODE}.md"

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo -e "${RED}Error: $PROMPT_FILE not found${NC}"
  exit 1
fi

switch_to_build_mode() {
  echo ""
  echo -e "${CYAN}=== Switching to Exploration Mode ===${NC}"
  echo ""
  MODE="build"
  PROMPT_FILE="PROMPT_${MODE}.md"
  ITERATION=0
}

countdown() {
  local seconds=$1
  local message=$2

  while [[ $seconds -gt 0 ]]; do
    local hours=$((seconds / 3600))
    local minutes=$(((seconds % 3600) / 60))
    local secs=$((seconds % 60))
    printf "\r${CYAN}%s${NC} Time remaining: %02d:%02d:%02d " "$message" $hours $minutes $secs
    sleep 1
    ((seconds--))
  done
  printf "\r%-80s\r" " "
}

is_usage_limit_error() {
  local output="$1"
  local exit_code="$2"

  [[ "$exit_code" -eq 0 ]] && return 1

  if echo "$output" | grep -q "You've hit your limit\|You have hit your limit\|rate.limit\|usage.limit\|Error: 429\|Error: 529"; then
    return 0
  fi
  return 1
}

handle_usage_limit() {
  local wait_time=3600  # Default 1 hour

  echo ""
  echo -e "${YELLOW}=== Usage Limit Detected ===${NC}"
  echo -e "${YELLOW}Waiting for reset...${NC}"
  echo ""

  countdown $wait_time "Waiting for rate limit reset..."

  echo ""
  echo -e "${GREEN}Resuming...${NC}"
  echo ""

  CONSECUTIVE_FAILURES=0
}

echo -e "${GREEN}╔════════════════════════════════════════╗${NC}"
echo -e "${GREEN}║     CLAIR Exploration Loop             ║${NC}"
echo -e "${GREEN}║     Exploring AI-Native Computation    ║${NC}"
echo -e "${GREEN}╚════════════════════════════════════════╝${NC}"
echo ""

if [[ "$AUTO_MODE" == true ]]; then
  echo -e "Mode: ${CYAN}AUTO${NC} (plan ×${PLAN_MAX_ITERATIONS} → explore)"
  [[ $MAX_ITERATIONS -gt 0 ]] && echo "Max exploration iterations: $MAX_ITERATIONS"
else
  echo -e "Mode: ${CYAN}$(echo "$MODE" | tr '[:lower:]' '[:upper:]')${NC}"
  [[ $MAX_ITERATIONS -gt 0 ]] && echo "Max iterations: $MAX_ITERATIONS"
fi
echo "Press Ctrl+C to stop"
echo "---"

while true; do
  ITERATION=$((ITERATION + 1))
  echo ""
  MODE_DISPLAY=$(echo "$MODE" | tr '[:lower:]' '[:upper:]')
  if [[ "$MODE" == "plan" ]]; then
    echo -e "${GREEN}=== PLANNING Iteration $ITERATION ===${NC}"
  else
    echo -e "${GREEN}=== EXPLORATION Iteration $ITERATION ===${NC}"
  fi
  echo ""

  TEMP_OUTPUT=$(mktemp)
  set +e

  claude --print \
    --verbose \
    --output-format stream-json \
    --dangerously-skip-permissions \
    < "$PROMPT_FILE" 2>&1 | tee "$TEMP_OUTPUT" | sed 's/\x1b\[[0-9;]*m//g' | grep --line-buffered '^{' | jq --unbuffered -r '
      def tool_info:
        if .name == "Edit" or .name == "Write" or .name == "Read" then
          (.input.file_path // .input.path | split("/") | last | .[0:60])
        elif .name == "Bash" then
          (.input.command // .input.cmd | if contains("\n") then split("\n") | first | .[0:50] else .[0:80] end)
        elif .name == "Grep" then
          (.input.pattern | .[0:40])
        elif .name == "Glob" then
          (.input.pattern // .input.filePattern | .[0:40])
        elif .name == "Task" then
          (.input.description // .input.prompt | if contains("\n") then .[0:40] else .[0:80] end)
        else null end;
      if .type == "assistant" then
        .message.content[] |
        if .type == "text" then
          if (.text | split("\n") | length) <= 3 then .text else empty end
        elif .type == "tool_use" then
          "    [" + .name + "]" + (tool_info | if . then " " + . else "" end)
        else empty end
      elif .type == "result" then
        "--- " + ((.duration_ms / 1000 * 10 | floor / 10) | tostring) + "s, " + (.num_turns | tostring) + " turns ---"
      else empty end
    ' 2>/dev/null

  EXIT_CODE=${PIPESTATUS[0]}
  OUTPUT=$(cat "$TEMP_OUTPUT")
  RESULT_MSG=$(sed 's/\x1b\[[0-9;]*m//g' "$TEMP_OUTPUT" | grep '^{' | jq -r 'select(.type == "result") | .result // empty' 2>/dev/null | tail -1)
  rm -f "$TEMP_OUTPUT"
  set -e

  if is_usage_limit_error "$OUTPUT" "$EXIT_CODE"; then
    handle_usage_limit "$OUTPUT"
    ITERATION=$((ITERATION - 1))
    continue
  fi

  if [[ $EXIT_CODE -ne 0 ]]; then
    CONSECUTIVE_FAILURES=$((CONSECUTIVE_FAILURES + 1))
    echo ""
    echo -e "${RED}=== Error (exit code: $EXIT_CODE) ===${NC}"

    BACKOFF=$((30 * (2 ** (CONSECUTIVE_FAILURES - 1))))
    [[ $BACKOFF -gt 300 ]] && BACKOFF=300

    echo -e "${YELLOW}Retrying in ${BACKOFF}s... (failures: $CONSECUTIVE_FAILURES)${NC}"
    countdown $BACKOFF "Waiting..."
    ITERATION=$((ITERATION - 1))
    continue
  fi

  CONSECUTIVE_FAILURES=0

  # In auto mode, switch from plan to build after hitting plan cap
  if [[ "$AUTO_MODE" == true && "$MODE" == "plan" && $ITERATION -ge $PLAN_MAX_ITERATIONS ]]; then
    switch_to_build_mode
    continue
  fi

  if [[ "$RESULT_MSG" =~ RALPH_COMPLETE ]]; then
    echo ""
    echo -e "${GREEN}╔════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║     EXPLORATION COMPLETE               ║${NC}"
    echo -e "${GREEN}║     All threads explored               ║${NC}"
    echo -e "${GREEN}╚════════════════════════════════════════╝${NC}"
    break
  fi

  if [[ $MAX_ITERATIONS -gt 0 && $ITERATION -ge $MAX_ITERATIONS ]]; then
    echo ""
    echo -e "${GREEN}Reached max iterations ($MAX_ITERATIONS).${NC}"
    break
  fi

  sleep 2
done

echo ""
echo -e "${GREEN}Exploration session complete. Iterations: $ITERATION${NC}"
echo ""
echo "Results in:"
echo "  - exploration/*.md (thread explorations)"
echo "  - formal/*.md (formalizations)"
echo "  - EXPLORATION.md (state summary)"
