# CLAIR Example: PI Calculation

This example demonstrates the Thinker (Oracle) + Assembler architecture.

## User Request

"Write a program to calculate PI to N decimal places"

---

## Phase 1: Oracle (Thinker LLM)

The Oracle reasons about the problem and produces a CLAIR trace.

```clair
; === USER INPUT ===
b1 1.0 L0 @user "write a program to calculate PI to N decimal places"

; === REQUIREMENTS ANALYSIS ===
b2 .95 L0 @self <b1 "N can be arbitrarily large"
b3 .95 L0 @self <b2 "need arbitrary precision arithmetic"
b4 .9 L0 @self <b3 "cannot use floating point, need big decimal or rational"

; === ALGORITHM SELECTION ===
b5 .3 L0 @self <b3 "Leibniz series: slow, needs billions of terms"
b6 .5 L0 @self <b3 "Machin formula: moderate speed"
b7 .85 L0 @self <b3 "Chudnovsky: ~14 digits per iteration"
b8 .85 L0 @self <b7 ?["n<20"] "use Chudnovsky algorithm"

; === REQUIRED COMPONENTS ===
b9 .9 L0 @self <b8 "need: factorial function"
b10 .9 L0 @self <b8 "need: arbitrary precision division"
b11 .9 L0 @self <b8 "need: square root of 10005"

; === COMPUTATION STRUCTURE ===
b12 .9 L0 @self <b9,b10,b11 "iterate k from 0 until precision reached"
b13 .9 L0 @self <b12 "for each k: compute (-1)^k * (6k)! * (13591409 + 545140134*k)"
b14 .9 L0 @self <b13 "divide by (3k)! * (k!)^3 * 640320^(3k+3/2)"
b15 .9 L0 @self <b14 "accumulate sum"
b16 .85 L0 @self <b15,b11 "final: PI = 426880 * sqrt(10005) / sum"

; === INTERFACE ===
b17 .9 L0 @self <b1 "input: n (positive integer, number of digits)"
b18 .9 L0 @self <b16 "output: string representation of PI to n digits"
```

### Trace Summary

```
b1 (user request)
├── b2 (N arbitrarily large)
│   └── b3 (need arbitrary precision)
│       ├── b4 (no floats)
│       ├── b5 (Leibniz: .3) ✗
│       ├── b6 (Machin: .5) ✗
│       └── b7 (Chudnovsky: .85) ✓
│           └── b8 (use Chudnovsky)
│               ├── b9 (need factorial)
│               ├── b10 (need division)
│               └── b11 (need sqrt)
│                   └── b12-b16 (algorithm steps)
└── b17-b18 (interface)
```

---

## Phase 2: Assembler (Doer LLM)

The Assembler reads the CLAIR trace and produces executable code.

### Assembler's Interpretation

| CLAIR Belief | Interpretation | Implementation Decision |
|--------------|----------------|------------------------|
| b4 | "arbitrary precision, no floats" | Use Python `decimal` module |
| b8 | "use Chudnovsky" | I know this algorithm |
| b9 | "need factorial" | Implement with memoization |
| b10 | "need division" | `Decimal` handles this |
| b11 | "need sqrt(10005)" | Use `Decimal.sqrt()` |
| b12 | "iterate k" | `for k in range(...)` |
| b13-b14 | "compute term" | Chudnovsky term formula |
| b16 | "426880 * sqrt / sum" | Final calculation |
| b17-b18 | "input n, output string" | Function signature |

### Generated Code (Python)

```python
"""
PI Calculator using Chudnovsky Algorithm

Generated from CLAIR trace.
Reasoning: b1 -> b3 -> b7 -> b8 -> b12-b16

To audit: "Why Chudnovsky?"
  b8 <- b7 "~14 digits per iteration"
  b7 <- b3 "need arbitrary precision"
  b3 <- b2 "N can be arbitrarily large"
  b2 <- b1 (user request)
"""

from decimal import Decimal, getcontext


def calculate_pi(n: int) -> str:
    """
    Calculate PI to n decimal places.

    Args:
        n: Number of decimal places (positive integer)

    Returns:
        String representation of PI to n decimal places

    CLAIR: b17 (input) -> b16 (calculation) -> b18 (output)
    """
    # b4: Set arbitrary precision (extra guard digits for intermediate calc)
    getcontext().prec = n + 50

    # b11: Precompute sqrt(10005)
    sqrt_10005 = Decimal(10005).sqrt()

    # b9: Factorial with memoization
    fact_cache = {0: Decimal(1)}
    def factorial(k):
        if k not in fact_cache:
            fact_cache[k] = Decimal(k) * factorial(k - 1)
        return fact_cache[k]

    # b12-b15: Main Chudnovsky loop
    C = Decimal(426880) * sqrt_10005  # Constant factor
    sum_total = Decimal(0)

    # b12: Iterate until precision reached (~14 digits per iteration)
    iterations_needed = n // 14 + 10

    for k in range(iterations_needed):
        # b13: Compute numerator: (-1)^k * (6k)! * (13591409 + 545140134*k)
        sign = Decimal((-1) ** k)
        numerator = sign * factorial(6 * k) * (13591409 + 545140134 * k)

        # b14: Compute denominator: (3k)! * (k!)^3 * 640320^(3k + 3/2)
        denominator = (
            factorial(3 * k) *
            (factorial(k) ** 3) *
            (Decimal(640320) ** (3 * k + Decimal('1.5')))
        )

        # b15: Accumulate
        sum_total += numerator / denominator

    # b16: Final calculation: PI = 426880 * sqrt(10005) / sum
    pi = C / sum_total

    # b18: Return as string with n decimal places
    pi_str = str(pi)
    decimal_point = pi_str.index('.')
    return pi_str[:decimal_point + n + 1]


# Example usage
if __name__ == "__main__":
    print(calculate_pi(50))
```

---

## Phase 3: Queries

The CLAIR trace can answer questions about the generated code.

### "Why Chudnovsky algorithm?"

**Trace:** `b8 <- b7 <- b3 <- b2 <- b1`

**Answer:** "The user requested PI to N decimal places, where N can be arbitrarily large. This requires arbitrary precision arithmetic. Chudnovsky algorithm was selected because it converges at ~14 digits per iteration, making it efficient for high precision (confidence .85 vs Leibniz .3 and Machin .5)."

### "Why not Leibniz?"

**Trace:** `b5 (.3 confidence)`

**Answer:** "Leibniz series was considered but scored low confidence (.3) because it requires billions of terms for high precision. Chudnovsky scored .85."

### "When should I reconsider this choice?"

**Trace:** `b8 ?["n<20"]`

**Answer:** "If n < 20 digits, Chudnovsky may be overkill. Simpler methods would suffice."

### "What does this code need to run?"

**Trace:** `b4, b9, b10, b11`

**Answer:** "Arbitrary precision arithmetic (no floats), factorial function, arbitrary precision division, and square root of 10005."

---

## Summary

| Phase | Actor | Input | Output |
|-------|-------|-------|--------|
| 1 | Oracle (Thinker) | User request | CLAIR trace |
| 2 | Assembler (Doer) | CLAIR trace | Executable code |
| 3 | Auditor | CLAIR trace + query | Natural language explanation |

**CLAIR is the interface.** The Oracle reasons, the Assembler implements, and the trace preserves why.
