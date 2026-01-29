#import "../layout.typ": *

// Appendix E: Complete CLAIR Language Specification
#heading(level: 1)[Complete CLAIR Language Specification]

This appendix provides the complete formal specification of the CLAIR language, including syntax (concrete and abstract), static semantics (type system), and dynamic semantics (operational rules). The specification is self-contained and sufficient for implementing a conforming CLAIR interpreter.

#heading(level: 2)[E.1 Syntax]

#heading(level: 3)[E.1.1 Type Grammar]

The type grammar defines the set of valid types in CLAIR.

+---
+**Category** | **Production** | **Description**
Base Types | B ::= "Nat" | Natural numbers
| | B ::= "Bool" | Boolean values
| | B ::= "String" | Text strings
| | B ::= "Unit" | Unit type (single value)
Confidence | c ∈ ℚ | Rational in [0,1]
Types | A ::= B | Base type
| | A ::= A → B | Function type
| | A ::= A × B | Product type
| | A ::= A + B | Sum type
| | A ::= "Belief<"A"["c"]" | Belief type with confidence bound
| | A ::= "Meta<"A"["n"]"["c"]" | Stratified meta-belief type
+---

#heading(level: 3)[E.1.2 Expression Grammar]

The expression grammar defines the syntactic forms of CLAIR programs.

+---
+**Category** | **Production** | **Description**
Variables | e ::= x | Variable reference
Lambdas | e ::= "λ"x":"A"."e | Anonymous function
Application | e ::= e e | Function application
Pairs | e ::= "("e ", " e")" | Ordered pair
Projections | e ::= e "." "1" | First projection
| | e ::= e "." "2" | Second projection
Injections | e ::= "inl@"B "("e")" | Left injection
| | e ::= "inr@"A "("e")" | Right injection
Case | e ::= "case" e "of" "inl" x "=>" e "|" "inr" y "=>" e | Sum elimination
Literals | e ::= n | Natural number literal
| | e ::= "true" | "false" | Boolean literals
| | e ::= "\"s"\"" | String literal
| | e ::= "()" | Unit literal
Beliefs | e ::= "belief("e ", " c ", " j")" | Belief constructor
| | e ::= "val("e")" | Extract belief value
| | e ::= "conf("e")" | Extract belief confidence
| | e ::= "just("e")" | Extract belief justification
Derivation | e ::= "derive("e ", " e")" | Combine beliefs (conjunctive)
Aggregation | e ::= "aggregate("e ", " e")" | Aggregate beliefs (independent)
Defeat | e ::= "undercut("e ", " e")" | Apply undercut
| | e ::= "rebut("e ", " e")" | Apply rebuttal
Introspection | e ::= "introspect("e")" | Safe self-reference
Let Binding | e ::= "let" x "=" e "in" e | Local binding
+---

#heading(level: 3)[E.1.3 Abstract Syntax]

The abstract syntax uses de Bruijn indices for variable representation.

#definition([
The abstract syntax "Expr" is defined inductively with the following constructors:

"var(n)" — Variable at de Bruijn index n
"lam(A, e)" — Lambda abstraction "λ":"A"."e
"app(e₁, e₂)" — Function application e₁ e₂
"pair(e₁, e₂)" — Ordered pair
"fst(e)" — First projection
"snd(e)" — Second projection
"inl(B, e)" — Left injection
"inr(A, e)" — Right injection
"case(e, e₁, e₂)" — Case analysis
"litNat(n)" — Natural literal
"litBool(b)" — Boolean literal
"litString(s)" — String literal
"litUnit" — Unit literal
"belief(v, c, j)" — Belief constructor
"val(e)" — Value extraction
"conf(e)" — Confidence extraction
"just(e)" — Justification extraction
"derive(e₁, e₂)" — Derivation
"aggregate(e₁, e₂)" — Aggregation
"undercut(e, d)" — Undercut
"rebut(e₁, e₂)" — Rebuttal
"introspect(e)" — Introspection
"letIn(e₁, e₂)" — Let binding

The "Justification" type tracks derivation structure:
"axiomJ(name)" — Named axiom
"rule(name, js)" — Named rule with premises
"agg(js)" — Aggregation
"undercut_j(j, d)" — Undercut application
"rebut_j(j₁, j₂)" — Rebuttal application
])

#heading(level: 3)[E.1.4 Well-Formedness]

A type is well-formed if all confidence bounds are in [0,1].

#definition([
The judgment "wf(A)" holds when:

"wf(B)" for all base types B
"wf(A)" ∧ "wf(B)" ⇒ "wf(A → B)"
"wf(A)" ∧ "wf(B)" ⇒ "wf(A × B)"
"wf(A)" ∧ "wf(B)" ⇒ "wf(A + B)"
"wf(A)" ∧ c ∈ [0,1] ⇒ "wf(Belief<"A"["c"])"
"wf(A)" ∧ c ∈ [0,1] ⇒ "wf(Meta<"A"["n"]"["c"])"
])

#heading(level: 2)[E.2 Static Semantics (Type System)]

#heading(level: 3)[E.2.1 Typing Contexts]

A typing context Γ maps variable indices to type-confidence pairs.

Γ ::= "∅" | Γ ", " 〈A, c〉

#definition([
The lookup operation Γ.lookup(n) returns the type-confidence pair at index n (0-indexed from most recent binding).
])

#heading(level: 3)[E.2.2 Typing Judgment Form]

The primary typing judgment has the form:

Γ "⊢" e ":" A "@" c

"In context Γ, expression e has type A with confidence bound c."

#heading(level: 3)[E.2.3 Typing Rules]

The following rules define well-typed CLAIR expressions. Confidence propagation is explicit in each rule.

*T-Variable:* Γ "⊢" "var(n)" ":" A "@" c if Γ.lookup(n) = 〈A, c〉

*T-Abstraction:* If Γ ", " 〈A, c_A〉 "⊢" e ":" B "@" c_B, then Γ "⊢" "lam(A, e)" ":" (A "→" B) "@" c_B

*T-Application:* If Γ "⊢" e₁ ":" (A "→" B) "@" c₁ and Γ "⊢" e₂ ":" A "@" c₂, then Γ "⊢" "app(e₁, e₂)" ":" B "@" (c₁ "×" c₂)

*Confidence multiplies for conjunctive derivation.*

*T-Pair:* If Γ "⊢" e₁ ":" A "@" c₁ and Γ "⊢" e₂ ":" B "@" c₂, then Γ "⊢" "pair(e₁, e₂)" ":" (A "×" B) "@" (c₁ "×" c₂)

*T-Fst/T-Snd* preserve confidence.

*T-Inl/T-Inr* preserve confidence.

*T-Case:* If Γ "⊢" e ":" (A "+" B) "@" c and Γ ", " 〈A, c〉 "⊢" e₁ ":" C "@" c₁ and Γ ", " 〈B, c〉 "⊢" e₂ ":" C "@" c₂, then Γ "⊢" "case(e, e₁, e₂)" ":" C "@" (c "⊕" c₁ "⊕" c₂)

*Uses probabilistic OR for confidence aggregation.*

*T-Belief:* If Γ "⊢" v ":" A "@" 1 and c_bound "≤" c_actual, then Γ "⊢" "belief(v, c_actual, j)" ":" "Belief<"A"["c_bound"]" "@" c_bound

The belief's actual confidence c_actual must meet or exceed the declared bound c_bound.

*T-Val/T-Conf/T-Just* preserve the enclosing confidence.

*T-Derive:* If Γ "⊢" e₁ ":" "Belief<"A"["c₁"]" "@" c_e₁ and Γ "⊢" e₂ ":" "Belief<"B"["c₂"]" "@" c_e₂, then Γ "⊢" "derive(e₁, e₂)" ":" "Belief<"A "×" B"["c₁ "×" c₂"]" "@" (c_e₁ "×" c_e₂)

*Confidence multiplies: both premises must be true.*

*T-Aggregate:* If Γ "⊢" e₁ ":" "Belief<"A"["c₁"]" "@" c_e₁ and Γ "⊢" e₂ ":" "Belief<"A"["c₂"]" "@" c_e₂, then Γ "⊢" "aggregate(e₁, e₂)" ":" "Belief<"A"["c₁ "⊕" c₂"]" "@" (c_e₁ "⊕" c_e₂)

*Uses probabilistic OR: independent evidence.*

*T-Undercut:* If Γ "⊢" e ":" "Belief<"A"["c"]" "@" c_e and Γ "⊢" d ":" "Belief<Unit>["d_c"]" "@" c_d, then Γ "⊢" "undercut(e, d)" ":" "Belief<"A"["undercut(c, d_c)"]" "@" (c_e "×" c_d)

where "undercut(c, d)" = c "×" (1 "−" d).

*T-Rebut:* If Γ "⊢" e_for ":" "Belief<"A"["c_for"]" "@" c_e₁ and Γ "⊢" e_against ":" "Belief<"A"["c_against"]" "@" c_e₂, then Γ "⊢" "rebut(e_for, e_against)" ":" "Belief<"A"["rebut(c_for, c_against)"]" "@" (c_e₁ "×" c_e₂)

where "rebut(c_for, c_against)" = c_for "//" (c_for "+" c_against) (with "1⁄2" when both are 0).

*T-Introspect:* If Γ "⊢" e ":" "Meta<"A"["m"]"["c"]" "@" c_e and m "<" n, then:

The resulting type is: "Meta<"Meta<"A"["m"]"["c"]"">["n"]"["g(c)"]" (a meta-belief about a meta-belief).

Thus: Γ "⊢" "introspect(e)" ":" "Meta<"Meta<"A"["m"]"["c"]"">["n"]"["g(c)"]" "@" c_e

where "g(c)" = c² is the Löb discount function (to prevent bootstrapping).

*Requires level constraint:* only higher levels can introspect lower levels.

#heading(level: 3)[E.2.4 Subtyping]

CLAIR supports subtyping based on confidence bounds.

*S-Belief:* "Belief<"A"["c"]" "<:" "Belief<"A"["c']"" if c "≥" c'

Higher confidence is a subtype of lower confidence.

*S-Meta* follows the same rule.

*T-Sub:* If Γ "⊢" e ":" A "@" c and A "<:" A' and c "≥" c', then Γ "⊢" e ":" A' "@" c'

Allows weakening both type and confidence.

#heading(level: 2)[E.3 Dynamic Semantics]

#heading(level: 3)[E.3.1 Values]

A value is a fully evaluated expression.

#definition([
The predicate "IsValue(e)" holds for:

- All lambda abstractions "lam(A, e)"
- All pairs "pair(v₁, v₂)" where v₁, v₂ are values
- All injections "inl(B, v)" and "inr(A, v)" where v is a value
- All literals ("litNat", "litBool", "litString", "litUnit")
- All belief constructors "belief(v, c, j)" where v is a value
])

#heading(level: 3)[E.3.2 Small-Step Operational Semantics]

The small-step relation e "→" e' defines single-step reduction using call-by-value evaluation order.

*Beta Reduction:* "(λ":"A"." e) v" "→" "e[x := v]" if "IsValue(v)"

*Context Rules:*
"app(e₁, e₂)" "→" "app(e₁', e₂)" if e₁ "→" e₁'
"app(v₁, e₂)" "→" "app(v₁, e₂')" if e₂ "→" e₂' and "IsValue(v₁)"

*Projections:*
"fst(pair(v₁, v₂))" "→" v₁ if "IsValue(v₁)", "IsValue(v₂)"
"snd(pair(v₁, v₂))" "→" v₂ if "IsValue(v₁)", "IsValue(v₂)"

Context rules for "fst" and "snd" evaluate subexpressions first.

*Case Analysis:*
When "case(inl(v), e₁, e₂)" evaluates and v is a value, it reduces to "e₁[x := v]".
When "case(inr(v), e₁, e₂)" evaluates and v is a value, it reduces to "e₂[y := v]".

Context rule for "case" evaluates the scrutinee first.

Context rule for "case" evaluates the scrutinee first.

*Let Binding:* "letIn(v, e)" "→" "e[x := v]" if "IsValue(v)"

Context rule for "letIn" evaluates the binding first.

*Belief Projections:*
"val(belief(v, c, j))" "→" v if "IsValue(v)"
"conf(belief(v, c, j))" "→" "belief(v, c, j)" if "IsValue(v)"
"just(belief(v, c, j))" "→" "litString(toString(j))" if "IsValue(v)"

Context rules evaluate subexpressions to values first.

*Derivation, Aggregation, Defeat:*

These operations evaluate to values using the confidence operations defined in the typing rules. The small-step semantics provides context rules that evaluate both subexpressions to values before computing the result.

For example, when "derive(v₁, v₂)" has both subexpressions as values, the evaluator computes a new belief with:
- Value: "pair(v₁.value, v₂.value)"
- Confidence: "v₁.confidence × v₂.confidence"
- Justification: "rule(\"derive\", [v₁.just, v₂.just])"

*Introspection:* "introspect(v)" "→" v if "IsValue(v)"

Context rule evaluates subexpression first.

#heading(level: 3)[E.3.3 Multi-Step Reduction]

The multi-step reduction relation e "→→" e' is the reflexive-transitive closure of "→".

e "→→" e if e = e'
e "→→" e'' if e "→" e' and e' "→→" e''

#heading(level: 3)[E.3.4 Evaluation Function]

The evaluation function "eval(e)" returns the result of reducing e to a value, or fails if:

1. The expression gets stuck (no applicable rule)
2. The expression exceeds the fuel bound (default: 1000 steps)

#definition([
"eval(e)" = "some(v)" if e "→→" v and "IsValue(v)"
"eval(e)" = "none" otherwise (stuck or out of fuel)
])

#heading(level: 2)[E.4 Well-Formedness Constraints]

#heading(level: 3)[E.4.1 Acyclicity of Justification Graphs]

For deterministic evaluation in the DAG semantics, justification graphs must be acyclic.

#definition([
A justification graph G = "(V, E)" is *well-formed* iff:

1. For all nodes v ∈ V, the transitive closure of E starting from v contains no cycles.
2. Equivalently: there is no path v "→→" v for any v ∈ V.

*Enforcement:* In the reference interpreter, this is checked during type checking by tracking provenance and ensuring no belief can transitively depend on itself.
])

#heading(level: 3)[E.4.2 Stratification Constraints]

For safe introspection, meta-belief levels must form a strict hierarchy.

#definition([
The *stratification constraint* requires:

1. Every "introspect(e)" operation has proof m "<" n where:
   - m is the level of the source belief
   - n is the level of the resulting meta-belief

2. This is enforced at compile time: the type checker requires a proof term of type m "<" n.

*Consequence:* No belief can introspect itself or any belief that transitively introspects it.
])

#heading(level: 3)[E.4.3 Confidence Bounds]

All confidence values must satisfy 0 "≤" c "≤" 1.

*Enforcement:* The type system checks this at all belief construction points.

#heading(level: 2)[E.5 Example Programs]

#example([
Basic Belief:
```
belief(42, 0.9, axiomJ("sensor-reading"))
```
A belief in the value 42 with confidence 0.9, traced to a sensor reading axiom.
], title: "Basic Belief")

#example([
Derivation:
```
let p = belief("it is raining", 0.8, axiomJ("weather-report")) in
let q = belief("I have an umbrella", 0.9, axiomJ("visual-check")) in
derive(p, q)
```
Combines two beliefs by multiplication, yielding confidence 0.72.
], title: "Conjunctive Derivation")

#example([
Independent Evidence Aggregation:
```
let e1 = belief("stock will rise", 0.6, axiomJ("analyst-a")) in
let e2 = belief("stock will rise", 0.7, axiomJ("analyst-b")) in
aggregate(e1, e2)
```
Uses probabilistic OR: 0.6 ⊕ 0.7 = 0.6 + 0.7 − 0.6×0.7 = 0.88.
], title: "Aggregation")

#example([
Defeat:
```
let claim = belief("system is secure", 0.95, axiomJ("vendor-claim")) in
let vuln = belief("critical CVE found", 0.8, axiomJ("security-audit")) in
undercut(claim, vuln)
```
Applies undercut: 0.95 × (1 − 0.8) = 0.19.
], title: "Undercut")

#heading(level: 2)[E.6 Summary]

This specification provides:

1. *Complete type grammar:* Base types, functions, products, sums, beliefs, and meta-beliefs
2. *Complete expression grammar:* All CLAIR syntactic forms
3. *Static semantics:* 20 typing rules covering all constructs
4. *Dynamic semantics:* Small-step operational semantics with call-by-value evaluation
5. *Well-formedness constraints:* Acyclicity, stratification, and confidence bounds

The specification is sufficient for implementing a conforming CLAIR interpreter and type checker. The Lean 4 formalization in Appendix A provides a machine-checked version of this specification.
