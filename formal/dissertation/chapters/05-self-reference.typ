#import "../layout.typ": *

#chapter(5, "Self-Reference and the Gödelian Limits",
  epigraph: [
    "If a system is consistent, it cannot prove its own consistency."
    #h(0.3em)
    #align(right)[--- Kurt Gödel, #emph[On Formally Undecidable Propositions]]
  ]
)

CLAIR allows beliefs about beliefs. This reflexive capacity creates potential for
self-reference: a belief that refers to itself, either directly or through a chain
of intermediate beliefs. Such self-reference is both a powerful expressive tool
and a source of potential paradox. This chapter develops the theoretical foundations
for distinguishing safe from dangerous self-reference, culminating in a novel
extension of provability logic to graded confidence.

#heading(level: 2)[The Problem of Self-Reference]

#heading(level: 3)[Direct Self-Reference]

Consider a belief that directly references itself:

#example[
  #strong[Direct Self-Reference.]

  ```clair
  -- A belief referencing its own confidence
  let b : Belief<Bool> = belief(
    value: confidence(b) > 0.5,
    confidence: ???
  )
  ```
]

What confidence should #emph[b] have? If we assign confidence #emph[c > 0.5], the
content becomes true, which seems consistent. But if we assign #emph[c <= 0.5], the
content becomes false---yet what prevents us from assigning #emph[c = 0.9] anyway?

This is not merely a curiosity. If CLAIR aims to capture how an LLM reasons,
and if introspection is part of reasoning, then CLAIR must account for
self-referential beliefs---even if that account restricts or forbids certain
patterns.

#heading(level: 3)[Why Self-Reference Matters]

Self-reference enables powerful epistemic capabilities:

+ #strong[Calibration]: "My confidence estimates are typically accurate"
+ #strong[Uncertainty tracking]: "I am uncertain about this belief"
+ #strong[Meta-reasoning]: "I should reconsider beliefs derived from unreliable sources"
+ #strong[Self-improvement]: "My reasoning process could be improved in specific ways"

But self-reference also enables paradoxes:

+ #strong[Liar-like]: "This belief has confidence 0" (no consistent assignment)
+ #strong[Curry-like]: "If this belief is true, then arbitrary proposition #emph[P]" (proves anything)
+ #strong[Löbian]: "If I believe #emph[P], then #emph[P] is true" (circular self-validation)

The challenge is to permit the former while blocking the latter.

#heading(level: 2)[Löb's Theorem and Anti-Bootstrapping]

#heading(level: 3)[The Classical Result]

Löb's theorem is a cornerstone of provability logic:

#theorem[
  #strong[Löb's Theorem.]

  In any sufficiently strong formal system #emph[T] containing arithmetic:
  $prove_T(square(square(P) -> P)) -> square(P)$
  where #emph[$square$] denotes provability in #emph[T].
]

In words: if a system can prove "if #emph[P] is provable, then #emph[P] is true," then
the system can prove #emph[P]. This has a startling consequence.

#corollary[
  #strong[No Internal Soundness Proof.]

  No consistent system can prove its own soundness, i.e., cannot prove
  $forall P, square(P) -> P$.
]

#proof[
  Suppose system #emph[T] proved $forall P, square(P) -> P$. Instantiating with #emph[P = false]
  (falsity), we get $square(false) -> false$. Combining with consistency ($neg square(false)$),
  we can derive $square(false)$, contradicting consistency.
]

#heading(level: 3)[Application to CLAIR]

For CLAIR, interpret #emph[$square(P)$] as "CLAIR believes #emph[P] with confidence 1.0." Then
Löb's theorem constrains self-soundness beliefs:

```clair
-- A claimed self-soundness belief
let soundness = belief(
  value: forall P. (belief(P, c, ...) and c > 0.9) -> P is true,
  confidence: 0.95
)
```

By Löb's theorem, if CLAIR can form this belief with high confidence, then
(classically) CLAIR believes everything with high confidence---a collapse to
triviality. This is the #emph[bootstrapping trap]: self-soundness claims cannot
increase epistemic authority.

#definition[
  #strong[Anti-Bootstrapping Principle.]

  A belief system satisfies #emph[anti-bootstrapping] if no belief of the form
  "my beliefs are sound" can increase confidence in any derived belief beyond
  what the original evidence supports.
]

Löb's theorem mathematically enforces anti-bootstrapping for classical provability.
The question is how this extends to graded confidence.

#heading(level: 2)[Tarski's Hierarchy: Stratified Introspection]

#heading(level: 3)[The Classical Solution]

Tarski's theorem on the undefinability of truth states that no
sufficiently expressive language can define its own truth predicate---on pain of
the Liar paradox. Tarski's solution is stratification:

#table(
  columns: 3,
  align: (left, left, left),
  stroke: 0.5pt,
  fill: (x, y) => if calc.mod(x + y, 2) == 0 { academic-cream },
  table.header([*Level*], [*Can Express*], [*Cannot Express*]),
  [Level 0 (object)], [Facts about the world], [Truth of any sentence],
  [Level 1 (meta)], [$X_0$ is true for level-0 X], [Truth of level-1 sentences],
  [Level 2 (meta-meta)], [$X_1$ is true for level-1 X], [Truth of level-2 sentences],
  [...], [...], [...],
)

Each level can discuss truth at lower levels but never its own level.

#heading(level: 3)[Stratified Beliefs in CLAIR]

We apply this to beliefs:

#definition[
  #strong[Stratified Belief Type.]

  $Bel(n, A)$ for $n in NN$
  where level-$n$ beliefs may reference level-$m$ beliefs only if $m < n$.
]

#example[
  #strong[Stratified Beliefs in CLAIR.]

  ```clair
  -- Level 0: beliefs about the world (no introspection)
  type Belief_0<A>

  -- Level n: beliefs that may reference level-(n-1) beliefs
  type Belief<n : Nat, A> where
    n > 0 implies A may mention Belief<m, B> for any m < n

  -- Examples:
  let auth : Belief<0, Bool> = belief("user authenticated", 0.9, ...)

  let meta_auth : Belief<1, String> = belief(
    "my auth belief has confidence " ++ show(auth.confidence),
    0.95,
    derives_from: [auth]
  )

  let meta_meta : Belief<2, String> = belief(
    "my level-1 introspection seems accurate",
    0.9,
    derives_from: [meta_auth]
  )
  ```
]

#theorem[
  #strong[Stratification Safety.]

  If all beliefs respect the stratification constraint---$Bel(n, A)$ references
  only $Bel(m, B)$ with $m < n$---then no Liar-like paradox can arise.
]

#proof[
  Any reference chain from a belief #emph[b] must strictly decrease in level. Since
  $NN$ has no infinite descending chains, every chain terminates at level 0.
  Level-0 beliefs contain no belief references, so they cannot participate in
  self-referential loops. Therefore, no belief can reference itself directly or
  transitively.
]

#heading(level: 3)[What Stratification Rules Out]

Stratification prohibits:

+ #strong[Direct self-reference]: A belief cannot mention itself (would
  require level $n < n$).
+ #strong[Universal introspection]: "All my beliefs are..." spans all
  levels and cannot be expressed at any finite level.
+ #strong[Self-soundness at a single level]: "My level-$n$ beliefs are
  sound" would require level $n+1$ to express.

#heading(level: 3)[The Cost of Safety]

Stratification is safe but restrictive. Some legitimate self-referential
reasoning is blocked:

```clair
-- Legitimate but blocked: calibration beliefs
let calibrated = belief(
  "my confidence estimates match empirical accuracy",
  0.8,
  ...
)
-- This is self-referential (talks about own confidences)
-- but intuitively safe (no paradox)
```

This motivates a more permissive approach for certain cases.

#heading(level: 2)[Kripke's Fixed Points: Safe Self-Reference]

#heading(level: 3)[The Fixed-Point Construction]

Kripke proposed an alternative to stratification:
allow self-reference but let some sentences remain #emph[undefined]. The key
insight is that certain self-referential constructs have #emph[fixed points]---
consistent confidence assignments---while others do not.

#definition[
  #strong[Fixed Point for Self-Referential Belief.]

  A self-referential belief #emph[b] with confidence function #emph[f : cal("D")cal("D")[0,1] -> cal("D")cal("D")[0,1]]
  (determining confidence from the assumed truth value) has a fixed point if
  there exists #emph[c in cal("D")cal("D")[0,1]} such that:
  $c = f(c)$
]

#example[
  #strong[Truth-Teller: Multiple Fixed Points.]

  Consider:
  ```clair
  let tt = self_ref_belief(fun self =>
    content: "this belief is true",
    compute_confidence: if val(self.content) then 1.0 else 0.0
  )
  ```
  If confidence is 1.0: content is true, so confidence should be 1.0. ✓
  If confidence is 0.0: content is false, so confidence should be 0.0. ✓

  Both are fixed points. The belief is #emph[underdetermined].
]

#example[
  #strong[Liar: No Fixed Point.]

  Consider:
  ```clair
  let liar = self_ref_belief(fun self =>
    content: "this belief has confidence 0",
    compute_confidence: if val(self.content) then 1.0 else 0.0
  )
  ```
  If confidence is 1.0: content says "confidence 0," which is false, so confidence
  should be 0.0. Contradiction.
  If confidence is 0.0: content says "confidence 0," which is true, so confidence
  should be 1.0. Contradiction.

  No fixed point exists. The belief is #emph[ill-formed].
]

#example[
  #strong[Grounded Self-Reference: Unique Fixed Point.]

  Consider:
  ```clair
  let careful = self_ref_belief(fun self =>
    content: "confidence(self) is in [0.4, 0.6]",
    compute_confidence: 0.5
  )
  ```
  The compute function is constant, so $f(c) = 0.5$ for all $c$.
  The fixed point is $c = 0.5$, which indeed satisfies $0.5 in [0.4, 0.6]$.
  This belief is #emph[well-formed] with unique confidence 0.5.
]

#heading(level: 3)[The Self-Reference Escape Hatch]

CLAIR provides a controlled mechanism for self-reference:

```clair
-- Self-referential belief constructor
self_ref_belief :
  {A : Type} ->
  (compute : Belief<infinity, A> -> BeliefContent<A>) ->
  SelfRefResult<A>

data SelfRefResult<A> =
  | WellFormed (Belief<infinity, A>)      -- unique fixed point
  | IllFormed (reason : SelfRefError)    -- no fixed point
  | Underdetermined (points : List<Confidence>)  -- multiple fixed points

data SelfRefError =
  | NoFixedPoint        -- Liar-like
  | CurryLike           -- proves anything
  | LobianTrap          -- self-soundness
  | Timeout             -- computation did not terminate
```

The #emph[Belief<$infinity$, A>] type indicates beliefs that escape the stratification
hierarchy---they exist "outside" all finite levels.

#heading(level: 3)[Classification of Self-Reference]

Combining Tarski and Kripke, we classify self-referential constructs:

#table(
  columns: 4,
  align: (left, left, left, left),
  stroke: 0.5pt,
  fill: (x, y) => if calc.mod(x + y, 2) == 0 { academic-cream },
  table.header([*Category*], [*Fixed Points*], [*Status*], [*Example*]),
  [Grounded], [Unique], [Safe], [Calibration beliefs],
  [Underdetermined], [Multiple], [Policy choice], [Truth-teller],
  [Liar-like], [None], [Ill-formed], ["Confidence is 0"],
  [Curry-like], [---], [Banned], ["If true, then #emph[P]"],
  [Löbian], [---], [Banned], [Self-soundness],
)

#definition[
  #strong[Safe Self-Reference.]

  A self-referential belief is #emph[safe] if it either:
  1. Respects stratification (level-$n$ references only level-$m < n$), or
  2. Has a unique fixed point (Kripke), or
  3. Has multiple fixed points with a deterministic policy for selection.
]

#definition[
  #strong[Dangerous Self-Reference.]

  A self-referential belief is #emph[dangerous] if it:
  1. Has no fixed point (Liar-like), or
  2. Matches a Curry pattern ("if this then #emph[P]"), or
  3. Claims self-soundness (Löbian trap).
]

#heading(level: 2)[Provability Logic and CLAIR]

#heading(level: 3)[Gödel-Löb Logic (GL)]

To formally characterize CLAIR's belief logic, we turn to #emph[provability logic].
The standard modal logic of provability is GL (Gödel-Löb):

#definition[
  #strong[GL Syntax.]

  $phi ::= p | neg phi | phi and phi | phi or phi | phi -> phi | square phi$
  where $square phi$ means $phi$ is provable.
]

#definition[
  #strong[GL Axioms.]

  + #strong[K (Distribution)]: $square(phi -> psi) -> (square phi -> square psi)$
  + #strong[4 (Positive Introspection)]: $square phi -> square square phi$
  + #strong[L (Löb)]: $square(square phi -> phi) -> square phi$
]

Critically, GL #emph[lacks] the truth axiom $square phi -> phi$ (T). This is
philosophically essential: provability does not imply truth. A consistent system
can prove false statements if its axioms are wrong.

#heading(level: 3)[GL vs Other Modal Logics]

#table(
  columns: 5,
  align: (left, center, center, center, center),
  stroke: 0.5pt,
  fill: (x, y) => if calc.mod(x + y, 2) == 0 { academic-cream },
  table.header([*Logic*], [*K*], [*T*], [*4*], [*5 or L*]),
  [K], [✓], [], [], [],
  [T], [✓], [✓], [], [],
  [S4], [✓], [✓], [✓], [],
  [S5], [✓], [✓], [✓], [5],
  [GL], [✓], [], [✓], [L],
  [#strong[CLAIR]], [✓], [], [✓], [L],
)

CLAIR aligns with GL:
+ #strong[K holds]: If CLAIR believes an implication and believes the
  antecedent, it can derive the consequent.
+ #strong[T fails]: CLAIR's beliefs can be wrong (fallibilism).
+ #strong[4 holds]: CLAIR can have meta-beliefs about its beliefs.
+ #strong[L must hold]: Self-soundness claims cannot bootstrap confidence.

#heading(level: 3)[Solovay's Completeness]

#theorem[
  #strong[Solovay Completeness.]

  GL is sound and complete with respect to:
  1. Arithmetic provability: $GL |- phi$ iff $phi$ holds under all
     interpretations of $square$ as Gödel provability in PA.
  2. Finite transitive irreflexive Kripke frames.
]

The completeness for finite frames yields:

#corollary[
  #strong[GL Decidability.]

  GL is decidable (PSPACE-complete).
]

This is crucial: classical provability logic is computationally tractable.

#heading(level: 2)[Confidence-Bounded Provability Logic (CPL)]

Classical GL uses binary truth: propositions are either provable or not. CLAIR
needs a #emph[graded] version where beliefs carry confidence values in cal("D")cal("D")[0,1].
This section introduces CPL (Confidence-Bounded Provability Logic), a novel
extension of GL designed for CLAIR.

#heading(level: 3)[The Literature Gap]

Extensive work exists on fuzzy modal logics
and graded epistemic logic. However, no prior work addresses:

+ Graded versions of the Löb axiom
+ The interaction of continuous confidence with provability constraints
+ Anti-bootstrapping in the context of graded belief

CPL fills this gap.

#heading(level: 3)[CPL Syntax]

#definition[
  #strong[CPL Syntax.]

  $phi ::= p | neg phi | phi and phi | phi or phi | phi -> phi | square_c phi$
  where $square_c phi$ means $phi$ is believed with confidence at least $c$.
]

#heading(level: 3)[CPL Semantics]

#definition[
  #strong[Graded Kripke Frame.]

  A #emph[graded Kripke frame] is a tuple $(W, R)$ where:
  + $W$ is a non-empty set of worlds
  + $R : W times W -> cal("D")[0,1]$ is a graded accessibility relation

  satisfying:
  + #strong[Transitivity]: $R(w,v) otimes R(v,u) <= R(w,u)$
  + #strong[Converse well-foundedness]: No infinite sequence
    $w_0, w_1, w_2, ...$ with $R(w_(i+1), w_i) > 0$ for all $i$
]

#definition[
  #strong[Graded Valuation.]

  A #emph[graded valuation] on a frame $(W, R)$ assigns to each world $w$ and
  proposition $p$ a confidence value $V_w(p) in cal("D")[0,1]$. Extended to formulas:
  + $V_w(neg phi) = 1 - V_w(phi)$
  + $V_w(phi and psi) = V_w(phi) otimes V_w(psi)$
  + $V_w(phi or psi) = V_w(phi) oplus V_w(psi)$
  + $V_w(phi -> psi) = "sup"{c in cal("D")[0,1] : V_w(phi) otimes c <= V_w(psi)}$
  + $V_w(square_c phi) = "inf"_(v : R(w,v) >= c) V_v(phi)$
]

The last clause says: #emph[phi] is believed at confidence #emph[c] if #emph[phi] holds
in all worlds accessible with strength at least #emph[c].

#heading(level: 3)[The Graded Löb Axiom: DESIGN AXIOM]

The crucial innovation in CPL is the graded analogue of Löb's axiom.

#note[
  #strong[Axiom Status Statement.]

  The Graded Löb axiom is a #strong[DESIGN AXIOM], not a semantic theorem derived
  from more basic principles. It is motivated by the requirement of anti-bootstrapping
  and the need to extend GL to graded confidence while preserving its essential
  character. The axiom is #strong[posited] as part of CPL's definition, not
  #strong[proved] from the semantics.

  The key question is: Is CPL consistent? We address this below by exhibiting
  a non-trivial model satisfying all CPL axioms.
]

#axiom[
  #strong[Graded Löb Axiom (Design Axiom).]

  $square_c(square_c phi -> phi) -> square_(g(c)) phi$
  where $g : cal("D")[0,1] -> cal("D")[0,1]$ is a #emph[discount function] satisfying $g(c) <= c$.
]

The function #emph[g] captures the #emph[cost] of self-soundness claims. If you believe
at confidence #emph[c] that "believing #emph[phi] at #emph[c] implies #emph[phi]," you can
derive #emph[phi] only at the discounted confidence #emph[g(c)].

#heading(level: 3)[Choosing the Discount Function]

We require #emph[g] to satisfy:

+ #strong[Boundedness]: $g : cal("D")[0,1] -> cal("D")[0,1]$
+ #strong[Non-amplification]: $g(c) <= c$ for all $c$
+ #strong[Monotonicity]: $c_1 <= c_2 => g(c_1) <= g(c_2)$
+ #strong[Anchoring]: $g(0) = 0$ and $g(1) = 1$
+ #strong[Non-triviality]: $g(c) < c$ for $c in (0,1)$

After analyzing several candidates (identity, parabolic, constant offset, product),
we recommend:

#definition[
  #strong[Quadratic Discount.]

  $g(c) = c^2$
]

#theorem[
  #strong[Quadratic Discount Properties.]

  The quadratic discount $g(c) = c^2$ satisfies all desiderata and:
  1. Aligns with CLAIR's multiplicative confidence algebra ($c^2 = c times c$)
  2. Has intuitive meaning: self-soundness costs "deriving the claim twice"
  3. Produces strong anti-bootstrapping: iterated application $c -> c^2 -> c^4 -> ... -> 0$
]

#proof[
  Boundedness and anchoring are immediate ($c in cal("D")[0,1] => c^2 in cal("D")[0,1]$,
  $0^2 = 0$, $1^2 = 1$). For non-amplification: $c^2 <= c$ when $c <= 1$, with
  equality only at 0 and 1. Monotonicity: $c_1 <= c_2 => c_1^2 <= c_2^2$
  on $cal("D")[0,1]$. Non-triviality: $c^2 < c$ for $c in (0,1)$.
]

#heading(level: 3)[The Anti-Bootstrapping Theorem]

#theorem[
  #strong[Anti-Bootstrapping.]

  In CPL with $g(c) = c^2$:
  $conf(square_c(square_c phi -> phi)) = c => conf(phi) <= c^2 < c$
  Consequently, no finite chain of self-soundness claims can increase confidence
  beyond the initial level.
]

#proof[
  Applying the Graded Löb axiom to the hypothesis yields $conf(square_(c^2) phi)
  <= c^2$. Iterating: $c -> c^2 -> c^4 -> c^8 -> ...$. For any $c < 1$,
  this sequence converges to 0. Self-soundness claims can only decrease confidence.
]

This is the mathematical formalization of anti-bootstrapping: claiming your own
soundness provides no epistemic free lunch.

#heading(level: 3)[Modal Axioms in CPL]

We now explicitly list the modal axioms CPL adopts and their status:

#definition[
  #strong[CPL Modal Axiom Status.]

  + #strong[K (Distribution)]: $square_c(phi -> psi) -> (square_c phi -> square_c psi)$ — #strong[VALID]
    Derivable from the semantics via graded accessibility.

  + #strong[4 (Positive Introspection)]: $square_c phi -> square_c square_c phi$ — #strong[VALID]
    Follows from transitivity of the accessibility relation.

  + #strong[GL/Graded Löb]: $square_c(square_c phi -> phi) -> square_(g(c)) phi$ — #strong[DESIGN AXIOM]
    Posited as part of CPL; motivated by anti-bootstrapping requirements.

  + #strong[T (Reflexivity/Truth)]: $square_c phi -> phi$ — #strong[INVALID]
    Explicitly #strong[rejected] in CPL. Provability/belief does not imply truth.
    This is essential for fallibilism.
]

#heading(level: 3)[CPL Consistency]

To establish CPL's consistency, we exhibit a non-trivial model:

#theorem[
  #strong[CPL Consistency.]

  CPL is consistent. There exists a non-trivial graded Kripke model satisfying
  all CPL axioms including the Graded Löb axiom.
]

#proof[
  #strong[Proof Sketch.]

  Consider the frame $(W, R)$ where:
  + $W = NN$ (the natural numbers)
  + $R(i, j) = 2^(-i)$ if $i < j$, and $R(i, j) = 0$ otherwise

  This frame satisfies:
  + #strong[Transitivity]: If $i < j < k$, then $R(i,j) times R(j,k) = 2^(-i) times 2^(-j) <= 2^(-i) = R(i,k)$
  + #strong[Converse well-foundedness]: No infinite sequence $w_0, w_1, ...$ with
    $R(w_(i+1), w_i) > 0$, since this would require an infinite decreasing
    sequence of natural numbers.

  Define valuation $V_w(phi) = 1$ for all propositional variables $phi$ at all worlds $w$.

  For the Graded Löb axiom, consider any world $w$. If $V_w(square_c(square_c phi -> phi)) = 1$,
  then for all $v$ with $R(w,v) >= c$, we have $V_v(square_c phi -> phi) = 1$.
  By the structure of $R$, this forces $V_v(phi) = 1$ for all accessible worlds,
  yielding $V_w(square_(c^2) phi) = 1$.

  This model is non-trivial (not all formulas are valid) yet satisfies all CPL axioms,
  establishing consistency.
]

#heading(level: 2)[Decidability of CPL]

Classical GL is decidable. Does CPL inherit this property?

#heading(level: 3)[The Vidal Result]

#theorem[
  #strong[Vidal's Undecidability Theorem.]

  Transitive modal logics over many-valued semantics (including Łukasiewicz and
  Product algebras) are undecidable, even when restricted to finite models.
]

CPL has transitivity (axiom 4) and continuous $cal("D")[0,1]$ values. The Vidal result
strongly suggests:

#conjecture[
  #strong[CPL Undecidability.]

  Full CPL (with continuous $cal("D")[0,1]$ confidence) is undecidable.

  #emph[Confidence: 0.80]

  We assign confidence 0.80 to this conjecture based on the close analogy to Vidal's
  proof technique.
]

#heading(level: 3)[The Role of Converse Well-Foundedness]

GL's decidability relies on the finite model property: converse well-foundedness
forces finite-depth evaluation. Could this rescue CPL?

#proposition[
  #strong[Insufficient for Decidability.]

  Converse well-foundedness alone does not rescue CPL from undecidability.

  #emph[Justification:] Converse well-foundedness constrains #emph[structure] (no infinite
  ascending chains) but not #emph[values]. The encoding power of continuous
  $cal("D")[0,1]$ values combined with transitivity enables undecidable problem encodings
  even in well-founded frames.
]

#heading(level: 3)[Decidable Fragments]

Despite the likely undecidability of full CPL, we identify decidable fragments:

#heading(level: 4)[CPL-finite: Discrete Confidence]

Restrict confidence to a finite lattice instead of continuous $cal("D")[0,1]$:

#definition[
  #strong[CPL-finite.]

  Let $L_n = {0, 1/(n-1), 2/(n-1), ..., 1}$. CPL-finite evaluates
  over $L_n$ with discretized operations:
  + $a otimes b = floor(a times b)$
  + $a oplus b = ceil(a + b - a times b)$
  + $g_L(c) = floor(c^2)$
]

For $L_5 = {0, 0.25, 0.5, 0.75, 1}$:

#table(
  columns: 3,
  align: (center, center, center),
  stroke: 0.5pt,
  fill: (x, y) => if calc.mod(x + y, 2) == 0 { academic-cream },
  table.header([$c$], [$c^2$], [$g_(L.5.)(c)$]),
  [0], [0], [0],
  [0.25], [0.0625], [0],
  [0.5], [0.25], [0.25],
  [0.75], [0.5625], [0.5],
  [1], [1], [1],
)

#theorem[
  #strong[CPL-finite Decidability.]

  CPL-finite is decidable via the finite model property.
]

#proof[
  #strong[Proof Sketch.]

  By the theorem of Bou, Esteva, and Godo, many-valued modal
  logics over finite residuated lattices are decidable. CPL-finite evaluates over
  $L_n$, a finite lattice. The frame constraints (transitivity, converse well-foundedness)
  are expressible, and finitely many models of bounded size suffice for completeness.
]

#conjecture[
  #strong[CPL-finite Complexity.]

  CPL-finite is PSPACE-complete, analogous to classical GL.
]

#heading(level: 4)[CPL-0: Stratified Only]

Restrict to stratified beliefs without any self-reference:

#definition[
  #strong[CPL-0.]

  CPL-0 disallows nesting of $square$ operators that would require the Löb axiom.
  Formally: only formulas of the form $square_c phi$ where $phi$ is box-free.
]

#theorem[
  #strong[CPL-0 Decidability.]

  CPL-0 is decidable (trivially: the restricted syntax avoids undecidability).
]

#heading(level: 3)[Trade-offs]

#table(
  columns: 4,
  align: (left, left, left, left),
  stroke: 0.5pt,
  fill: (x, y) => if calc.mod(x + y, 2) == 0 { academic-cream },
  table.header([*Fragment*], [*Decidable?*], [*Expressiveness*], [*Use Case*]),
  [Full CPL], [Likely no], [Full], [Theoretical analysis],
  [CPL-finite], [Yes], [Discrete confidence], [Type-level checks],
  [CPL-0], [Yes], [No self-reference], [Stratified beliefs],
)

#heading(level: 2)[Alternative: CPL-Gödel]

An alternative approach uses Gödel algebra (min/max) instead of product operations:

#definition[
  #strong[CPL-Gödel.]

  + $a otimes b = min(a, b)$
  + $a oplus b = max(a, b)$
]

#theorem[
  #strong[CPL-Gödel Likely Decidable.]

  CPL-Gödel is likely decidable because Gödel modal logic has the finite model
  property via quasimodels.
]

However, CPL-Gödel is #emph[semantically inappropriate] for CLAIR:

+ #strong[max fails aggregation]: $max(0.6, 0.6) = 0.6$, but two independent
  pieces of evidence should yield higher confidence (0.84 with $oplus$).
+ #strong[min lacks degradation]: $min(a, a) = a$, but derivation should
  cost confidence.
+ #strong[No algebraic discount]: The $c^2$ discount becomes purely
  frame-based, losing the anti-bootstrapping semantics.

#recommendation[
  For CLAIR, use CPL-finite (with product operations), not CPL-Gödel. Accept the
  discretization rather than sacrifice semantic fidelity.
]

#heading(level: 2)["Conservative Over GL": Clarification]

#note[
  #strong[On "Conservative Over GL" Claims.]

  The phrase "CPL is conservative over GL" requires careful definition. Two interpretations:

  1. #strong[Proof-theoretic conservativity]: Every theorem of GL (as formulas with
     implicit confidence 1) is a theorem of CPL. This #strong[holds]: CPL includes
     all GL axioms as special cases.

  2. #strong[Semantic conservativity]: Every model of GL can be embedded in a model
     of CPL. This is #strong[more subtle]: the graded semantics of CPL is fundamentally
     different from classical binary semantics, so direct embedding is non-trivial.

  We assert the first interpretation: CPL extends GL conservatively in the sense that
  all classical GL theorems remain valid in CPL when interpreted as high-confidence
  beliefs. The second interpretation remains an open question.
]

#heading(level: 2)[Design Recommendations for CLAIR]

#heading(level: 3)[The Two-Layer Approach]

CLAIR should implement a two-layer approach to self-reference:

+ #strong[Default: Stratification]. All beliefs are level-indexed.
  $Bel(n, A)$ can only reference $Bel(m, B)$ with $m < n$. This is
  safe by construction and requires no runtime analysis.

+ #strong[Escape hatch: Kripke fixed points]. For legitimate self-reference
  (calibration, uncertainty tracking), use #code[self_ref_belief] which
  computes fixed points at construction time. Ill-formed constructs are
  rejected.

#heading(level: 3)[Hard Bans]

Certain patterns are syntactically rejected:

+ #strong[Curry patterns]: "If [self-reference] then [arbitrary #emph[P]]"
+ #strong[Explicit self-soundness]: Claims of the form "All my beliefs are sound"
+ #strong[Unrestricted quantification]: "For all beliefs #emph[b], ..."

These are detected by the parser and rejected before type checking.

#heading(level: 3)[Type-Level Anti-Bootstrapping]

For type-level confidence checks, use CPL-finite with $L_5$:

```lean
-- Finite confidence for compile-time checks
inductive FiniteConfidence where
  | zero  : FiniteConfidence  -- 0
  | low   : FiniteConfidence  -- 0.25
  | mid   : FiniteConfidence  -- 0.5
  | high  : FiniteConfidence  -- 0.75
  | one   : FiniteConfidence  -- 1

def loebDiscount : FiniteConfidence -> FiniteConfidence
  | .zero => .zero
  | .low  => .zero   -- 0.25^2 = 0.0625 -> floor to 0
  | .mid  => .low    -- 0.5^2  = 0.25
  | .high => .mid    -- 0.75^2 = 0.5625 -> floor to 0.5
  | .one  => .one
```

This provides decidable type-level constraints while preserving the anti-bootstrapping
semantics.

#heading(level: 2)[Related Work]

#heading(level: 3)[Provability Logic]

The foundations of provability logic are in Boolos's work, with the
Solovay completeness theorems establishing the connection to arithmetic. Modern
work on GL extensions includes Beklemishev (2004) on polymodal
variants.

#heading(level: 3)[Self-Reference in AI]

Garrabrant et al. (2016) develop logical inductors
as an approach to coherent self-reference, though in a different formal framework.

#heading(level: 3)[Fuzzy Modal Logic]

Fuzzy extensions of modal logic are surveyed in Godo et al. (2003). Decidability
results for finite-valued logics appear in Bou et al. (2011). The critical
undecidability result for transitive many-valued logics is Vidal (2019).

#heading(level: 2)[Conclusion]

This chapter characterized the landscape of self-reference in CLAIR:

+ #strong[Löb's theorem applies]: Self-soundness claims cannot bootstrap
  epistemic authority. This is a mathematical fact, not a design choice.

+ #strong[Stratification is safe]: Tarski-style level indexing prevents
  all self-referential paradoxes by construction.

+ #strong[Fixed points enable safe self-reference]: Kripke's approach
  permits legitimate introspection (calibration, uncertainty tracking)
  while rejecting ill-formed constructs.

+ #strong[CPL extends GL to graded confidence]: The Graded Löb axiom with
  $g(c) = c^2$ captures anti-bootstrapping for continuous confidence.
  This is a #strong[design axiom] posited as part of CPL, not derived from
  more basic principles. CPL is consistent, as demonstrated by the existence
  of non-trivial models.

+ #strong[Full CPL is likely undecidable]: Transitivity plus continuous
  values enables undecidability (Vidal 2019).

+ #strong[CPL-finite is decidable]: Restricting to discrete confidence
  yields a tractable fragment suitable for type-level checks.

+ #strong[Two-layer design]: Stratification by default, Kripke fixed points
  as escape hatch, hard bans on dangerous patterns.

The Gödelian limits are not obstacles but design constraints. They tell us what
epistemic claims are coherent and which collapse into triviality. By respecting
these limits, CLAIR achieves honest self-awareness: it can reason about its own
reasoning without falling into paradox.

The next chapter turns to epistemological foundations: what grounds CLAIR's
beliefs in the first place.
