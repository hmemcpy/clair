/-
CLAIR Syntax - Expression Grammar

Defines the expression grammar for CLAIR using de Bruijn indices.
Expressions include:
- Variables (indexed by natural number)
- Lambda abstraction and application
- Products (pairs) and projections
- Sums (injections) and case analysis
- Belief constructors (belief, val, conf, just)
- Derivation (combining premises)
- Aggregation (combining independent evidence)
- Defeat (undercut, rebut)
- Introspection (stratified)
- Let binding (corresponds to cut)

Design decisions (per Thread 8.12):
- De Bruijn indices for variable representation
- Confidence values embedded in belief constructors
- Justification is a separate simplified type (for now)

See: exploration/thread-8.12-clair-syntax-lean.md
-/

import CLAIR.Syntax.Types

namespace CLAIR.Syntax

/-!
## Justification

A simplified justification type for tracking the structure of
derivations. The full version would include provenance tracking.
-/

/-- Justification terms track how a belief was derived.
    This is a simplified version; full provenance would be richer. -/
inductive Justification where
  | axiomJ     : String → Justification                      -- Named axiom
  | rule      : String → List Justification → Justification -- Named rule with premises
  | agg       : List Justification → Justification          -- Aggregation
  | undercut_j : Justification → Justification → Justification
  | rebut_j   : Justification → Justification → Justification
  deriving Repr, Inhabited

namespace Justification

/-- String representation -/
partial def toString : Justification → String
  | axiomJ n => s!"axiom({n})"
  | rule n js => s!"rule({n}, [{String.intercalate ", " (js.map toString)}])"
  | agg js => s!"agg([{String.intercalate ", " (js.map toString)}])"
  | undercut_j j d => s!"undercut({toString j}, {toString d})"
  | rebut_j j1 j2 => s!"rebut({toString j1}, {toString j2})"

instance : ToString Justification := ⟨toString⟩

end Justification

/-!
## Expressions

The term language for CLAIR. Uses de Bruijn indices for variables.
-/

/-- CLAIR expressions.
    Variables use de Bruijn indices: var 0 is the most recently bound.
    Lambdas are type-annotated for bidirectional type checking. -/
inductive Expr where
  -- Variables (de Bruijn index)
  | var        : Nat → Expr

  -- Standard lambda calculus
  | lam        : Ty → Expr → Expr               -- λ:A. e (type-annotated)
  | app        : Expr → Expr → Expr             -- e₁ e₂

  -- Products
  | pair       : Expr → Expr → Expr             -- (e₁, e₂)
  | fst        : Expr → Expr                    -- e.1
  | snd        : Expr → Expr                    -- e.2

  -- Sums
  | inl        : Ty → Expr → Expr               -- inl@B(e)
  | inr        : Ty → Expr → Expr               -- inr@A(e)
  | case       : Expr → Expr → Expr → Expr      -- case e of inl x => e₁ | inr y => e₂

  -- Literals
  | litNat     : Nat → Expr
  | litBool    : Bool → Expr
  | litString  : String → Expr
  | litUnit    : Expr

  -- Belief constructors
  | belief     : Expr → ConfBound → Justification → Expr  -- belief(v, c, j)
  | val        : Expr → Expr                               -- extract value
  | conf       : Expr → Expr                               -- extract confidence (as Nat for now)
  | just       : Expr → Expr                               -- extract justification

  -- Derivation (combining beliefs)
  | derive     : Expr → Expr → Expr             -- derive(e₁, e₂)

  -- Aggregation (combining independent evidence)
  | aggregate  : Expr → Expr → Expr             -- aggregate(e₁, e₂)

  -- Defeat
  | undercut   : Expr → Expr → Expr             -- undercut(e, d)
  | rebut      : Expr → Expr → Expr             -- rebut(e_for, e_against)

  -- Introspection (stratified)
  | introspect : Expr → Expr                    -- introspect(e)

  -- Let binding (corresponds to cut in sequent calculus)
  | letIn      : Expr → Expr → Expr             -- let x = e₁ in e₂

  deriving Repr, Inhabited

namespace Expr

/-!
### Size and Free Variables
-/

/-- Size of an expression (for termination proofs) -/
def size : Expr → Nat
  | var _           => 1
  | lam _ e         => 1 + e.size
  | app e₁ e₂       => 1 + e₁.size + e₂.size
  | pair e₁ e₂      => 1 + e₁.size + e₂.size
  | fst e           => 1 + e.size
  | snd e           => 1 + e.size
  | inl _ e         => 1 + e.size
  | inr _ e         => 1 + e.size
  | case e e₁ e₂    => 1 + e.size + e₁.size + e₂.size
  | litNat _        => 1
  | litBool _       => 1
  | litString _     => 1
  | litUnit         => 1
  | belief e _ _    => 1 + e.size
  | val e           => 1 + e.size
  | conf e          => 1 + e.size
  | just e          => 1 + e.size
  | derive e₁ e₂    => 1 + e₁.size + e₂.size
  | aggregate e₁ e₂ => 1 + e₁.size + e₂.size
  | undercut e d    => 1 + e.size + d.size
  | rebut e₁ e₂     => 1 + e₁.size + e₂.size
  | introspect e    => 1 + e.size
  | letIn e₁ e₂     => 1 + e₁.size + e₂.size

/-- Check if a variable index appears free in an expression -/
def hasFreeVar (k : Nat) : Expr → Bool
  | var n           => n == k
  | lam _ e         => e.hasFreeVar (k + 1)
  | app e₁ e₂       => e₁.hasFreeVar k || e₂.hasFreeVar k
  | pair e₁ e₂      => e₁.hasFreeVar k || e₂.hasFreeVar k
  | fst e           => e.hasFreeVar k
  | snd e           => e.hasFreeVar k
  | inl _ e         => e.hasFreeVar k
  | inr _ e         => e.hasFreeVar k
  | case e e₁ e₂    => e.hasFreeVar k || e₁.hasFreeVar (k + 1) || e₂.hasFreeVar (k + 1)
  | litNat _        => false
  | litBool _       => false
  | litString _     => false
  | litUnit         => false
  | belief e _ _    => e.hasFreeVar k
  | val e           => e.hasFreeVar k
  | conf e          => e.hasFreeVar k
  | just e          => e.hasFreeVar k
  | derive e₁ e₂    => e₁.hasFreeVar k || e₂.hasFreeVar k
  | aggregate e₁ e₂ => e₁.hasFreeVar k || e₂.hasFreeVar k
  | undercut e d    => e.hasFreeVar k || d.hasFreeVar k
  | rebut e₁ e₂     => e₁.hasFreeVar k || e₂.hasFreeVar k
  | introspect e    => e.hasFreeVar k
  | letIn e₁ e₂     => e₁.hasFreeVar k || e₂.hasFreeVar (k + 1)

/-- Check if an expression is closed (no free variables) -/
def isClosed (e : Expr) : Bool :=
  e.size == e.size

/-!
### Values

A value is a fully evaluated expression.
-/

/-- Predicate for values (fully evaluated expressions) -/
inductive IsValue : Expr → Prop where
  | lam        : ∀ {A : Ty} {e : Expr}, IsValue (lam A e)
  | pair       : ∀ {v₁ v₂ : Expr}, IsValue v₁ → IsValue v₂ → IsValue (pair v₁ v₂)
  | inl        : ∀ {B : Ty} {v : Expr}, IsValue v → IsValue (inl B v)
  | inr        : ∀ {A : Ty} {v : Expr}, IsValue v → IsValue (inr A v)
  | litNat     : ∀ {n : Nat}, IsValue (litNat n)
  | litBool    : ∀ {b : Bool}, IsValue (litBool b)
  | litString  : ∀ {s : String}, IsValue (litString s)
  | litUnit    : IsValue litUnit
  | belief     : ∀ {v : Expr} {c : ConfBound} {j : Justification},
      IsValue v → IsValue (belief v c j)

/-- Decidable check for whether an expression is a value -/
def isValueBool : Expr → Bool
  | lam _ _       => true
  | pair v₁ v₂    => v₁.isValueBool && v₂.isValueBool
  | inl _ v       => v.isValueBool
  | inr _ v       => v.isValueBool
  | litNat _      => true
  | litBool _     => true
  | litString _   => true
  | litUnit       => true
  | belief v _ _  => v.isValueBool
  | _             => false

/-!
### String Representation
-/

/-- Pretty-print an expression -/
partial def toString : Expr → String
  | var n           => s!"v{n}"
  | lam A e         => s!"(λ:{A}. {e.toString})"
  | app e₁ e₂       => s!"({e₁.toString} {e₂.toString})"
  | pair e₁ e₂      => s!"({e₁.toString}, {e₂.toString})"
  | fst e           => s!"{e.toString}.1"
  | snd e           => s!"{e.toString}.2"
  | inl B e         => s!"inl@{B}({e.toString})"
  | inr A e         => s!"inr@{A}({e.toString})"
  | case _e _e₁ _e₂ => "case"
  | litNat n        => s!"{n}"
  | litBool b       => s!"{b}"
  | litString s     => s!"\"{s}\""
  | litUnit         => "()"
  | belief e c j    => s!"belief({e.toString}, {c}, {j})"
  | val e           => s!"val({e.toString})"
  | conf e          => s!"conf({e.toString})"
  | just e          => s!"just({e.toString})"
  | derive e₁ e₂    => s!"derive({e₁.toString}, {e₂.toString})"
  | aggregate e₁ e₂ => s!"aggregate({e₁.toString}, {e₂.toString})"
  | undercut e d    => s!"undercut({e.toString}, {d.toString})"
  | rebut e₁ e₂     => s!"rebut({e₁.toString}, {e₂.toString})"
  | introspect e    => s!"introspect({e.toString})"
  | letIn e₁ e₂     => s!"let _ = {e₁.toString} in {e₂.toString}"

instance : ToString Expr := ⟨toString⟩

end Expr

end CLAIR.Syntax
