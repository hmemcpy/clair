/-
CLAIR Syntax - Substitution

Implements substitution for de Bruijn indexed expressions.
This requires careful index shifting to maintain correct references.

The key operations are:
- shift: Adjust indices when entering/leaving binders
- subst: Replace a variable with an expression

See: exploration/thread-8.12-clair-syntax-lean.md
-/

import CLAIR.Syntax.Expr

namespace CLAIR.Syntax

namespace Expr

/-!
## Index Shifting

When substituting under a binder, we need to shift the indices
in the substituted term to account for the new binding.

shift d c e: Add d to all indices ≥ c in e
- d is the shift amount (can be negative conceptually, but we use Nat)
- c is the cutoff (indices below c are local to inner binders)
-/

/-- Shift free variable indices by d, starting from cutoff c.
    Indices < c are considered bound locally and not shifted.
    Indices ≥ c are free and shifted by d. -/
def shift (d : Nat) (cutoff : Nat) : Expr → Expr
  | var n           =>
      if n < cutoff then var n else var (n + d)
  | lam A e         => lam A (shift d (cutoff + 1) e)
  | app e₁ e₂       => app (shift d cutoff e₁) (shift d cutoff e₂)
  | pair e₁ e₂      => pair (shift d cutoff e₁) (shift d cutoff e₂)
  | fst e           => fst (shift d cutoff e)
  | snd e           => snd (shift d cutoff e)
  | inl B e         => inl B (shift d cutoff e)
  | inr A e         => inr A (shift d cutoff e)
  | case e e₁ e₂    => Expr.case (shift d cutoff e) (shift d (cutoff + 1) e₁) (shift d (cutoff + 1) e₂)
  | litNat n        => litNat n
  | litBool b       => litBool b
  | litString s     => litString s
  | litUnit         => litUnit
  | belief e cb j => Expr.belief (shift d cutoff e) cb j
  | val e           => val (shift d cutoff e)
  | conf e          => conf (shift d cutoff e)
  | just e          => just (shift d cutoff e)
  | derive e₁ e₂    => derive (shift d cutoff e₁) (shift d cutoff e₂)
  | aggregate e₁ e₂ => aggregate (shift d cutoff e₁) (shift d cutoff e₂)
  | undercut e e'   => undercut (shift d cutoff e) (shift d cutoff e')
  | rebut e₁ e₂     => rebut (shift d cutoff e₁) (shift d cutoff e₂)
  | introspect e    => introspect (shift d cutoff e)
  | letIn e₁ e₂     => letIn (shift d cutoff e₁) (shift d (cutoff + 1) e₂)

/-- Shift all free variables (cutoff = 0) -/
abbrev shiftFree (d : Nat) : Expr → Expr := shift d 0

/-!
## Substitution

subst k s e: Replace variable k with expression s in e

Key insight: When we go under a binder:
1. Increment k (the target variable is now one level deeper)
2. Shift s (its free variables need to account for the new binder)
-/

/-- Substitute expression s for variable index k in expression e.
    subst k s e = e[k := s] -/
def subst (k : Nat) (s : Expr) : Expr → Expr
  | var n           =>
      if n < k then var n           -- Bound above the target
      else if n = k then s          -- Found the target
      else var (n - 1)              -- Bound below, shift down
  | lam A e         =>
      -- Under the binder: target is k+1, shift s to account for new binding
      lam A (subst (k + 1) (shiftFree 1 s) e)
  | app e₁ e₂       => app (subst k s e₁) (subst k s e₂)
  | pair e₁ e₂      => pair (subst k s e₁) (subst k s e₂)
  | fst e           => fst (subst k s e)
  | snd e           => snd (subst k s e)
  | inl B e         => inl B (subst k s e)
  | inr A e         => inr A (subst k s e)
  | case e e₁ e₂    =>
      Expr.case (subst k s e)
        (subst (k + 1) (shiftFree 1 s) e₁)
        (subst (k + 1) (shiftFree 1 s) e₂)
  | litNat n        => litNat n
  | litBool b       => litBool b
  | litString str   => litString str
  | litUnit         => litUnit
  | belief e c j    => Expr.belief (subst k s e) c j
  | val e           => val (subst k s e)
  | conf e          => conf (subst k s e)
  | just e          => just (subst k s e)
  | derive e₁ e₂    => derive (subst k s e₁) (subst k s e₂)
  | aggregate e₁ e₂ => aggregate (subst k s e₁) (subst k s e₂)
  | undercut e d    => undercut (subst k s e) (subst k s d)
  | rebut e₁ e₂     => rebut (subst k s e₁) (subst k s e₂)
  | introspect e    => introspect (subst k s e)
  | letIn e₁ e₂     =>
      letIn (subst k s e₁) (subst (k + 1) (shiftFree 1 s) e₂)

/-- Substitute for variable 0 (the common case for beta reduction) -/
abbrev subst0 (s : Expr) : Expr → Expr := subst 0 s

/-!
## Substitution Lemmas

These lemmas are essential for proving type preservation.
-/

/-- Shifting by 0 is identity -/
theorem shift_zero (c : Nat) (e : Expr) : shift 0 c e = e := by
  sorry

/-- Values are preserved by shifting -/
theorem shift_preserves_value (d c : Nat) (e : Expr) :
    IsValue e → IsValue (shift d c e) := by
  sorry

/-- Substituting in a value preserves being a value -/
theorem subst_preserves_value (k : Nat) (s : Expr) (e : Expr) :
    IsValue e → IsValue (subst k s e) := by
  sorry

end Expr

end CLAIR.Syntax
