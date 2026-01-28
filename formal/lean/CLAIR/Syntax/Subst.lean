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
def shift (d : Nat) (c : Nat) : Expr → Expr
  | var n           =>
      if n < c then var n else var (n + d)
  | lam A e         => lam A (shift d (c + 1) e)
  | app e₁ e₂       => app (shift d c e₁) (shift d c e₂)
  | pair e₁ e₂      => pair (shift d c e₁) (shift d c e₂)
  | fst e           => fst (shift d c e)
  | snd e           => snd (shift d c e)
  | inl B e         => inl B (shift d c e)
  | inr A e         => inr A (shift d c e)
  | case e e₁ e₂    => case (shift d c e) (shift d (c + 1) e₁) (shift d (c + 1) e₂)
  | litNat n        => litNat n
  | litBool b       => litBool b
  | litString s     => litString s
  | litUnit         => litUnit
  | belief e conf j => belief (shift d c e) conf j
  | val e           => val (shift d c e)
  | conf e          => conf (shift d c e)
  | just e          => just (shift d c e)
  | derive e₁ e₂    => derive (shift d c e₁) (shift d c e₂)
  | aggregate e₁ e₂ => aggregate (shift d c e₁) (shift d c e₂)
  | undercut e e'   => undercut (shift d c e) (shift d c e')
  | rebut e₁ e₂     => rebut (shift d c e₁) (shift d c e₂)
  | introspect e    => introspect (shift d c e)
  | letIn e₁ e₂     => letIn (shift d c e₁) (shift d (c + 1) e₂)

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
      case (subst k s e)
           (subst (k + 1) (shiftFree 1 s) e₁)
           (subst (k + 1) (shiftFree 1 s) e₂)
  | litNat n        => litNat n
  | litBool b       => litBool b
  | litString str   => litString str
  | litUnit         => litUnit
  | belief e c j    => belief (subst k s e) c j
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
  induction e generalizing c with
  | var n =>
    simp only [shift]
    split_ifs <;> simp
  | lam A e ih =>
    simp only [shift]
    congr 1
    exact ih (c + 1)
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [shift]
    congr 1 <;> apply_assumption
  | pair e₁ e₂ ih₁ ih₂ =>
    simp only [shift]
    congr 1 <;> apply_assumption
  | fst e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | snd e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | inl B e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | inr A e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | case e e₁ e₂ ih ih₁ ih₂ =>
    simp only [shift]
    congr 1
    · exact ih c
    · exact ih₁ (c + 1)
    · exact ih₂ (c + 1)
  | litNat _ => rfl
  | litBool _ => rfl
  | litString _ => rfl
  | litUnit => rfl
  | belief e _ _ ih =>
    simp only [shift]
    congr 1
    exact ih c
  | val e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | conf e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | just e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | derive e₁ e₂ ih₁ ih₂ =>
    simp only [shift]
    congr 1 <;> apply_assumption
  | aggregate e₁ e₂ ih₁ ih₂ =>
    simp only [shift]
    congr 1 <;> apply_assumption
  | undercut e d ih₁ ih₂ =>
    simp only [shift]
    congr 1 <;> apply_assumption
  | rebut e₁ e₂ ih₁ ih₂ =>
    simp only [shift]
    congr 1 <;> apply_assumption
  | introspect e ih =>
    simp only [shift]
    congr 1
    exact ih c
  | letIn e₁ e₂ ih₁ ih₂ =>
    simp only [shift]
    congr 1
    · exact ih₁ c
    · exact ih₂ (c + 1)

/-- Values are preserved by shifting -/
theorem shift_preserves_value (d c : Nat) (e : Expr) :
    IsValue e → IsValue (shift d c e) := by
  intro hv
  induction hv generalizing c with
  | lam => constructor
  | pair _ _ ih₁ ih₂ =>
    constructor
    · exact ih₁ c
    · exact ih₂ c
  | inl _ ih => constructor; exact ih c
  | inr _ ih => constructor; exact ih c
  | litNat => constructor
  | litBool => constructor
  | litString => constructor
  | litUnit => constructor
  | belief _ ih =>
    constructor
    exact ih c

/-- Substituting in a value preserves being a value -/
theorem subst_preserves_value (k : Nat) (s : Expr) (e : Expr) :
    IsValue e → IsValue (subst k s e) := by
  intro hv
  induction hv generalizing k with
  | lam => constructor
  | pair _ _ ih₁ ih₂ =>
    constructor
    · exact ih₁ k
    · exact ih₂ k
  | inl _ ih => constructor; exact ih k
  | inr _ ih => constructor; exact ih k
  | litNat => constructor
  | litBool => constructor
  | litString => constructor
  | litUnit => constructor
  | belief _ ih =>
    constructor
    exact ih k

end Expr

end CLAIR.Syntax
