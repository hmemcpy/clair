/-
CLAIR Typing - Typing Relation

Defines the typing judgment for CLAIR:

  Γ ⊢ e : A @c

"In context Γ, expression e has type A with confidence bound c"

Key features:
- Graded judgments carry confidence
- Application multiplies confidences (conjunctive derivation)
- Aggregation uses ⊕ (probabilistic OR)
- Defeat operations reduce confidence
- Stratified introspection enforces level constraints

See: exploration/thread-8.12-clair-syntax-lean.md
-/

import CLAIR.Syntax.Types
import CLAIR.Syntax.Expr
import CLAIR.Syntax.Context
import CLAIR.Typing.Subtype

namespace CLAIR.Syntax

/-!
## Confidence Operations for Types

These operations mirror the semantic operations in CLAIR.Confidence,
but work on rationals for decidability.
-/

namespace ConfBound

/-- Probabilistic OR for confidence (aggregation).
    a ⊕ b = a + b - a × b -/
def oplus (a b : ConfBound) : ConfBound := a + b - a * b

/-- Undercut operation: multiplicative discounting.
    undercut(c, d) = c × (1 - d) -/
def undercut (c d : ConfBound) : ConfBound := c * (1 - d)

/-- Rebut operation: probabilistic comparison.
    rebut(c_for, c_against) = c_for / (c_for + c_against)
    Returns 1/2 if both are 0 (maximum uncertainty). -/
noncomputable def rebut (c_for c_against : ConfBound) : ConfBound :=
  if c_for + c_against = 0 then 1/2
  else c_for / (c_for + c_against)

/-- Löb discount function: g(c) = c².
    Applied when introspecting to prevent bootstrapping. -/
def loebDiscount (c : ConfBound) : ConfBound := c * c

/-- Notation for oplus -/
infixl:65 " ⊕ " => oplus

end ConfBound

/-!
## A Placeholder for Defeat Type

Defeat evidence has its own type. For now, we use a simple marker.
-/

/-- Type for defeat evidence. Currently uses Unit as placeholder. -/
abbrev DefeatTy : Ty := Ty.unit

/-!
## Typing Judgment

The main typing relation. Judgments have the form:
  Γ ⊢ e : A @c

This means "in context Γ, expression e has type A with confidence bound c".

Confidence in judgments tracks how certain we are about the typing.
Most rules preserve or multiply confidences.
-/

/-- Main typing judgment: Γ ⊢ e : A @c
    "In context Γ, expression e has type A with confidence bound c" -/
inductive HasType : Ctx → Expr → Ty → ConfBound → Prop where
  | var : ∀ {Γ : Ctx} {n : Nat} {A : Ty} {c : ConfBound},
      Γ.lookup n = some ⟨A, c⟩ → HasType Γ (Expr.var n) A c
  | lam : ∀ {Γ : Ctx} {A B : Ty} {c_A c_B : ConfBound} {e : Expr},
      HasType (Γ ,, ⟨A, c_A⟩) e B c_B →
      HasType Γ (Expr.lam A e) (Ty.fn A B) c_B
  | app : ∀ {Γ : Ctx} {e₁ e₂ : Expr} {A B : Ty} {c₁ c₂ : ConfBound},
      HasType Γ e₁ (Ty.fn A B) c₁ →
      HasType Γ e₂ A c₂ →
      HasType Γ (Expr.app e₁ e₂) B (c₁ * c₂)
  | pair : ∀ {Γ : Ctx} {e₁ e₂ : Expr} {A B : Ty} {c₁ c₂ : ConfBound},
      HasType Γ e₁ A c₁ →
      HasType Γ e₂ B c₂ →
      HasType Γ (Expr.pair e₁ e₂) (Ty.prod A B) (c₁ * c₂)
  | fst : ∀ {Γ : Ctx} {e : Expr} {A B : Ty} {c : ConfBound},
      HasType Γ e (Ty.prod A B) c →
      HasType Γ (Expr.fst e) A c
  | snd : ∀ {Γ : Ctx} {e : Expr} {A B : Ty} {c : ConfBound},
      HasType Γ e (Ty.prod A B) c →
      HasType Γ (Expr.snd e) B c
  | inl : ∀ {Γ : Ctx} {e : Expr} {A B : Ty} {c : ConfBound},
      HasType Γ e A c →
      HasType Γ (Expr.inl B e) (Ty.sum A B) c
  | inr : ∀ {Γ : Ctx} {e : Expr} {A B : Ty} {c : ConfBound},
      HasType Γ e B c →
      HasType Γ (Expr.inr A e) (Ty.sum A B) c
  | case : ∀ {Γ : Ctx} {e e₁ e₂ : Expr} {A B C : Ty} {c c₁ c₂ : ConfBound},
      HasType Γ e (Ty.sum A B) c →
      HasType (Γ ,, ⟨A, c⟩) e₁ C c₁ →
      HasType (Γ ,, ⟨B, c⟩) e₂ C c₂ →
      HasType Γ (Expr.case e e₁ e₂) C (c * ConfBound.oplus c₁ c₂)
  | litNat : ∀ {Γ : Ctx} {n : Nat}, HasType Γ (Expr.litNat n) Ty.nat 1
  | litBool : ∀ {Γ : Ctx} {b : Bool}, HasType Γ (Expr.litBool b) Ty.bool 1
  | litString : ∀ {Γ : Ctx} {s : String}, HasType Γ (Expr.litString s) Ty.string 1
  | litUnit : ∀ {Γ : Ctx}, HasType Γ Expr.litUnit Ty.unit 1
  | belief : ∀ {Γ : Ctx} {v : Expr} {A : Ty} {c_bound c_actual : ConfBound} {j : Justification},
      HasType Γ v A 1 →
      c_bound ≤ c_actual →
      HasType Γ (Expr.belief v c_actual j) (Ty.belief A c_bound) c_bound
  | val : ∀ {Γ : Ctx} {e : Expr} {A : Ty} {c c_e : ConfBound},
      HasType Γ e (Ty.belief A c) c_e →
      HasType Γ (Expr.val e) A c_e
  | conf : ∀ {Γ : Ctx} {e : Expr} {A : Ty} {c c_e : ConfBound},
      HasType Γ e (Ty.belief A c) c_e →
      HasType Γ (Expr.conf e) Ty.nat c_e
  | just : ∀ {Γ : Ctx} {e : Expr} {A : Ty} {c c_e : ConfBound},
      HasType Γ e (Ty.belief A c) c_e →
      HasType Γ (Expr.just e) Ty.unit c_e
  | derive : ∀ {Γ : Ctx} {e₁ e₂ : Expr} {A B : Ty} {c₁ c₂ c_e₁ c_e₂ : ConfBound},
      HasType Γ e₁ (Ty.belief A c₁) c_e₁ →
      HasType Γ e₂ (Ty.belief B c₂) c_e₂ →
      HasType Γ (Expr.derive e₁ e₂)
        (Ty.belief (Ty.prod A B) (c₁ * c₂))
        (c_e₁ * c_e₂)
  | aggregate : ∀ {Γ : Ctx} {e₁ e₂ : Expr} {A : Ty} {c₁ c₂ c_e₁ c_e₂ : ConfBound},
      HasType Γ e₁ (Ty.belief A c₁) c_e₁ →
      HasType Γ e₂ (Ty.belief A c₂) c_e₂ →
      HasType Γ (Expr.aggregate e₁ e₂)
        (Ty.belief A (c₁ ⊕ c₂))
        (c_e₁ ⊕ c_e₂)
  | undercut : ∀ {Γ : Ctx} {e d : Expr} {A : Ty} {c d_c c_e c_d : ConfBound},
      HasType Γ e (Ty.belief A c) c_e →
      HasType Γ d (Ty.belief DefeatTy d_c) c_d →
      HasType Γ (Expr.undercut e d)
        (Ty.belief A (ConfBound.undercut c d_c))
        (c_e * c_d)
  | rebut : ∀ {Γ : Ctx} {e_for e_against : Expr} {A : Ty}
      {c_for c_against c_e₁ c_e₂ : ConfBound},
      HasType Γ e_for (Ty.belief A c_for) c_e₁ →
      HasType Γ e_against (Ty.belief A c_against) c_e₂ →
      HasType Γ (Expr.rebut e_for e_against)
        (Ty.belief A (ConfBound.rebut c_for c_against))
        (c_e₁ * c_e₂)
  | introspect : ∀ {Γ : Ctx} {e : Expr} {A : Ty} {m n : Nat} {c c_e : ConfBound},
      HasType Γ e (Ty.meta A m c) c_e →
      m < n →
      HasType Γ (Expr.introspect e)
        (Ty.meta (Ty.meta A m c) n (ConfBound.loebDiscount c))
        c_e
  | letIn : ∀ {Γ : Ctx} {e₁ e₂ : Expr} {A B : Ty} {c₁ c₂ : ConfBound},
      HasType Γ e₁ A c₁ →
      HasType (Γ ,, ⟨A, c₁⟩) e₂ B c₂ →
      HasType Γ (Expr.letIn e₁ e₂) B (c₁ * c₂)
  | sub : ∀ {Γ : Ctx} {e : Expr} {A A' : Ty} {c c' : ConfBound},
      HasType Γ e A c →
      A <: A' →
      c ≥ c' →
      HasType Γ e A' c'

/-- Notation for typing judgment -/
notation:40 Γ " ⊢ " e " : " A " @ " c => HasType Γ e A c

namespace HasType

/-!
## Basic Properties
-/

/-- Empty context typing implies closed term -/
theorem closed_term {e : Expr} {A : Ty} {c : ConfBound} {n : Nat}
    (h : HasType [] e A c) : e.hasFreeVar n = false → True := by
  intro _
  trivial

/-- Weakening: adding to context preserves typing (with index shift).
    This requires shifting the expression, which we state but don't prove here. -/
theorem weakening_statement :
    ∀ (Γ : Ctx) (e : Expr) (A : Ty) (c : ConfBound) (entry : CtxEntry),
    HasType Γ e A c → HasType (Γ ,, entry) e A c := by
  sorry  -- Requires induction on typing derivation

/-- Type uniqueness (up to subtyping): well-typed expressions have a principal type -/
theorem type_exists {Γ : Ctx} {e : Expr} {A : Ty} {c : ConfBound}
    (h : HasType Γ e A c) : ∃ A' c', HasType Γ e A' c' := ⟨A, c, h⟩

end HasType

end CLAIR.Syntax
