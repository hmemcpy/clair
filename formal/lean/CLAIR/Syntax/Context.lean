/-
CLAIR Syntax - Typing Contexts

Defines typing contexts for CLAIR. A context is a list of
type-confidence pairs representing the assumptions in scope.

With de Bruijn indices, the most recently bound variable
is at position 0, so contexts are lists where the head is
the most recent binding.

See: exploration/thread-8.12-clair-syntax-lean.md
-/

import CLAIR.Syntax.Types

namespace CLAIR.Syntax

/-!
## Context Entries

Each entry in a context records a type and a confidence bound
for a variable.
-/

/-- A context entry: a type with a confidence bound.
    Represents an assumption like "x : Belief<A>[c]" -/
structure CtxEntry where
  ty   : Ty
  conf : ConfBound
  deriving Repr, DecidableEq, Inhabited

namespace CtxEntry

/-- Create an entry with full confidence -/
def withFullConf (ty : Ty) : CtxEntry := ⟨ty, 1⟩

/-- Create an entry for a non-belief type (confidence 1) -/
def plain (ty : Ty) : CtxEntry := ⟨ty, 1⟩

/-- String representation -/
def toString (e : CtxEntry) : String :=
  if e.conf = 1 then
    s!"{e.ty}"
  else
    s!"{e.ty} @{e.conf}"

instance : ToString CtxEntry := ⟨toString⟩

end CtxEntry

/-!
## Typing Contexts

A context is a list of entries. With de Bruijn indices:
- Position 0 is the most recently bound variable
- Position n corresponds to variable (var n)
-/

/-- A typing context is a list of entries.
    De Bruijn: head = most recent binding, accessed by var 0 -/
abbrev Ctx := List CtxEntry

namespace Ctx

/-- The empty context -/
def empty : Ctx := []

/-- Extend context with a new binding (becomes var 0) -/
def extend (Γ : Ctx) (entry : CtxEntry) : Ctx := entry :: Γ

/-- Notation for context extension -/
infixl:60 " ,, " => extend

/-- Look up a variable by de Bruijn index -/
def lookup (Γ : Ctx) (n : Nat) : Option CtxEntry :=
  Γ.get? n

/-!
### Length and Indices
-/

/-- Check if an index is valid for this context -/
def validIndex (Γ : Ctx) (n : Nat) : Prop := n < Γ.length

instance (Γ : Ctx) (n : Nat) : Decidable (Γ.validIndex n) :=
  Nat.decLt n Γ.length

/-- Get entry at index (with proof it exists) -/
def getEntry (Γ : Ctx) (n : Nat) (h : n < Γ.length) : CtxEntry :=
  Γ.get ⟨n, h⟩

/-!
### Context Theorems
-/

/-- Lookup in extended context at 0 returns the new entry -/
theorem lookup_extend_zero (Γ : Ctx) (e : CtxEntry) :
    (Γ ,, e).lookup 0 = some e := rfl

/-- Lookup in extended context at n+1 shifts to lookup at n -/
theorem lookup_extend_succ (Γ : Ctx) (e : CtxEntry) (n : Nat) :
    (Γ ,, e).lookup (n + 1) = Γ.lookup n := rfl

/-- Length of extended context -/
theorem length_extend (Γ : Ctx) (e : CtxEntry) :
    (Γ ,, e).length = Γ.length + 1 := rfl

/-- Valid index in extended context at 0 -/
theorem validIndex_extend_zero (Γ : Ctx) (e : CtxEntry) :
    0 < (Γ ,, e).length := Nat.zero_lt_succ _

/-- Valid index in extended context at n+1 iff valid at n in original -/
theorem validIndex_extend_succ (Γ : Ctx) (e : CtxEntry) (n : Nat) :
    n + 1 < (Γ ,, e).length ↔ n < Γ.length := by
  simp [length_extend, Nat.succ_lt_succ_iff]

/-!
### Well-Formed Contexts
-/

/-- A context is well-formed if all entries have valid confidence bounds -/
def WellFormed : Ctx → Prop
  | []      => True
  | e :: Γ  => ConfBound.valid e.conf ∧ WellFormed Γ

/-- Well-formedness is decidable -/
noncomputable instance : DecidablePred WellFormed := by
  intro _
  classical
  infer_instance

/-- Empty context is well-formed -/
theorem wellFormed_empty : WellFormed empty := trivial

/-- Extending with valid entry preserves well-formedness -/
theorem wellFormed_extend {Γ : Ctx} {e : CtxEntry}
    (hΓ : WellFormed Γ) (he : ConfBound.valid e.conf) : WellFormed (Γ ,, e) :=
  ⟨he, hΓ⟩

/-!
### String Representation
-/

/-- Pretty-print a context -/
def toString (Γ : Ctx) : String :=
  if Γ.isEmpty then
    "·"
  else
    let entries := Γ.enum.reverse.map fun ⟨i, e⟩ => s!"v{i} : {e}"
    String.intercalate ", " entries

instance : ToString Ctx := ⟨toString⟩

end Ctx

end CLAIR.Syntax
