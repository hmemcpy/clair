/-
CLAIR Syntax - Type Grammar

Defines the type grammar for CLAIR expressions. Types include:
- Base types (Nat, Bool, String, Unit)
- Function types (A → B)
- Product types (A × B)
- Sum types (A + B)
- Belief types (Belief<A>[c] with confidence bound)
- Meta types (Meta<A>[n][c] for stratified introspection)

Design decisions (per Thread 8.12):
- Confidence bounds use ℚ (rationals) for decidable type checking
- Types carry confidence bounds explicitly
- Meta types carry both level and confidence for stratification

See: exploration/thread-8.12-clair-syntax-lean.md
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order

namespace CLAIR.Syntax

/-!
## Confidence Bounds

For the type system, we use rationals rather than reals.
This gives us decidable equality and comparison, essential for
type checking.

The semantic Confidence type (in CLAIR.Confidence) uses ℝ;
we bridge between them when connecting syntax to semantics.
-/

/-- Confidence bounds for the type system.
    Uses rationals for decidability. -/
abbrev ConfBound := ℚ

/-- Check that a confidence bound is valid (in [0,1]) -/
def ConfBound.valid (c : ConfBound) : Prop := 0 ≤ c ∧ c ≤ 1

instance : DecidablePred ConfBound.valid := fun c =>
  And.decidable

/-!
## Base Types

The primitive types that CLAIR supports.
-/

/-- Base types in CLAIR -/
inductive BaseTy where
  | nat    : BaseTy
  | bool   : BaseTy
  | string : BaseTy
  | unit   : BaseTy
  deriving Repr, DecidableEq, Inhabited

namespace BaseTy

/-- String representation for debugging -/
def toString : BaseTy → String
  | nat    => "Nat"
  | bool   => "Bool"
  | string => "String"
  | unit   => "Unit"

instance : ToString BaseTy := ⟨toString⟩

end BaseTy

/-!
## CLAIR Types

The full type grammar for CLAIR.
-/

/-- CLAIR types with confidence bounds.
    Belief<A>[c] represents a belief in a value of type A
    with confidence bound c.
    Meta<A>[n][c] represents a stratified belief at level n. -/
inductive Ty where
  | base   : BaseTy → Ty                        -- Primitive types
  | fn     : Ty → Ty → Ty                       -- Function types: A → B
  | prod   : Ty → Ty → Ty                       -- Product types: A × B
  | sum    : Ty → Ty → Ty                       -- Sum types: A + B
  | belief : Ty → ConfBound → Ty                -- Belief types: Belief<A>[c]
  | meta   : Ty → Nat → ConfBound → Ty          -- Meta types: Meta<A>[n][c]
  deriving Repr, DecidableEq, Inhabited

namespace Ty

/-!
### Type Constructors
-/

/-- Shorthand for Nat type -/
abbrev nat : Ty := base .nat

/-- Shorthand for Bool type -/
abbrev bool : Ty := base .bool

/-- Shorthand for String type -/
abbrev string : Ty := base .string

/-- Shorthand for Unit type -/
abbrev unit : Ty := base .unit

/-- Arrow notation for function types -/
infixr:25 " ⇒ " => fn

/-- Product notation -/
infixl:35 " ⊗ " => prod

/-- Sum notation -/
infixl:30 " ⊕ₜ " => sum

/-!
### Type Properties
-/

/-- Check if a type is a base type -/
def isBase : Ty → Bool
  | base _ => true
  | _      => false

/-- Check if a type is a function type -/
def isFn : Ty → Bool
  | fn _ _ => true
  | _      => false

/-- Check if a type is a belief type -/
def isBelief : Ty → Bool
  | belief _ _ => true
  | _          => false

/-- Check if a type is a meta (stratified belief) type -/
def isMeta : Ty → Bool
  | meta _ _ _ => true
  | _          => false

/-- Extract the content type from a belief type -/
def beliefContent : Ty → Option Ty
  | belief A _ => some A
  | _          => none

/-- Extract the confidence bound from a belief type -/
def beliefConf : Ty → Option ConfBound
  | belief _ c => some c
  | _          => none

/-- Extract the level from a meta type -/
def metaLevel : Ty → Option Nat
  | meta _ n _ => some n
  | _          => none

/-!
### Size and Depth

Used for termination proofs in recursion.
-/

/-- Size of a type (for termination) -/
def size : Ty → Nat
  | base _       => 1
  | fn A B       => 1 + A.size + B.size
  | prod A B     => 1 + A.size + B.size
  | sum A B      => 1 + A.size + B.size
  | belief A _   => 1 + A.size
  | meta A _ _   => 1 + A.size

/-- Depth of a type (maximum nesting) -/
def depth : Ty → Nat
  | base _       => 0
  | fn A B       => 1 + max A.depth B.depth
  | prod A B     => 1 + max A.depth B.depth
  | sum A B      => 1 + max A.depth B.depth
  | belief A _   => 1 + A.depth
  | meta A _ _   => 1 + A.depth

/-!
### String Representation
-/

/-- Pretty-print a type -/
def toString : Ty → String
  | base b       => b.toString
  | fn A B       => s!"({A.toString} → {B.toString})"
  | prod A B     => s!"({A.toString} × {B.toString})"
  | sum A B      => s!"({A.toString} + {B.toString})"
  | belief A c   => s!"Belief<{A.toString}>[{c}]"
  | meta A n c   => s!"Meta<{A.toString}>[{n}][{c}]"

instance : ToString Ty := ⟨toString⟩

end Ty

/-!
## Well-Formedness

A type is well-formed if all confidence bounds are in [0,1].
-/

/-- A type is well-formed if all confidence bounds are valid -/
inductive WellFormedTy : Ty → Prop where
  | base   : WellFormedTy (Ty.base b)
  | fn     : WellFormedTy A → WellFormedTy B → WellFormedTy (Ty.fn A B)
  | prod   : WellFormedTy A → WellFormedTy B → WellFormedTy (Ty.prod A B)
  | sum    : WellFormedTy A → WellFormedTy B → WellFormedTy (Ty.sum A B)
  | belief : WellFormedTy A → c.valid → WellFormedTy (Ty.belief A c)
  | meta   : WellFormedTy A → c.valid → WellFormedTy (Ty.meta A n c)

/-- Well-formedness is decidable -/
instance : DecidablePred WellFormedTy := fun ty => by
  induction ty with
  | base b => exact isTrue WellFormedTy.base
  | fn A B ihA ihB =>
    cases ihA with
    | isTrue hA =>
      cases ihB with
      | isTrue hB => exact isTrue (WellFormedTy.fn hA hB)
      | isFalse hB => exact isFalse (fun h => by cases h; contradiction)
    | isFalse hA => exact isFalse (fun h => by cases h; contradiction)
  | prod A B ihA ihB =>
    cases ihA with
    | isTrue hA =>
      cases ihB with
      | isTrue hB => exact isTrue (WellFormedTy.prod hA hB)
      | isFalse hB => exact isFalse (fun h => by cases h; contradiction)
    | isFalse hA => exact isFalse (fun h => by cases h; contradiction)
  | sum A B ihA ihB =>
    cases ihA with
    | isTrue hA =>
      cases ihB with
      | isTrue hB => exact isTrue (WellFormedTy.sum hA hB)
      | isFalse hB => exact isFalse (fun h => by cases h; contradiction)
    | isFalse hA => exact isFalse (fun h => by cases h; contradiction)
  | belief A c ihA =>
    cases ihA with
    | isTrue hA =>
      cases inferInstance : (c.valid).decide with
      | true h =>
        have hc : c.valid := of_decide_eq_true h
        exact isTrue (WellFormedTy.belief hA hc)
      | false h =>
        have hc : ¬c.valid := of_decide_eq_false h
        exact isFalse (fun h => by cases h; contradiction)
    | isFalse hA => exact isFalse (fun h => by cases h; contradiction)
  | meta A n c ihA =>
    cases ihA with
    | isTrue hA =>
      cases inferInstance : (c.valid).decide with
      | true h =>
        have hc : c.valid := of_decide_eq_true h
        exact isTrue (WellFormedTy.meta hA hc)
      | false h =>
        have hc : ¬c.valid := of_decide_eq_false h
        exact isFalse (fun h => by cases h; contradiction)
    | isFalse hA => exact isFalse (fun h => by cases h; contradiction)

end CLAIR.Syntax
