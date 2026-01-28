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

import Mathlib.Data.Rat.Init

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

instance (c : ConfBound) : Decidable (c.valid) :=
  inferInstanceAs (Decidable (0 ≤ c ∧ c ≤ 1))

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
  | base   : (b : BaseTy) → WellFormedTy (Ty.base b)
  | fn     : {A B : Ty} → WellFormedTy A → WellFormedTy B → WellFormedTy (Ty.fn A B)
  | prod   : {A B : Ty} → WellFormedTy A → WellFormedTy B → WellFormedTy (Ty.prod A B)
  | sum    : {A B : Ty} → WellFormedTy A → WellFormedTy B → WellFormedTy (Ty.sum A B)
  | belief : {A : Ty} → (c : ConfBound) → WellFormedTy A → ConfBound.valid c → WellFormedTy (Ty.belief A c)
  | meta   : {A : Ty} → (n : Nat) → (c : ConfBound) → WellFormedTy A → ConfBound.valid c → WellFormedTy (Ty.meta A n c)

/-- Well-formedness is decidable -/
@[instance]
def decidableWellFormedTy (ty : Ty) : Decidable (WellFormedTy ty) :=
  match ty with
  | Ty.base b => isTrue (WellFormedTy.base b)
  | Ty.fn A B =>
    match decidableWellFormedTy A, decidableWellFormedTy B with
    | isTrue hA, isTrue hB => isTrue (WellFormedTy.fn hA hB)
    | isTrue hA, isFalse hB => isFalse (fun h => by cases h; contradiction)
    | isFalse hA, _ => isFalse (fun h => by cases h; contradiction)
  | Ty.prod A B =>
    match decidableWellFormedTy A, decidableWellFormedTy B with
    | isTrue hA, isTrue hB => isTrue (WellFormedTy.prod hA hB)
    | isTrue hA, isFalse hB => isFalse (fun h => by cases h; contradiction)
    | isFalse hA, _ => isFalse (fun h => by cases h; contradiction)
  | Ty.sum A B =>
    match decidableWellFormedTy A, decidableWellFormedTy B with
    | isTrue hA, isTrue hB => isTrue (WellFormedTy.sum hA hB)
    | isTrue hA, isFalse hB => isFalse (fun h => by cases h; contradiction)
    | isFalse hA, _ => isFalse (fun h => by cases h; contradiction)
  | Ty.belief A c =>
    match decidableWellFormedTy A with
    | isTrue hA =>
      if hcv : ConfBound.valid c then
        isTrue (WellFormedTy.belief c hA hcv)
      else
        isFalse (fun h => by cases h; contradiction)
    | isFalse hA => isFalse (fun h => by cases h; contradiction)
  | Ty.meta A n c =>
    match decidableWellFormedTy A with
    | isTrue hA =>
      if hcv : ConfBound.valid c then
        isTrue (WellFormedTy.meta n c hA hcv)
      else
        isFalse (fun h => by cases h; contradiction)
    | isFalse hA => isFalse (fun h => by cases h; contradiction)

instance : DecidablePred WellFormedTy := decidableWellFormedTy

end CLAIR.Syntax
