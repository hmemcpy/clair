/-
CLAIR Justification DAG - Directed Acyclic Graph of Beliefs

A CLAIR document is a DAG of beliefs where:
- Each belief can have multiple justifications (backward edges)
- The graph must be acyclic (no belief can justify itself transitively)
- All beliefs are grounded (can trace back to axioms)

This module formalizes these structural properties.

Key properties:
- Acyclicity: ∀ b, ¬ reachable b b
- Grounding: ∀ b, ∃ path to axiom
- Well-foundedness: Justification relation is well-founded

Created: 2026-01-29
See: formal/clair-spec.md
     notes/exploration-2026-01-29-minimal-spec.md
-/

import CLAIR.Confidence.Basic
import CLAIR.Belief.Basic

namespace CLAIR

/-!
## Belief Identifier

Each belief in a CLAIR document has a unique identifier.
-/

/-- Unique identifier for a belief in a CLAIR document -/
structure BeliefId where
  id : String
  deriving DecidableEq, Repr

/-!
## Provenance (Source)

Where a belief came from.
-/

/-- Source of a belief -/
inductive Source where
  | user : Source                    -- From user input
  | self : Source                    -- Derived by reasoning
  | file : String → Source           -- From a specific file
  | model : String → Source          -- From a specific model
  | ctx : Source                     -- From context
  deriving DecidableEq, Repr

/-!
## Justification Edge

An edge in the justification DAG.
-/

/-- A justification edge points from a conclusion to its supporting premise -/
structure JustificationEdge where
  premise : BeliefId
  deriving DecidableEq, Repr

/-!
## Invalidation Condition

Conditions under which a belief should be reconsidered.
-/

/-- A condition that would invalidate a belief -/
structure InvalidationCondition where
  condition : String
  deriving DecidableEq, Repr

/-!
## CLAIR Belief Node

A node in the CLAIR DAG, representing a single belief.
-/

/-- A belief node in the CLAIR DAG -/
structure BeliefNode where
  /-- Unique identifier -/
  id : BeliefId
  /-- Confidence in [0,1] -/
  confidence : Confidence
  /-- Stratification level -/
  level : Nat
  /-- Source/provenance -/
  source : Source
  /-- Justifications (backward edges to supporting beliefs) -/
  justifications : List JustificationEdge
  /-- Invalidation conditions -/
  invalidations : List InvalidationCondition
  /-- Content (opaque natural language string) -/
  content : String

namespace BeliefNode

/-- Check if a belief is an axiom (no justifications) -/
def isAxiom (b : BeliefNode) : Bool :=
  b.justifications.isEmpty

/-- Get the IDs of all premises that justify this belief -/
def premiseIds (b : BeliefNode) : List BeliefId :=
  b.justifications.map (·.premise)

end BeliefNode

/-!
## CLAIR Document (DAG)

A CLAIR document is a collection of belief nodes forming a DAG.
-/

/-- A CLAIR document: a DAG of beliefs -/
structure CLAIRDocument where
  /-- All belief nodes, keyed by ID -/
  nodes : List BeliefNode
  /-- All referenced IDs must exist -/
  valid_refs : ∀ b ∈ nodes, ∀ e ∈ b.justifications,
    ∃ premise ∈ nodes, premise.id = e.premise

namespace CLAIRDocument

/-- Get a belief by ID -/
def getNode (doc : CLAIRDocument) (id : BeliefId) : Option BeliefNode :=
  doc.nodes.find? (·.id == id)

/-- Get all axioms (beliefs with no justifications) -/
def axioms (doc : CLAIRDocument) : List BeliefNode :=
  doc.nodes.filter BeliefNode.isAxiom

/-- Check if an ID exists in the document -/
def hasId (doc : CLAIRDocument) (id : BeliefId) : Bool :=
  doc.nodes.any (·.id == id)

end CLAIRDocument

/-!
## Reachability

Define reachability in the justification graph.
A belief b is reachable from a if there is a path of justification edges.
-/

/-- One-step reachability: b directly justifies a -/
def justifies (doc : CLAIRDocument) (premise conclusion : BeliefId) : Prop :=
  ∃ b ∈ doc.nodes, b.id = conclusion ∧
    ∃ e ∈ b.justifications, e.premise = premise

/-- Transitive closure: reachable via chain of justifications -/
inductive Reachable (doc : CLAIRDocument) : BeliefId → BeliefId → Prop where
  | step : ∀ {a b : BeliefId}, justifies doc a b → Reachable doc a b
  | trans : ∀ {a b c : BeliefId}, Reachable doc a b → Reachable doc b c → Reachable doc a c

/-!
## Acyclicity

A CLAIR document is acyclic if no belief is reachable from itself.
-/

/-- A CLAIR document is acyclic -/
def Acyclic (doc : CLAIRDocument) : Prop :=
  ∀ b : BeliefId, ¬ Reachable doc b b

/-!
## Well-Foundedness

The justification relation should be well-founded.
This means every descending chain eventually reaches an axiom.
-/

/-- The "is justified by" relation -/
def isJustifiedBy (doc : CLAIRDocument) (a b : BeliefId) : Prop :=
  justifies doc b a

/-- A document is well-founded if the justification relation is well-founded -/
def WellFoundedJustification (doc : CLAIRDocument) : Prop :=
  WellFounded (isJustifiedBy doc)

/-!
## Grounding

Every belief should be grounded: traceable back to axioms.
-/

/-- A belief is grounded if it is either an axiom or all its premises are grounded -/
inductive Grounded (doc : CLAIRDocument) : BeliefId → Prop where
  | axiom : ∀ (id : BeliefId) (b : BeliefNode), b ∈ doc.nodes → b.id = id →
      b.isAxiom = true → Grounded doc id
  | derived : ∀ (id : BeliefId) (b : BeliefNode), b ∈ doc.nodes → b.id = id →
      (∀ e ∈ b.justifications, Grounded doc e.premise) →
      Grounded doc id

/-- A document is fully grounded if all beliefs are grounded -/
def FullyGrounded (doc : CLAIRDocument) : Prop :=
  ∀ b ∈ doc.nodes, Grounded doc b.id

/-!
## Key Theorems
-/

/-- Acyclic documents have well-founded justification.
    (Proof sketch: acyclicity implies no infinite descending chains) -/
theorem acyclic_implies_wellFounded (doc : CLAIRDocument) (h : Acyclic doc) :
    WellFoundedJustification doc := by
  sorry  -- Full proof requires more infrastructure

/-- Well-founded + non-empty axioms implies grounded.
    (Proof sketch: well-founded induction from axioms) -/
theorem wellFounded_axioms_implies_grounded (doc : CLAIRDocument)
    (hwf : WellFoundedJustification doc)
    (hax : doc.axioms.length > 0) :
    FullyGrounded doc := by
  sorry  -- Full proof requires more infrastructure

/-!
## Valid CLAIR Document

A valid CLAIR document satisfies all structural properties.
-/

/-- A valid CLAIR document is acyclic and fully grounded -/
structure ValidCLAIRDocument extends CLAIRDocument where
  acyclic : Acyclic toCLAIRDocument
  grounded : FullyGrounded toCLAIRDocument

/-!
## Construction Helpers
-/

/-- Create an axiom belief (no justifications) -/
def mkAxiom (id : String) (conf : Confidence) (level : Nat)
    (source : Source) (content : String) : BeliefNode :=
  { id := ⟨id⟩
    confidence := conf
    level := level
    source := source
    justifications := []
    invalidations := []
    content := content }

/-- Create a derived belief with justifications -/
def mkDerived (id : String) (conf : Confidence) (level : Nat)
    (source : Source) (premises : List String) (content : String) : BeliefNode :=
  { id := ⟨id⟩
    confidence := conf
    level := level
    source := source
    justifications := premises.map (fun p => ⟨⟨p⟩⟩)
    invalidations := []
    content := content }

end CLAIR
