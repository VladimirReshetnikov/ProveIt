import ConciseIPRA.PR

/-!
# Finite relational presentations, viability, and shrinking targets

Variable order is fixed throughout:
* `good`: candidate, precision, parameters;
* `edge`: next candidate, current candidate, precision, parameters.
The object implementation uses rectangular bounded tables and a reverse loop.
-/

namespace LeanProofs.ConciseIPRA.PFIG.Relation

open Syn
open scoped Fm

/-- A finite relation at each precision. -/
structure RelPresentation (n : Nat) where
  candBound : PTm (n + 1)       -- precision, parameters
  good : Fm PTm (n + 2)         -- candidate, precision, parameters
  edge : Fm PTm (n + 3)         -- next, current, precision, parameters
  goodQF : good.QF
  edgeQF : edge.QF

namespace RelPresentation

/-- Instantiate the goodness relation. -/
def goodAt {n m : Nat} (R : RelPresentation n)
    (candidate precision : PTm m) (params : Fin n → PTm m) : Fm PTm m :=
  R.good.subst (Fin.cases candidate (Fin.cases precision params))

/-- Instantiate the edge relation. -/
def edgeAt {n m : Nat} (R : RelPresentation n)
    (next current precision : PTm m) (params : Fin n → PTm m) : Fm PTm m :=
  R.edge.subst
    (Fin.cases next (Fin.cases current (Fin.cases precision params)))

end RelPresentation

/-- Semantic finite tower used to validate the dynamic program independently
of object syntax. -/
structure FiniteTower where
  levels : List (List Nat)
  edge : Nat → Nat → Nat → Prop
  edgeDecidable : ∀ i a b, Decidable (edge i a b)

/-- A finite path is represented by a list whose index is the level. -/
def FiniteTower.Path (T : FiniteTower) (xs : List Nat) : Prop :=
  xs.length = T.levels.length ∧
  (∀ i, (hi : i < xs.length) → xs[i] ∈ T.levels[i]) ∧
  (∀ i, (hi : i + 1 < xs.length) → T.edge i xs[i] xs[i + 1])

/-- Host-semantic viability.  The executable reference implementation uses
this recurrence; the Lean proof should use `termination_by horizon - level`. -/
def ViableSem (T : FiniteTower) (horizon level candidate : Nat) : Prop :=
  level ≤ horizon ∧
  ∃ xs, T.Path xs ∧ xs[level]? = some candidate

/-- Semantic theorem target: backward viability is equivalent to a path. -/
def ViabilityPathTarget : Prop :=
  ∀ (T : FiniteTower) (H i a : Nat),
    i ≤ H → H < T.levels.length →
    ViableSem T H i a ↔
      ∃ xs, T.Path xs ∧ xs[i]? = some a

/-- Object formula asserting that a completed table satisfies the recurrence.
The integrated module replaces this schematic field with a concrete QF formula
using the shared table encoding. -/
structure ViabilityTableSpec {n : Nat} (R : RelPresentation n) where
  horizon : PTm n
  table : PTm n
  tableOK : Fm PTm n
  qf : tableOK.QF
  nonempty : Fm PTm n
  pathOK : Fm PTm n

/-- Object reflection targets. -/
def ViabilityReflectionTarget : Prop :=
  ∀ (n : Nat) (R : RelPresentation n)
    (S : ViabilityTableSpec R) (Γ : List (Fm PTm n)),
    (Γ ⊢[PRAAx] S.tableOK) →
    (Γ ⊢[PRAAx] S.nonempty ⟶ S.pathOK)

/-- Rational metric data for shrinking viable clouds.  Arithmetic details are
kept in object formulas so the framework does not assume Mathlib real numbers. -/
structure ShrinkingData {n : Nat} (R : RelPresentation n) where
  observation : PTm (n + 2)    -- candidate, precision, parameters
  diameter : PTm (n + 1)       -- precision, parameters
  motion : PTm (n + 1)
  adjacentBound : Fm PTm n
  tailBudget : Fm PTm n
  regularName : Fm PTm n

/-- Main object targets from the report. -/
def AdjacentCoherenceTarget : Prop :=
  ∀ (n : Nat) (R : RelPresentation n) (D : ShrinkingData R)
    (Γ : List (Fm PTm n)),
    Γ ⊢[PRAAx] D.adjacentBound

def RegularNameTarget : Prop :=
  ∀ (n : Nat) (R : RelPresentation n) (D : ShrinkingData R)
    (Γ : List (Fm PTm n)),
    Γ ⊢[PRAAx] D.tailBudget → Γ ⊢[PRAAx] D.regularName

end LeanProofs.ConciseIPRA.PFIG.Relation
