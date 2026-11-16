import ConciseIPRA.NativeBiInterpretation

/-!
# Integration interface for the pinned ProveIt repository

STATUS: source-level integration outline; not compiler-checked in this package.
Unlike FiniteCore.lean and Targets.lean, this file requires the repository's
ConciseIPRA library and Mathlib v4.32.0.
It does not assert any of the unfinished analytic or geometric derivations.
-/

namespace IPRAEmbedding.ObjectInterface

open LeanProofs.ConciseIPRA
open scoped Fm

/-- Actual primitive-recursive definitions, not arbitrary programs given to a
purported universal total primitive-recursive evaluator. Natural arguments
encode the input, observation request, and any finite tuple data. -/
structure ObservationSymbols where
  inputCheck : PR 3
  outputCheck : PR 3
  demand : PR 2
  witness : PR 2

/-- A rational-valued fixed PR family, represented before quotienting. -/
structure RationalSymbols (arity : Nat) where
  numeratorPositive : PR arity
  numeratorNegative : PR arity
  denominatorPredecessor : PR arity

/-- Records the indispensable result of the object-theory phase.
Constructing the structure requires supplying an actual embedded proof. -/
structure DerivedStatement (n : Nat) where
  formula : Fm PTm n
  derivation : Prf PRAAx [] formula

/-- Pure syntactic composition inside the object theory. -/
theorem compose {n : Nat} {Γ : List (Fm PTm n)} {A B C : Fm PTm n}
    (hAB : Prf PRAAx Γ (A ⟶ B)) (hBC : Prf PRAAx Γ (B ⟶ C)) :
    Prf PRAAx Γ (A ⟶ C) := by
  exact .impI (.impE hBC.wk (.impE hAB.wk Prf.hyp0))

/-- Existing repository transport, usable only after the derivation exists. -/
theorem transport {n : Nat} (d : DerivedStatement n) :
    NPrf [] (NFm.ofPRA d.formula) := by
  have h := (pra_iff_native (Γ := []) (φ := d.formula)).mp d.derivation
  simpa using h

end IPRAEmbedding.ObjectInterface
