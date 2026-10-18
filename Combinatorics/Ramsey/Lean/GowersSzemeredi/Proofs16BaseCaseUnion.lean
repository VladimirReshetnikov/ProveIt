import GowersSzemeredi.Proofs16BaseCaseAssembly
import GowersSzemeredi.ProofInfrastructure

/-!
# Proper finite-union closure for the repaired Lemma 16.3

This module keeps `isMultilinear_const`; the rest of the development, with its
description, is in `Proofs16BaseCaseUnionSide`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma isMultilinear_const {N k : Nat} (c : ZMod N) :
    IsMultilinear (fun _ : Point N k => c) := by
  let e0 : Fin k -> Bool := fun _ => false
  refine ⟨fun e => if e = e0 then c else 0, ?_⟩
  intro x
  rw [Finset.sum_eq_single e0]
  · simp [e0]
  · intro e _he hne
    simp [hne]
  · simp

end LeanProofs.GowersSzemeredi.BaseCase
