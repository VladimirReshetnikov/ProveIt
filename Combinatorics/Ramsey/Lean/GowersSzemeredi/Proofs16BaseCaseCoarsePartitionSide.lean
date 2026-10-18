import GowersSzemeredi.Proofs16BaseCaseCoarsePartition

/-! Declarations of `Proofs16BaseCaseCoarsePartition` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma isMultilinear_const_one {N : Nat} (c : ZMod N) :
    IsMultilinear (fun _ : Point N 1 => c) := by
  let e0 : Fin 1 → Bool := fun _ => false
  refine ⟨fun e => if e = e0 then c else 0, ?_⟩
  intro x
  rw [Finset.sum_eq_single e0]
  · simp [e0]
  · intro e _ hne
    simp [hne]
  · simp

end LeanProofs.GowersSzemeredi.BaseCase
