import GowersSzemeredi.Proofs10Shift

/-! Declarations of `Proofs10Shift` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma fibreSize_eq_of_index_eq {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {x y : X} (hxy : D.index x = D.index y) :
    D.fibreSize x = D.fibreSize y := by
  simp only [MultifunctionDomain.fibreSize, hxy]

theorem lemma_10_8_holds : lemma_10_8 := by
  intro N _ X _ _ D W B eta theta P hregular htheta hP d hd
  exact almostEvery_mono (1 - Real.sqrt theta - eta) W
    (fun w => w ∈ shiftEligible D W d ∧
      AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P)
    (fun w => AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P)
    (shift_almostEvery_eligible D W B eta theta P hregular htheta hP d hd)
    (fun _ _ h => h.2)

end LeanProofs.GowersSzemeredi
