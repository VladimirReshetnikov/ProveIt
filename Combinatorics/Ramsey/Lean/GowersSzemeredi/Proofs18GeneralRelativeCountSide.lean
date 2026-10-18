import GowersSzemeredi.Proofs18GeneralRelativeCount

/-! Declarations of `Proofs18GeneralRelativeCount` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Relative uniformity compares the actual count to the count in the
support, scaled by the fourth power of its relative density. -/
theorem relative_fourFactor_counting_bound {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha 2) :
    ‖progressionAverage (fun _ : Fin 4 => indicator A) -
        (delta : Complex) ^ 4 * progressionAverage (fun _ : Fin 4 => indicator S)‖ ≤
      4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 :=
  (relative_progression_counting_bound (k := 4) (by norm_num) hN A S delta alpha hAS hδ hδone hα
    hu).trans (le_of_eq (by norm_num))

end LeanProofs.GowersSzemeredi
