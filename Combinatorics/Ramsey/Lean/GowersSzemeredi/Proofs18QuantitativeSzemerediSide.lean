import GowersSzemeredi.Proofs18QuantitativeSzemeredi
import GowersSzemeredi.Proofs03ProgressionExistence

/-! Declarations of `Proofs18QuantitativeSzemeredi` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Combining the exact density increment with the proved uniform case gives
the strongest direct prime-cyclic consequence currently justified by the
live Section 18 interfaces. -/
theorem section18_cyclic_dichotomy_holds_of_theorem_18_1
    (h181 : theorem_18_1) : section18_cyclic_dichotomy := by
  intro k alpha halpha halphaHalf
  obtain ⟨N0, hinc⟩ :=
    section18_cyclic_density_increment_holds_of_theorem_18_1 h181
      (k - 2) alpha halpha halphaHalf
  refine ⟨N0, ?_⟩
  intro N _instN _instPrime hN A hk hkN hdensity halphaUniform hscale
  by_cases huniform : UniformSetOfDegree A alpha (k - 2)
  · left
    apply corollary_3_6_holds N k hkN A alpha (density A) hdensity hk
    · unfold density
      have hNreal : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp
    · exact huniform
    · exact halphaUniform
    · exact hscale
  · right
    exact hinc N hN A huniform

end LeanProofs.GowersSzemeredi
