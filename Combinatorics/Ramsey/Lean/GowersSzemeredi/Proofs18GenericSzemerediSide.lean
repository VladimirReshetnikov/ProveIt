import GowersSzemeredi.Proofs18GenericSzemeredi

/-! Declarations of `Proofs18GenericSzemeredi` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-! ### The printed threshold as the offset-nine specialization -/

theorem double_exp_le_szemerediThreshold {L μ : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + 9)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThreshold delta L :=
  double_exp_le_szemerediThresholdAt (c := 9) hL hδ hδhalf hfit

/-- **Theorem 18.2 at length `L` from a degree-`(L−2)` envelope.** -/
theorem theorem182At_of_envBound {L μ : Nat} (hL : 3 ≤ L) (henv : EnvBound (L - 2) μ)
    (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + 9)) :
    Theorem182At L :=
  theorem182AtSharp_of_envBound (c := 9) hL henv hμ hLμ hfit

end LeanProofs.GowersSzemeredi
