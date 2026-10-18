import GowersSzemeredi.Proofs18GeneralIntervalStopping

/-! Declarations of `Proofs18GeneralIntervalStopping` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

theorem intervalUniformityParameter_le_one {delta : Real} {k : Nat}
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hk : 0 < k) :
    intervalUniformityParameter delta k ≤ 1 := by
  have hkR : (1 : Real) ≤ k := by exact_mod_cast hk
  have hp : delta ^ k ≤ 1 := pow_le_one₀ hδ hδone
  have hden : (1 : Real) ≤ 512 * (k : Real) ^ 3 := by
    have hh : (1 : Real) ≤ (k : Real) ^ 3 := one_le_pow₀ hkR
    linarith
  apply pow_le_one₀ (by positivity)
  exact (div_le_one (by positivity : (0 : Real) < 512 * (k : Real) ^ 3)).mpr (hp.trans hden)

end LeanProofs.GowersSzemeredi
