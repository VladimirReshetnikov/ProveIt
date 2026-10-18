import GowersSzemeredi.Proofs18DensityIterationPowerBound

/-! Declarations of `Proofs18DensityIterationPowerBound` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem densityIterationClosedThreshold_le_double_exp
    (T c rho gain K X : Real) (g r p : Nat) (hgain : 0 < gain) (hX : 2 ≤ X)
    (hA : 1 + Real.log (max 1 T) + |Real.log c| ≤ K * X ^ p)
    (hg : gain⁻¹ ≤ X ^ g) (hr : rho⁻¹ ≤ X ^ r) (hp : g + r + 2 ≤ p) :
    densityIterationClosedThreshold T c rho ⌈gain⁻¹⌉₊ ≤
      Real.exp (Real.exp ((K + 1) * X ^ p)) := by
  have hXone : 1 ≤ X := by linarith only [hX]
  have hXpos : 0 < X := by linarith only [hX]
  have he : ∀ y : Real, y ≤ Real.exp y := fun y =>
    (le_add_of_nonneg_right (by norm_num : (0 : Real) ≤ 1)).trans (Real.add_one_le_exp y)
  have hb : 2 * max 1 rho⁻¹ ≤ X ^ (r + 1) := by
    calc
      _ ≤ X * X ^ r := mul_le_mul hX (max_le (one_le_pow₀ hXone) hr)
        (le_trans (by norm_num) (le_max_left _ _)) hXpos.le
      _ = _ := (pow_succ' _ _).symm
  simpa only [add_mul, one_mul] using
    densityIterationClosedThreshold_le_double_exp_of_exp_power_bounds T c rho gain (K * X ^ p) X
      g (r + 1) p hgain hX (hA.trans (he _)) hg (hb.trans (he _)) (by omega)

end LeanProofs.GowersSzemeredi
