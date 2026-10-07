import GowersSzemeredi.Proofs18DensityIterationPowerBound
import GowersSzemeredi.Proofs13FejerThresholdPolynomial

/-! Double-exponential density iteration when the inverse length exponent
and logarithmic threshold budget are single exponential. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exponentially small cubic length exponent still permits a
fixed-power double-exponential bound on the full finite iteration. -/
theorem densityIterationClosedThreshold_le_double_exp_of_exp_budget
    (T c rho gain X : Real) (g r p : Nat) (hgain : 0 < gain) (hX : 2 ≤ X)
    (hA : 1 + Real.log (max 1 T) + |Real.log c| ≤ Real.exp (X ^ p))
    (hg : gain⁻¹ ≤ X ^ g) (hb : 2 * max 1 rho⁻¹ ≤ Real.exp (X ^ r))
    (hp : g + 1 + r ≤ p) :
    densityIterationClosedThreshold T c rho ⌈gain⁻¹⌉₊ ≤
      Real.exp (Real.exp (X ^ (p + 1))) := by
  let A := 1 + Real.log (max 1 T) + |Real.log c|
  let b := 2 * max 1 rho⁻¹
  let n := ⌈gain⁻¹⌉₊
  have hXone : 1 ≤ X := by linarith only [hX]
  have hXpos : 0 < X := by linarith only [hX]
  have hApos : 0 < A := by
    have hl := Real.log_nonneg (le_max_left (1 : Real) T)
    have ha := abs_nonneg (Real.log c)
    dsimp [A]
    linarith only [hl, ha]
  have hbone : 1 ≤ b := by
    have h := le_max_left (1 : Real) rho⁻¹
    dsimp [b]
    linarith only [h]
  have hn : (n : Real) ≤ X ^ (g + 1) := nat_ceil_le_pow_succ hX (inv_nonneg.mpr hgain.le) hg
  have hlogb : Real.log b ≤ X ^ r := (Real.log_le_iff_le_exp (by linarith only [hbone])).mpr hb
  have hlogA : Real.log A ≤ X ^ p := (Real.log_le_iff_le_exp hApos).mpr hA
  have hprod : (n : Real) * Real.log b ≤ X ^ p := by
    calc
      _ ≤ X ^ (g + 1) * X ^ r :=
        mul_le_mul hn hlogb (Real.log_nonneg hbone) (pow_nonneg hXpos.le _)
      _ = X ^ (g + 1 + r) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hXone hp
  change Real.exp (A * b ^ n) ≤ _
  apply Real.exp_le_exp.mpr
  apply (Real.log_le_iff_le_exp (mul_pos hApos (pow_pos (by linarith only [hbone]) _))).mp
  rw [Real.log_mul hApos.ne' (pow_pos (by linarith only [hbone]) n).ne', Real.log_pow]
  calc
    _ ≤ 2 * X ^ p := by linarith only [hlogA, hprod]
    _ ≤ X * X ^ p := mul_le_mul_of_nonneg_right hX (pow_nonneg hXpos.le _)
    _ = _ := (pow_succ' _ _).symm

end LeanProofs.GowersSzemeredi
