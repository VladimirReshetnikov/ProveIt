import GowersSzemeredi.Proofs18DensityIterationGrowth

/-! Fixed-power parameter estimates imply a double-exponential bound for
the entire finite density iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem densityIterationClosedThreshold_le_double_exp
    (T c rho gain K X : Real) (g r p : Nat) (hgain : 0 < gain) (hX : 2 ≤ X)
    (hA : 1 + Real.log (max 1 T) + |Real.log c| ≤ K * X ^ p)
    (hg : gain⁻¹ ≤ X ^ g) (hr : rho⁻¹ ≤ X ^ r) (hp : g + r + 2 ≤ p) :
    densityIterationClosedThreshold T c rho ⌈gain⁻¹⌉₊ ≤
      Real.exp (Real.exp ((K + 1) * X ^ p)) := by
  let A := 1 + Real.log (max 1 T) + |Real.log c|
  let b := 2 * max 1 rho⁻¹
  let n := ⌈gain⁻¹⌉₊
  have hXone : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hApos : 0 < A := by
    have hl : 0 ≤ Real.log (max 1 T) := Real.log_nonneg (le_max_left _ _)
    dsimp [A]
    linarith [abs_nonneg (Real.log c)]
  have hbone : 1 ≤ b := by
    have := le_max_left 1 rho⁻¹
    dsimp [b]
    linarith
  have hb : b ≤ X ^ (r + 1) := by
    calc
      _ ≤ X * X ^ r := mul_le_mul hX (max_le (one_le_pow₀ hXone) hr)
        (le_trans (by norm_num) (le_max_left _ _)) hXpos.le
      _ = _ := (pow_succ' _ _).symm
  have hn : (n : Real) ≤ X ^ (g + 1) := by
    have hceil := (Nat.ceil_lt_add_one (inv_nonneg.mpr hgain.le)).le
    have hpow : 1 ≤ X ^ g := one_le_pow₀ hXone
    calc
      _ ≤ gain⁻¹ + 1 := hceil
      _ ≤ 2 * X ^ g := by linarith
      _ ≤ X * X ^ g := mul_le_mul_of_nonneg_right hX (pow_nonneg hXpos.le _)
      _ = _ := (pow_succ' _ _).symm
  have hlogb : Real.log b ≤ X ^ (r + 1) := (Real.log_le_self (by linarith)).trans hb
  have hlogA : Real.log A ≤ K * X ^ p := (Real.log_le_self hApos.le).trans hA
  have hprod : (n : Real) * Real.log b ≤ X ^ p := by
    calc
      _ ≤ X ^ (g + 1) * X ^ (r + 1) :=
        mul_le_mul hn hlogb (Real.log_nonneg hbone) (pow_nonneg hXpos.le _)
      _ = X ^ (g + r + 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ hXone hp
  change Real.exp (A * b ^ n) ≤ _
  apply Real.exp_le_exp.mpr
  apply (Real.log_le_iff_le_exp (mul_pos hApos (pow_pos (by linarith) _))).mp
  rw [Real.log_mul hApos.ne' (pow_pos (by linarith) n).ne', Real.log_pow]
  linarith

end LeanProofs.GowersSzemeredi
