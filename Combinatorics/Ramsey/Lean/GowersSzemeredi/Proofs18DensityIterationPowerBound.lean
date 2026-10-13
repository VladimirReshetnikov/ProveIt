import GowersSzemeredi.Proofs18DensityIterationGrowth

/-! Fixed-power parameter estimates imply a double-exponential bound for
the entire finite density iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Exponential bounds on the two factors of the closed threshold combine
before applying the outer exponential. No sign condition on the budget `a` is needed. -/
theorem densityIterationClosedThreshold_le_double_exp_of_exp_power_bounds
    (T c rho gain a X : Real) (g r p : Nat) (hgain : 0 < gain) (hX : 2 ≤ X)
    (hA : 1 + Real.log (max 1 T) + |Real.log c| ≤ Real.exp a)
    (hg : gain⁻¹ ≤ X ^ g) (hb : 2 * max 1 rho⁻¹ ≤ Real.exp (X ^ r))
    (hp : g + 1 + r ≤ p) :
    densityIterationClosedThreshold T c rho ⌈gain⁻¹⌉₊ ≤
      Real.exp (Real.exp (a + X ^ p)) := by
  have hXone : 1 ≤ X := by linarith only [hX]
  have hXpos : 0 < X := by linarith only [hX]
  have hn : (⌈gain⁻¹⌉₊ : Real) ≤ X ^ (g + 1) := by
    calc
      _ ≤ gain⁻¹ + 1 := (Nat.ceil_lt_add_one (inv_nonneg.mpr hgain.le)).le
      _ ≤ X ^ g + X ^ g := add_le_add hg (one_le_pow₀ hXone)
      _ ≤ X * X ^ g := by nlinarith only [hX, pow_nonneg hXpos.le g]
      _ = _ := (pow_succ' X g).symm
  have hprod : (⌈gain⁻¹⌉₊ : Real) * X ^ r ≤ X ^ p := by
    calc
      _ ≤ X ^ (g + 1) * X ^ r := mul_le_mul_of_nonneg_right hn (pow_nonneg hXpos.le r)
      _ = X ^ (g + 1 + r) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hXone hp
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.exp a * (Real.exp (X ^ r)) ^ ⌈gain⁻¹⌉₊ :=
      mul_le_mul hA (pow_le_pow_left₀ (by positivity) hb _) (by positivity) (Real.exp_pos _).le
    _ = Real.exp (a + (⌈gain⁻¹⌉₊ : Real) * X ^ r) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (add_le_add le_rfl hprod)

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
