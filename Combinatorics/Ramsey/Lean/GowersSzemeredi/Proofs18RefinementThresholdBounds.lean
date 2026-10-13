import GowersSzemeredi.Proofs18CoverBudget

/-! The phase-refinement threshold at the exponential level.

The estimate is parameterized by a polynomial partition budget and is
shared by the legacy cover envelopes and the final envelope. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `2^n ≤ e^n`. -/
theorem two_pow_le_exp_nat (n : Nat) : (2 : Real) ^ n ≤ Real.exp n := by
  have h2 : (2 : Real) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : Real); linarith
  calc (2 : Real) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2 n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

/-- **A constant tower at the exponential level**: `2^(2^m) ≤ exp(X^(2^j))`
once `m ≤ 2^j`. -/
theorem two_tower_le_ex {X : Real} (hX : 2 ≤ X) {m j : Nat} (hmj : m ≤ 2 ^ j) :
    (2 : Real) ^ (2 ^ m) ≤ Real.exp (X ^ (2 ^ j)) := by
  refine (two_pow_le_exp_nat (2 ^ m)).trans (Real.exp_le_exp.mpr ?_)
  push_cast
  exact (pow_le_pow_left₀ (by norm_num) hX m).trans (pw_natpow hX hmj)

theorem forty_cube_le (k : Nat) : 40 * (k + 1 + 1) ^ 3 + 2 ≤ 2 ^ (k + 11) := by
  have h1 := cube_le_two_pow_sharp k
  have h2 : (k + 1 + 1) ^ 3 ≤ (k + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : 2 ^ (k + 11) = 2048 * 2 ^ k := by rw [pow_add]; ring
  have h4 := Nat.one_le_two_pow (n := k)
  omega

/-- **The phase-refinement threshold, with the constants at the exponential
level.** -/
theorem inv_thr_le_ex_of_partition_bound {X : Real} (hX : 2 ≤ X) {k q : Nat} {η β e σ : Real} {M s : Nat}
    (hpart : polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ q)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (M + q + 4) (k + 16)) s + 1)))) := by
  -- the refinement constant at `b = ηβ/2`
  have hb : 0 < η * β / 2 := by positivity
  have hbi : (η * β / 2)⁻¹ ≤ X ^ (2 ^ (M + 2)) := by
    rw [show (η * β / 2)⁻¹ = 2 * (η⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr hη0).le (inv_pos.mpr hβ0).le hηi hβi
    exact pw_mul' hX (by norm_num) (by positivity) (hX.trans (pw_X hX M)) h1 |>.trans
      (pw_mono hX le_rfl (by omega))
  have hb1 : 1 ≤ (η * β / 2)⁻¹ := by
    rw [one_le_inv₀ hb]
    have : η * β ≤ 1 := mul_le_one₀ hη1 hβ0.le hβ1
    linarith
  have hscaled := section5LocalRefinementConstant_le_scaled (k + 1 + 1) (η * β / 2)
    (η * β / 2)⁻¹ hb hb1 le_rfl
  have hs5 : section5LocalRefinementConstant (k + 1 + 1) 1 ≤ Real.exp (X ^ (2 ^ (k + 11))) :=
    (s5_one_le (d := k + 1 + 1) (by omega)).trans (two_tower_le_ex hX (forty_cube_le k))
  have hpow : ((η * β / 2)⁻¹) ^ polynomialPartitionConstant (k + 1 + 1) ≤
      X ^ (2 ^ (M + 2 + q)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi hpart
  have hR : section5LocalRefinementConstant (k + 1 + 1) (η * β / 2) ≤
      Real.exp (X ^ (2 ^ (max (k + 11) (M + 2 + q) + 1))) :=
    hscaled.trans (ex_mul' hX (pow_nonneg (inv_pos.mpr hb).le _) hs5 (ex_of_pw hpow))
  -- the count constant
  have hσ16 : σ / 16 ≤ 1 := by linarith
  have hσ16' : 0 ≤ σ / 16 := by positivity
  have hr1 : (1 : Real) ≤ 2 * ((k + 1 + 2 : Nat) : Real) := by push_cast; linarith
  have hc1 : (1 : Real) ≤ 6 * ((k + 1 : Nat) : Real) := by push_cast; linarith
  have hrpow : (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16) ≤
      2 * ((k + 1 + 2 : Nat) : Real) :=
    Real.rpow_le_self_of_one_le hr1 (by linarith)
  have hcpow : (6 * ((k + 1 : Nat) : Real)) ^ (σ / 16) ≤
      6 * ((k + 1 : Nat) : Real) := Real.rpow_le_self_of_one_le hc1 hσ16
  have hB0 : 0 ≤ boundaryRefinementConstant (1 / 16) := (section5LocalRefinementConstant_pos _ _).le
  have hr : 2 * ((k + 1 + 2 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 2 * (k + 1 + 2)) (by omega)
    push_cast at this ⊢; linarith
  have hc : 6 * ((k + 1 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 6 * (k + 1)) (by omega)
    push_cast at this ⊢; linarith
  have hBe : boundaryRefinementConstant (1 / 16) ≤ Real.exp (X ^ (2 ^ 11)) :=
    cubic_boundary_refinement_constant_upper.trans (two_tower_le_ex hX (by norm_num))
  have h2e : (2 : Real) ≤ Real.exp (X ^ (2 ^ 0)) :=
    ex_of_pw (hX.trans (pw_X hX 0))
  have h2B : 2 * boundaryRefinementConstant (1 / 16) ≤ Real.exp (X ^ (2 ^ (max 0 11 + 1))) :=
    ex_mul' hX hB0 h2e hBe
  have hD : inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (X ^ (2 ^ (k + 14))) := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    have hmax : max 1 (2 * boundaryRefinementConstant (1 / 16) *
        (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16)) ≤
        Real.exp (X ^ (2 ^ (max (max 0 11 + 1) (k + 3) + 1))) :=
      max_le (Real.one_le_exp (by positivity)) (ex_mul' hX (Real.rpow_nonneg (by linarith) _) h2B
        (ex_of_pw (hrpow.trans hr)))
    have := ex_mul' hX (Real.rpow_nonneg (by linarith) _) hmax (ex_of_pw (hcpow.trans hc))
    exact ex_mono hX this (by omega)
  have hD1 : 1 ≤ inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hc1 hσ16')
  have hP1 : (1 : Real) ≤ polynomialPartitionConstant (k + 1 + 1) := by
    exact_mod_cast polyPartConst_pos (k + 1 + 1)
  have hDp : (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^
      ((polynomialPartitionConstant (k + 1 + 1) : Real))⁻¹ ≤
      inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ :=
    Real.rpow_le_self_of_one_le hD1 (inv_le_one_of_one_le₀ hP1)
  have hPIC : phaseInverseConstant (k + 1 + 1) (η * β / 2)
      (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ≤
      Real.exp (X ^ (2 ^ (max (max (M + q + 4) (k + 16)) s))) := by
    unfold phaseInverseConstant
    have := ex_mul' hX (Real.rpow_nonneg (le_trans zero_le_one hD1) _) hR (hDp.trans hD)
    exact ex_mono hX this (by omega)
  unfold inverseStepThreshold
  have hppt := positivePowerThreshold_one_le_double_exp hσ'0.le (le_exp_exp_of_le_exp hPIC) hσ'
  refine hppt.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact pw_add hX (pw_mono hX le_rfl le_rfl) (pw_mono hX le_rfl (le_max_right _ s))

/-- The phase-refinement estimate with the original polynomial partition budget. -/
theorem inv_thr_le_ex {X : Real} (hX : 2 ≤ X) {k : Nat} {η β e σ : Real} {M s : Nat}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (M + 4 * (k + 3) ^ 2 + 4) (k + 16)) s + 1)))) := by
  exact inv_thr_le_ex_of_partition_bound hX
    (by simpa only [show k + 1 + 1 + 1 = k + 3 by omega] using polyPartConst_le (k + 1 + 1))
    hη0 hη1 hβ0 hβ1 hηi hβi hs0 hs16 hσ'0 hσ'

end LeanProofs.GowersSzemeredi
