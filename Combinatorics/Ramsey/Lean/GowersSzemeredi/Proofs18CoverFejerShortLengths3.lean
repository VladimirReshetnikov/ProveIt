import GowersSzemeredi.Proofs18CoverFejerShortLengths

/-! **Theorem 18.2 and Corollary 18.7 with `L + 3` at lengths `L ≤ 5`**
(Notes L.16k).

`Proofs18CoverFejerShortLengths` with `4` replaced by `3` (generated). The
corpus's explicit thresholds (Roth's `exp(exp(10¹²·δ⁻¹))` for `L ≤ 3`;
towers with `2^21` and `2^73` on top for `L = 4, 5`) stay below the
threshold with `L + 3` on top: `2^(4+3) = 128 ≥ 21` and `2^(5+3) = 256 ≥ 73`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem roth_threshold_le_szemerediThresholdAt_three (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThresholdAt 3 delta k := by
  have hu : (2 : Real) ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by linarith)
  have hu1 : (1 : Real) ≤ delta⁻¹ := by linarith
  have hu0 : (0 : Real) ≤ delta⁻¹ := by linarith
  have hx : (6 : Real) ≤ (2 : Real) ^ (k + 3 : Nat) := by
    have h6 : (2 : Real) ^ (3 : Nat) ≤ (2 : Real) ^ (k + 3 : Nat) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h64 : (6 : Real) ≤ (2 : Real) ^ (3 : Nat) := by norm_num
    linarith
  have hE : (42 : Real) ≤ (2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat)) := by
    have h64 : (2 : Real) ^ (6 : Real) ≤ (2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    have h64' : (2 : Real) ^ (6 : Real) = 64 := by
      rw [show (6 : Real) = ((6 : Nat) : Real) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hpow42 : delta⁻¹ ^ (42 : Nat) ≤
      delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat))) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by exact_mod_cast hE)
  have h41 : (2 : Real) ^ (41 : Nat) ≤ delta⁻¹ ^ (41 : Nat) :=
    pow_le_pow_left₀ (by norm_num) hu 41
  have hinner : 1 + 2 * (1000000000000 * delta⁻¹) ≤
      delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 3 : Nat))) := by
    have h41' : (2000000000001 : Real) ≤ delta⁻¹ ^ (41 : Nat) := by
      have : (2000000000001 : Real) ≤ (2 : Real) ^ (41 : Nat) := by norm_num
      linarith
    have h42 : delta⁻¹ ^ (42 : Nat) = delta⁻¹ * delta⁻¹ ^ (41 : Nat) := by ring
    nlinarith [mul_le_mul_of_nonneg_left h41' hu0, hpow42, h42, hu1]
  unfold szemerediThresholdAt
  apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    2 * Real.exp (1000000000000 * delta⁻¹) ≤
        2 * (2 : Real) ^ (2 * (1000000000000 * delta⁻¹)) :=
      mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
    _ = (2 : Real) ^ (1 + 2 * (1000000000000 * delta⁻¹)) := by
      rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner

theorem quadraticIntervalClosedThreshold_le_at_three {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ szemerediThresholdAt 3 delta 4 := by
  apply (quadraticIntervalClosedThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 128))) =
      szemerediThresholdAt 3 delta 4 := by
    unfold szemerediThresholdAt
    rw [show (2 : Real) ^ (4 + 3 : Nat) = 128 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 21 ≤ 128))

theorem fejerFiveTermThreshold_le_at_three {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ szemerediThresholdAt 3 delta 5 := by
  apply (fejerFiveTermThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 256))) =
      szemerediThresholdAt 3 delta 5 := by
    unfold szemerediThresholdAt
    rw [show (2 : Real) ^ (5 + 3 : Nat) = 256 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 73 ≤ 256))

/-- **Theorem 18.2 with `L + 3` at every length `L ≤ 5`.** -/
theorem theorem_18_2_L3_le_five {k : Nat} (hk : k ≤ 5) : Theorem182AtSharp 3 k := by
  rcases (by omega : k ≤ 3 ∨ k = 4 ∨ k = 5) with h | rfl | rfl
  · intro delta N hδ hδ2 hN A hA hc
    obtain ⟨a, d, hd, hap⟩ := roth_explicit_threshold delta N hδ
      ((roth_threshold_le_szemerediThresholdAt_three k hδ hδ2).trans hN) A hA hc
    exact ⟨a, d, hd, fun i hi => hap i (by omega)⟩
  · intro delta N hδ hδhalf hN A hA hcard
    exact hasNatAP_Icc_of_fin_interval
      (fun B hB => quadratic_interval_szemeredi_closed delta hδ (by linarith) N
        ((quadraticIntervalClosedThreshold_le_at_three hδ hδhalf).trans hN) B hB) A hA hcard
  · intro delta N hδ hδhalf hN A hA hcard
    exact natural_five_term_fejer delta hδ (by linarith only [hδhalf]) N
      ((fejerFiveTermThreshold_le_at_three hδ hδhalf).trans hN) A hA hcard

/-- **Corollary 18.7 with `L + 3` at every length `L ≤ 5`.** -/
theorem corollary_18_7_L3_le_five {k : Nat} (hk : k ≤ 5) : Corollary187AtSharp 3 k :=
  (theorem_18_2_L3_le_five hk).corollary_18_7

end LeanProofs.GowersSzemeredi
