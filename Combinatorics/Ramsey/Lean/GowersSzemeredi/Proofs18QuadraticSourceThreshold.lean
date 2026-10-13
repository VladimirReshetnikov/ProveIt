import GowersSzemeredi.Proofs18QuadraticSharperEnvelope
import GowersSzemeredi.Proofs18GeneralIteration
import GowersSzemeredi.Proofs18DoubleExponentialBounds

/-! The fully explicit four-term iteration fits the source's stated
quantitative Szemeredi threshold. This is a restricted instance only. -/
set_option autoImplicit false
set_option maxRecDepth 12000
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A concrete base-two double-exponential bound, throughout
0 < delta <= 1/2, with no unspecified multiplicative constant. -/
theorem quadraticIntervalClosedThreshold_le_explicit_tower {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) := by
  let u : Real := delta⁻¹
  let p : Nat := 12402
  let q : Nat := 153 * p
  let E : Nat := 2 ^ 21
  have hu : 2 ≤ u := by
    change 2 ≤ delta⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hb : 2 / intervalQuadraticUniformityParameter delta ≤ u ^ (153 : Nat) :=
    two_div_intervalQuadraticUniformityParameter_le_inv_pow hδ hδhalf
  have habsorb : (2 / intervalQuadraticUniformityParameter delta) ^ p ≤ u ^ q := by
    have h := pow_le_pow_left₀
      (by positivity : (0 : Real) ≤ 2 / intervalQuadraticUniformityParameter delta) hb p
    simpa only [← pow_mul] using h
  have hqE : q + 2 ≤ E := by norm_num [q, p, E]
  have hexp := exp_exp_pow_le_two_rpow_two_rpow hu hqE
  apply (quadraticIntervalClosedThreshold_le_double_exp_alpha_sharp hδ (by linarith)).trans
  exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans hexp

/-- The simplified four-term bound is smaller than the paper's exact
four-term instance, whose innermost power is 2^8192. -/
theorem quadraticIntervalClosedThreshold_le_source {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ szemerediThreshold delta 4 := by
  apply (quadraticIntervalClosedThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 8192))) =
      szemerediThreshold delta 4 := by
    unfold szemerediThreshold
    rw [show (2 : Real) ^ (4 + 9 : Nat) = 8192 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 21 ≤ 8192))

/-- The new four-term threshold is strictly smaller than the source's
four-term threshold over the entire stated density range. -/
theorem four_term_explicit_tower_lt_source {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) <
      szemerediThreshold delta 4 := by
  have hu : 1 < delta⁻¹ := by
    have hh : 2 ≤ delta⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hδ).mpr
      linarith
    linarith
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 8192))) =
      szemerediThreshold delta 4 := by
    unfold szemerediThreshold
    rw [show (2 : Real) ^ (4 + 9 : Nat) = 8192 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  exact pow_lt_pow_right₀ hu (Nat.pow_lt_pow_right (by norm_num) (by norm_num : 21 < 8192))

/-- A smaller explicit threshold suffices in the four-term natural-interval
case: the innermost exponent is 2^21 instead of the source's 2^8192. -/
theorem natural_four_term_explicit_tower
    (delta : Real) (N : Nat) (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hN : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) ≤ N)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A 4 :=
  hasNatAP_Icc_of_fin_interval
    (fun B hB => quadratic_interval_szemeredi_closed delta hδ (by linarith) N
      ((quadraticIntervalClosedThreshold_le_explicit_tower hδ hδhalf).trans hN) B hB) A hA hcard

/-- Theorem 18.2 is proved with its exact displayed threshold for four-term
progressions in {1,...,N}, independently of the higher-dimensional gap. -/
theorem theorem_18_2_four_holds
    (delta : Real) (N : Nat) (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hN : szemerediThreshold delta 4 ≤ N)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A 4 :=
  hasNatAP_Icc_of_fin_interval
    (fun B hB => quadratic_interval_szemeredi_closed delta hδ (by linarith) N
      ((quadraticIntervalClosedThreshold_le_source hδ hδhalf).trans hN) B hB) A hA hcard

end LeanProofs.GowersSzemeredi
