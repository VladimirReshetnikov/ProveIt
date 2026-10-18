import GowersSzemeredi.Proofs18QuadraticSourceThreshold

/-! Declarations of `Proofs18QuadraticSourceThreshold` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false
set_option maxRecDepth 12000

noncomputable section

namespace LeanProofs.GowersSzemeredi

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
