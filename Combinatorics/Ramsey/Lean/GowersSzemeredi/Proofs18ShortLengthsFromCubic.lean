import GowersSzemeredi.Proofs18SharpInterfaces
import GowersSzemeredi.Proofs18QuadraticSourceThreshold

/-! Short-length instances of the offset-three bound from the existing
quadratic and cubic discrepancy arguments. Lengths two through four use
prefixes of the explicit four-term progression; length five uses the
cubic envelope through the general density iteration. The empty and
one-term cases follow from positive density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem szemerediThresholdAt_mono {c c' k : Nat} (hc : c ≤ c') {delta : Real} (hδ : 0 < delta)
    (hδ1 : delta ≤ 1) : szemerediThresholdAt c delta k ≤ szemerediThresholdAt c' delta k := by
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  unfold szemerediThresholdAt
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hu
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- A smaller constant gives a stronger Theorem 18.2. -/
theorem Theorem182AtSharp.mono {c c' k : Nat} (h : Theorem182AtSharp c k) (hc : c ≤ c') :
    Theorem182AtSharp c' k := fun delta N hδ hδ2 hN A hA hcard =>
  h delta N hδ hδ2 ((szemerediThresholdAt_mono hc hδ (by linarith)).trans hN) A hA hcard

/-- **Theorem 18.2 with `L + 3` at every length `L ≤ 5`.** -/
theorem theorem_18_2_L3_le_five {k : Nat} (hk : k ≤ 5) : Theorem182AtSharp 3 k := by
  by_cases hk5 : k = 5
  · subst k
    exact theorem182AtSharp_of_envBound (L := 5) (μ := 62) (c := 3)
      (by norm_num) envBound_three (by norm_num) (by norm_num) (by norm_num)
  intro delta N hδ hδhalf hN A hA hcard
  by_cases hk1 : k ≤ 1
  · have hNpos : (0 : Real) < N :=
      (show 0 < szemerediThresholdAt 3 delta k by unfold szemerediThresholdAt; positivity).trans_le hN
    have hcardpos : 0 < A.card := by
      exact_mod_cast (mul_pos hδ hNpos).trans_le hcard
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardpos
    refine ⟨a, 1, by decide, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    simpa [hi0] using ha
  have hk4 : k ≤ 4 := by omega
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ (2 ^ (k + 3))))) =
      szemerediThresholdAt 3 delta k := by
    unfold szemerediThresholdAt
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have hthreshold : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) ≤
      szemerediThresholdAt 3 delta k := by
    rw [← hsource]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply pow_le_pow_right₀ hu
    apply Nat.pow_le_pow_right (by norm_num)
    exact (by norm_num : 21 ≤ (2 : Nat) ^ 5).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨a, d, hd, hmem⟩ := natural_four_term_explicit_tower delta N hδ hδhalf
    (hthreshold.trans hN) A hA hcard
  exact ⟨a, d, hd, fun i hi => hmem i (hi.trans_le hk4)⟩

end LeanProofs.GowersSzemeredi
