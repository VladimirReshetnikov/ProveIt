import GowersSzemeredi.Proofs13SmallRecurrenceScale

/-! Declarations of `Proofs13SmallRecurrenceScale` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem lemma_13_5_small_recurrence_scale {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) (hL : 0 < D.P.length)
    (hscale : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q)) ≤ 2) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  classical
  have hP := h134.2.2.1
  have hH := h134.2.2.2.1
  have hw : S.alpha ^ 32 * (N : Real) ^ 31 * D.P.length / 8 ≤
      (goodHeightWeight S (D.P.carrier ∩ D.H) : Real) := by
    rw [Finset.inter_eq_right.mpr hH]
    exact h134.2.2.2.2.2.2.2.1
  have hc := stage135_critical_count_of_weight S D D.P hP hw
  have hmass : 0 < S.alpha ^ 32 * (D.P.length : Real) / 16 :=
    div_pos (mul_pos (pow_pos S.alpha_pos _) (by exact_mod_cast hL)) (by norm_num)
  have hcard : 0 < (criticalHeights S D ⟨D.P⟩).card := by exact_mod_cast hmass.trans_le hc
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hcard
  obtain ⟨hhPH, hhstrong⟩ := Finset.mem_filter.mp hh
  obtain ⟨hhP, hhH⟩ := Finset.mem_inter.mp hhPH
  let Q : ModAP N := ⟨h, D.P.step, 1⟩
  have hQ : Q.carrier = {h} := by simp [Q, ModAP.carrier]
  have hproper : Q.IsProper := by change Q.carrier.card = 1; rw [hQ]; simp
  have hcrit : criticalHeights S D ⟨Q⟩ = {h} := by
    ext x
    simp only [criticalHeights, hQ, Finset.mem_filter, Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun hx => hx.1.1, fun hx => by subst x; exact ⟨⟨rfl, hhH⟩, hhstrong⟩⟩
  have hLreal : (0 : Real) < D.P.length := by exact_mod_cast hL
  have hLone : (1 : Real) ≤ D.P.length := by exact_mod_cast hL
  have htarget : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) ≤ 2 := by
    apply le_trans (Real.rpow_le_rpow_of_exponent_le hLone ?_) hscale
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have htolerance : (1 / 2 : Real) ≤
      (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) := by
    rw [Real.rpow_neg hLreal.le]
    simpa only [one_div] using (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLreal _) hscale)
  refine ⟨⟨Q⟩, h134.2.1, hproper, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Finset.singleton_subset_iff.mpr hhP
  · simp only [Q, Nat.cast_one]
    linarith only [htarget]
  · intro i x _
    exact (centeredAbs_le_half_modulus _).trans (by
      have hb := mul_le_mul_of_nonneg_right htolerance (Nat.cast_nonneg N)
      simpa only [one_div_mul_eq_div] using hb)
  · rw [hcrit, Finset.card_singleton]
    have ha : S.alpha ^ 32 ≤ 1 := pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one
    simp only [Q, Nat.cast_one, mul_one]
    linarith only [ha]

/-- The small-scale branch, including an empty input progression. -/
theorem lemma_13_5_small_scale {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hscale : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q)) ≤ 2) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  by_cases hL : D.P.length = 0
  · exact lemma_13_5_empty_progression S D theta h134 hL
  · exact lemma_13_5_small_recurrence_scale S D theta h134 (by omega) hscale

end LeanProofs.GowersSzemeredi
