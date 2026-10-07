import GowersSzemeredi.Proofs13SmallRecurrenceScale

/-! A nonzero simultaneous recurrence step for a single selected height.
The half-modulus branch and the Bohr argument together cover every scale. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exists_nonzero_small_multiples {N q L : Nat} [NeZero N]
    (hN : 2 ≤ N) (hq : 0 < q) (hL : 0 < L) (hLN : L ≤ N)
    (a : Fin q → ZMod N) {e : Real} (he : 0 < e) (hqe : 2 * (q : Real) * e ≤ 1) :
    ∃ d : ZMod N, d != 0 ∧ ∀ i,
      (centeredAbs (a i * d) : Real) ≤ (L : Real) ^ (-e) * N := by
  classical
  let delta := (L : Real) ^ (-e)
  have hL0 : (0 : Real) < L := by exact_mod_cast hL
  have hL1 : (1 : Real) ≤ L := by exact_mod_cast hL
  have hdelta : 0 < delta := Real.rpow_pos_of_pos hL0 _
  have hd1 : delta ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  by_cases hhalf : (1 / 2 : Real) ≤ delta
  · have hNne : N ≠ 1 := by omega
    have hone : (1 : ZMod N) != 0 := bne_iff_ne.mpr (by
      intro hz
      exact hNne (ZMod.one_eq_zero_iff.mp hz))
    refine ⟨1, hone, fun i => ?_⟩
    exact (centeredAbs_le_half_modulus _).trans (by
      have hb := mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg N)
      simpa only [one_div_mul_eq_div] using hb)
  · have hsmall : delta < 1 / 2 := lt_of_not_ge hhalf
    let K : Finset (ZMod N) := Finset.univ.image a
    have hK : K.Nonempty := ⟨a ⟨0, hq⟩, Finset.mem_image.mpr ⟨⟨0, hq⟩, Finset.mem_univ _, rfl⟩⟩
    have hc : 0 < (K.card : Real) := by exact_mod_cast Finset.card_pos.mpr hK
    have hcard : (K.card : Real) ≤ q := by
      exact_mod_cast (Finset.card_image_le.trans (le_of_eq (Finset.card_fin q)))
    have hexp : 2 * e ≤ 1 / (K.card : Real) := by
      apply (le_div_iff₀ hc).mpr
      have h := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 2 * e by positivity)
      nlinarith only [h, hqe]
    have hpow : (N : Real) ^ (-(1 / (K.card : Real))) ≤ delta ^ 2 := by
      calc
        _ ≤ (L : Real) ^ (-(1 / (K.card : Real))) :=
          Real.rpow_le_rpow_of_nonpos hL0 (by exact_mod_cast hLN) (neg_nonpos.mpr (by positivity))
        _ ≤ (L : Real) ^ (-(2 * e)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hexp)
        _ = delta ^ 2 := by
          dsimp [delta]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          congr 1
          push_cast
          ring
    have hthreshold : 2 * (N : Real) ^ (-(1 / (K.card : Real))) < delta := by
      nlinarith only [hpow, hsmall, hdelta]
    obtain ⟨d, hd, hdne⟩ := (lemma_7_7_holds N K delta hN hdelta hd1).2 hK hthreshold
    refine ⟨d, hdne, fun i => ?_⟩
    exact (Finset.mem_filter.mp hd).2 (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- The entire singleton-scale case from the printed Lemma 13.5 proof.
A simultaneous Bohr step replaces the unstated smallness argument. -/
theorem lemma_13_5_singleton_scale_positive {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) (hL : 0 < D.P.length)
    (hscale : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) ≤ 2) :
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
  have hNtwo : 2 ≤ N := by
    by_contra hN
    have hN1 : N = 1 := by have := NeZero.pos N; omega
    subst N
    exact (bne_iff_ne.mp h134.2.1) (Subsingleton.elim _ _)
  have hLN : D.P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using Finset.card_le_univ D.P.carrier
  have hqn : 2 * D.q ≤ 2 ^ (11 * D.q) := by
    have h := Nat.lt_two_pow_self (n := 11 * D.q)
    omega
  have hqe : 2 * (D.q : Real) * ((1 : Real) / 2 ^ (11 * D.q)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast hqn)
  obtain ⟨d, hd, hsmall⟩ := exists_nonzero_small_multiples hNtwo h134.1 hL hLN
    (fun i => D.a i * h + D.b i) (by positivity) hqe
  let Q : ModAP N := ⟨h, d, 1⟩
  have hQ : Q.carrier = {h} := by simp [Q, ModAP.carrier]
  have hproper : Q.IsProper := by change Q.carrier.card = 1; rw [hQ]; simp
  have hcrit : criticalHeights S D ⟨Q⟩ = {h} := by
    ext x
    simp only [criticalHeights, hQ, Finset.mem_filter, Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun hx => hx.1.1, fun hx => by subst x; exact ⟨⟨rfl, hhH⟩, hhstrong⟩⟩
  refine ⟨⟨Q⟩, hd, hproper, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Finset.singleton_subset_iff.mpr hhP
  · simp only [Q, Nat.cast_one]
    linarith only [hscale]
  · intro i x hx
    rw [hQ, Finset.mem_singleton] at hx
    subst x
    exact hsmall i
  · rw [hcrit, Finset.card_singleton]
    have ha : S.alpha ^ 32 ≤ 1 := pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one
    simp only [Q, Nat.cast_one, mul_one]
    linarith only [ha]
theorem lemma_13_5_singleton_scale {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hscale : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) ≤ 2) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  by_cases hL : D.P.length = 0
  · exact lemma_13_5_empty_progression S D theta h134 hL
  · exact lemma_13_5_singleton_scale_positive S D theta h134 (by omega) hscale

/-- The numerical cutoff used for the small case in the paper, including
its endpoint, implies the verified singleton-scale condition. -/
theorem lemma_13_5_printed_small_case {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hscale : D.P.length ≤ 2 ^ (2 ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  apply lemma_13_5_singleton_scale S D theta h134
  have hR : (D.P.length : Real) ≤ (2 : Real) ^ (2 ^ (12 * D.q) : Nat) := by
    exact_mod_cast hscale
  have hroot := Real.rpow_le_rpow (Nat.cast_nonneg D.P.length) hR
    (show (0 : Real) ≤ (((2 ^ (12 * D.q) : Nat) : Real)⁻¹) by positivity)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by positivity)] at hroot
  simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div] using hroot

end LeanProofs.GowersSzemeredi
