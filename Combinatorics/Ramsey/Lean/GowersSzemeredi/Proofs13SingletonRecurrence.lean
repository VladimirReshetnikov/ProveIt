import GowersSzemeredi.Proofs13SmallRecurrenceScale

/-! A nonzero simultaneous recurrence step for a single selected height.
The half-modulus branch and the Bohr argument together cover every scale.

`lemma_13_5_printed_small_case` is in `Proofs13SingletonRecurrenceSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exists_nonzero_small_multiples {N q L : Nat} [NeZero N]
    (hN : 2 ≤ N) (hq : 0 < q) (hL : 0 < L) (hLN : L ≤ N)
    (a : Fin q → ZMod N) {e : Real} (he : 0 < e) (hqe : 2 * (q : Real) * e ≤ 1) :
    ∃ d : ZMod N, d != 0 ∧ ∀ i,
      (centeredAbs (a i * d) : Real) ≤ (L : Real) ^ (-e) * N := by
  have hL0 : (0 : Real) < L := by exact_mod_cast hL
  have hL1 : (1 : Real) ≤ L := by exact_mod_cast hL
  have hdelta : 0 < (L : Real) ^ (-e) := Real.rpow_pos_of_pos hL0 _
  by_cases hhalf : (1 / 2 : Real) ≤ (L : Real) ^ (-e)
  · -- the step `1` already has precision `1 / 2`
    haveI : Fact (1 < N) := ⟨hN⟩
    refine ⟨1, bne_iff_ne.mpr one_ne_zero, fun i => (centeredAbs_le_half_modulus _).trans ?_⟩
    linarith [mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg N : (0 : Real) ≤ N)]
  let K : Finset (ZMod N) := Finset.univ.image a
  have hK : K.Nonempty := ⟨a ⟨0, hq⟩, Finset.mem_image_of_mem a (Finset.mem_univ _)⟩
  have hc : 0 < (K.card : Real) := by exact_mod_cast hK.card_pos
  have hcard : (K.card : Real) ≤ q := by
    exact_mod_cast Finset.card_image_le.trans (Finset.card_fin q).le
  have hexp : 2 * e ≤ 1 / (K.card : Real) := (le_div_iff₀ hc).mpr (by
    linarith [mul_le_mul_of_nonneg_left hcard (by positivity : (0 : Real) ≤ 2 * e)])
  -- `N ^ (-1 / |K|) ≤ L ^ (-1 / |K|) ≤ L ^ (-2 e)`
  have hpow : (N : Real) ^ (-(1 / (K.card : Real))) ≤ (L : Real) ^ (-e) * (L : Real) ^ (-e) := by
    rw [← Real.rpow_add hL0]
    exact (Real.rpow_le_rpow_of_nonpos hL0 (by exact_mod_cast hLN)
      (neg_nonpos.mpr (by positivity))).trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  obtain ⟨d, hd, hdne⟩ := (lemma_7_7_holds N K _ hN hdelta
    (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))).2 hK
    (by linarith [mul_lt_mul_of_pos_left (lt_of_not_ge hhalf) hdelta])
  exact ⟨d, hdne, fun i => (Finset.mem_filter.mp hd).2 (a i)
    (Finset.mem_image_of_mem a (Finset.mem_univ i))⟩

/-- Stage 13.5 data at a length exponent `eL` and a precision exponent `eP`. -/
def IsStage135At {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (eL eP : Real) : Prop :=
  E.Q.step != 0 ∧ E.Q.IsProper ∧ E.Q.carrier ⊆ D.P.carrier ∧
  (D.P.length : Real) ^ eL / 2 ≤ E.Q.length ∧
  (∀ i, ∀ h, h ∈ E.Q.carrier →
    (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤
      (D.P.length : Real) ^ (-eP) * N) ∧
  S.alpha ^ 32 * E.Q.length / 20 ≤ (criticalHeights S D E).card

theorem isStage135Data_iff_at {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) :
    IsStage135Data S D E ↔
      IsStage135At S D E ((1 : Real) / (2 : Real) ^ (12 * D.q))
        ((1 : Real) / (2 : Real) ^ (11 * D.q)) :=
  Iff.rfl

/-- **The singleton scale.** One strong critical height, with a nonzero
step making every phase small, is a Stage 13.5 progression at a length
exponent `eL` with `|P|^eL ≤ 2` and a precision exponent `eP` with
`2q·eP ≤ 1`. -/
theorem stage135_singleton_at {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) (hL : 0 < D.P.length) {eL eP : Real} (he : 0 < eP)
    (hqe : 2 * (D.q : Real) * eP ≤ 1) (hscale : (D.P.length : Real) ^ eL ≤ 2) :
    ∃ E : Stage135Data N, IsStage135At S D E eL eP := by
  classical
  obtain ⟨hq, hstep, hP, hH, -, -, -, hw, -⟩ := h134
  have hmass : 0 < S.alpha ^ 32 * (D.P.length : Real) / 16 := by
    have := S.alpha_pos
    positivity
  obtain ⟨h, hh⟩ := Finset.card_pos.mp (Nat.cast_pos.mp (hmass.trans_le
    (stage135_critical_count_of_weight S D D.P hP (by rwa [Finset.inter_eq_right.mpr hH]))))
  obtain ⟨hhPH, hhstrong⟩ := Finset.mem_filter.mp hh
  obtain ⟨hhP, hhH⟩ := Finset.mem_inter.mp hhPH
  have hNtwo : 2 ≤ N := by
    have := ZMod.nontrivial_iff.mp (nontrivial_of_ne _ _ (bne_iff_ne.mp hstep))
    have := NeZero.ne N
    omega
  obtain ⟨d, hd, hsmall⟩ := exists_nonzero_small_multiples hNtwo hq hL
    (by rw [← hP]; exact (Finset.card_le_univ _).trans_eq (ZMod.card N))
    (fun i => D.a i * h + D.b i) he hqe
  -- the one-point progression `{h}` with step `d`
  let Q : ModAP N := ⟨h, d, 1⟩
  have hQ : Q.carrier = {h} := by simp [Q, ModAP.carrier]
  refine ⟨⟨Q⟩, hd, (by change Q.carrier.card = 1; rw [hQ, Finset.card_singleton]),
    (by rw [hQ]; exact Finset.singleton_subset_iff.mpr hhP), ?_,
    fun i x hx => (by rw [hQ, Finset.mem_singleton] at hx; subst x; exact hsmall i), ?_⟩
  · simp only [Q, Nat.cast_one]
    linarith only [hscale]
  · have h1 : (1 : Real) ≤ (criticalHeights S D ⟨Q⟩).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨h, by simp [criticalHeights, hQ, hhH, hhstrong]⟩
    simp only [Q, Nat.cast_one, mul_one] at h1 ⊢
    linarith only [h1, pow_le_one₀ (n := 32) S.alpha_pos.le S.alpha_at_most_one]

/-- The entire singleton-scale case from the printed Lemma 13.5 proof.
A simultaneous Bohr step replaces the unstated smallness argument. -/
theorem lemma_13_5_singleton_scale_positive {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) (hL : 0 < D.P.length)
    (hscale : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) ≤ 2) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  have hqn : 2 * D.q ≤ 2 ^ (11 * D.q) := by
    have h := Nat.lt_two_pow_self (n := 11 * D.q)
    omega
  exact stage135_singleton_at S D theta h134 hL (eP := (1 : Real) / (2 : Real) ^ (11 * D.q))
    (by positivity)
    (by rw [mul_one_div]; exact (div_le_one (by positivity)).mpr (by exact_mod_cast hqn)) hscale

theorem lemma_13_5_singleton_scale {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hscale : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) ≤ 2) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  by_cases hL : D.P.length = 0
  · exact lemma_13_5_empty_progression S D theta h134 hL
  · exact lemma_13_5_singleton_scale_positive S D theta h134 (by omega) hscale

end LeanProofs.GowersSzemeredi
