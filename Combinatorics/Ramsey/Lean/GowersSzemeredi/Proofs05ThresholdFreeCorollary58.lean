import GowersSzemeredi.Proofs05ThresholdFreeCorollary
import GowersSzemeredi.Proofs05HighCorrelationAssembly
import GowersSzemeredi.Proofs05HighCorrelationScale
import GowersSzemeredi.Proofs05ThresholdFreeScale
import GowersSzemeredi.Proofs05AffineLocalization
import GowersSzemeredi.Proofs05QuadraticLocalization

/-! Corollary 5.8 from threshold-free polynomial localization, and its degree-one and degree-two specializations. Kept apart from the localization modules so that the final route does not import the high-correlation branches. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

theorem corollary58At_of_threshold_free_localization (k : Nat) (hk : 1 ≤ k)
    (hloc : ThresholdFreePolynomialLocalization k) : Corollary58At k := by
  classical
  intro N M _ A P phi delta alpha hM ha hA hdata hcover hdis hcomp hcor
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  have hdelta : delta = density A := by
    unfold density
    rw [hA]
    exact (mul_div_cancel_right₀ _ hNr.ne').symm
  subst delta
  let U := Finset.univ.biUnion (fun i => (P i).carrier)
  let B : Fin M → Finset (ZMod N) := fun i => (P i).carrier
  let w : Fin M → ZMod N → Complex := fun i x => exponential (-(phi i x))
  have hpart : IsPartition B U := by
    constructor
    · intro x
      simp only [U, B, Finset.mem_biUnion, Finset.mem_univ, true_and]
    · exact hdis
  have hAU : A ⊆ U := by
    intro x hx
    exact (hpart.1 x).mpr (hcover x hx)
  have hw : ∀ i x, ‖w i x‖ ≤ 1 := by
    intro i x
    exact (AddChar.norm_apply (ZMod.stdAddChar (N := N)) (-(phi i x))).le
  have hd := cover_correlation_density_strict A U B w hpart hAU hw ha hcor
  have hcells := high_correlation_parent_card_pos A U B w hpart hAU hw hcomp ha hcor
  have hMN : M ≤ N := by
    calc
      M = ∑ _i : Fin M, 1 := by simp
      _ ≤ ∑ i, (B i).card := Finset.sum_le_sum fun i _ => hcells i
      _ = U.card := hpart.sum_card
      _ ≤ N := by simpa only [ZMod.card] using U.card_le_univ
  have hS : 1 ≤ (N : Real) / M := by
    apply (le_div_iff₀ hMr).mpr
    simpa only [one_mul] using (show (M : Real) ≤ N by exact_mod_cast hMN)
  let K := polynomialPartitionConstant k
  let L := Nat.ceil (((N : Real) / M) ^ (K : Real)⁻¹ / 8)
  have hK : 4 ≤ K := polynomialPartitionConstant_ge_four hk
  obtain ⟨hL, htarget, hscale⟩ := threshold_free_target_scale hS hK
  change 1 ≤ L at hL
  change ((N : Real) / M) ^ (K : Real)⁻¹ / 8 ≤ (L : Real) at htarget
  by_cases hLone : L = 1
  · have hApos : 0 < A.card := by
      have hc : (A.card : Real) = density A * N :=
        (div_mul_cancel₀ _ hNr.ne').symm
      exact_mod_cast (hc.symm ▸ mul_pos hd.1 hNr)
    obtain ⟨a, haA⟩ := Finset.card_pos.mp hApos
    let Q : ModAP N := ⟨a, 0, 1⟩
    have hQ : Q.carrier = {a} := by simp [Q, ModAP.carrier]
    have hbound := (cover_correlation_density_bounds A U B w hpart hAU hw hcor).1
    have hd1 := density_le_one A
    have hgain : density A + alpha / 16 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hd1)]
    refine ⟨Q, ?_, ?_, ?_⟩
    · change Q.carrier.card = 1
      simp only [hQ, Finset.card_singleton]
    · simpa only [hQ, Finset.card_singleton, hLone, Nat.cast_one] using htarget
    · simpa only [hQ, Finset.inter_singleton_of_mem haA, Finset.card_singleton,
        Nat.cast_one, mul_one] using hgain
  have hL2 : 2 ≤ L := by omega
  have hL0 : 0 < L := by omega
  obtain ⟨hscaleK, hscale3⟩ := hscale hL2
  have hSN : (N : Real) / M ≤ N := by
    apply (div_le_iff₀ hMr).mpr
    have hm1 : (1 : Real) ≤ M := by exact_mod_cast hM
    nlinarith
  have hNL : L ^ 3 ≤ N := by exact_mod_cast (hscale3.trans_le hSN).le
  by_cases hsmall : alpha ≤ 3 * (1 - density A) / (2 * L)
  · obtain ⟨Q, hQ, hlen, hgain⟩ :=
      exists_proper_progression_of_small_correlation A hL2 hNL hd.1 hd.2 hsmall
    refine ⟨Q, hQ, ?_, le_trans ?_ hgain⟩
    · rw [show Q.carrier.card = L from hQ.trans hlen]
      exact htarget
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
  have hhigh : 3 * (1 - density A) / (2 * L) < alpha := lt_of_not_ge hsmall
  have hlarge (i : Fin M) : (2 * L) ^ (K / 2) ≤ (P i).length := by
    have hp := high_correlation_parent_scale A U B w hpart hAU hw hcomp ha hL0 hcor hhigh i
    have hr := threshold_free_parent_large hK hL hM (NeZero.pos N) hscaleK hp
    exact hr.le.trans (hdata i).1.le
  choose m R z hR hshape using fun i =>
    hloc N (P i) (phi i) L (hdata i).1 (hdata i).2 hL2 (hlarge i)
  have hRcell : ∀ i j, 0 < (R i j).carrier.card := by
    intro i j
    rw [(hshape i j).1]
    exact hL0.trans_le (hshape i j).2.1
  obtain ⟨i, j, hgain⟩ := density_cell_of_high_correlation A U B hpart hAU hL0 m
    (fun i j => (R i j).carrier) hR hRcell w z
    (fun i j => (hshape i j).2.2.1) ha (fun i j => (hshape i j).2.2.2) hcor hhigh.le
  refine ⟨R i j, (hshape i j).1, ?_, le_trans ?_ hgain⟩
  · apply htarget.trans
    exact_mod_cast ((hshape i j).2.1.trans_eq (hshape i j).1.symm)
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith

theorem corollary_5_8_holds_of_threshold_free_localization
    (hloc : ∀ k, 1 ≤ k → ThresholdFreePolynomialLocalization k) : corollary_5_8 := by
  intro N k M _ A P phi delta alpha hk
  exact corollary58At_of_threshold_free_localization k hk (hloc k hk) N M A P phi delta alpha

/-- The complete degree-one specialization, without any added scale condition. -/
theorem corollary_5_8_degree_one : Corollary58At 1 :=
  corollary58At_of_threshold_free_localization 1 (by omega) thresholdFreePolynomialLocalization_one

/-- The complete degree-two specialization with the catalogue's scale and gain. -/
theorem corollary_5_8_degree_two : Corollary58At 2 :=
  corollary58At_of_threshold_free_localization 2 (by omega) thresholdFreePolynomialLocalization_two

end LeanProofs.GowersSzemeredi
