import OAI.Combinatorics.Progressions.Geometry.CoordinatedMatchingScale

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

noncomputable def matchingWidthLoss (rank : ℕ) (P K delta c : ℝ) : ℝ :=
  K + coordinatedMatchingScaleLoss rank P K delta c + 12

theorem matchingWidthLoss_nonneg (rank : ℕ) {P K delta c : ℝ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ matchingWidthLoss rank P K delta c := by
  have hEd := (localMomentErrorBudget_spec hdelta).1
  have hEc := (unbalancedErrorBudget_spec hc hc1).1
  unfold matchingWidthLoss coordinatedMatchingScaleLoss
  positivity

variable {N : ℕ} [NeZero N]

theorem exists_coordinated_bohr_matching
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {W epsilon M P K delta c : ℝ} (hW : 0 ≤ W) (hepsilon : 0 < epsilon)
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp P) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1)
    (kappa : ℝ≥0) (hkappa : kappa ≤ localizedAverageScale B.rank W (epsilon / 4))
    (hkappaLog : Real.exp (-K) ≤ (kappa : ℝ)) :
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      L.radius ≤ B.radius / 3 ∧ S.radius ≤ L.radius ∧
      B.radius * Real.exp (-(K + 6)) ≤ L.radius ∧
      B.radius * Real.exp (-matchingWidthLoss B.rank P K delta c) ≤ S.radius ∧
      L.carrier ⊆ (B.ndilate (kappa / 3)).carrier ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ epsilon := by
  intro tau
  have hkappa0 : 0 < kappa := by
    exact_mod_cast (Real.exp_pos (-K)).trans_le hkappaLog
  obtain ⟨htau0, htau, hmoment, hsmall, herror⟩ :=
    coordinatedMatchingScale_spec B.rank hM hdelta hc hkappa0
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos,
      hLlo, hLhi, hSlo, hShi, hLB, hSL, hcompare⟩ :=
    exists_bohr_matching_scales_with_scales B hBpos hB hW hepsilon kappa tau
      hkappa0 hkappa htau0 htau
  have hLrank : L.rank = B.rank := congrArg Finset.card hLfreq
  have hkappa1 : kappa ≤ 1 := hkappa.trans
    (localizedAverageScale_le_one B.rank hW (show 0 < epsilon / 4 by positivity))
  have htau1 : tau ≤ 1 := htau.trans
    ((div_le_self (by positivity) (by norm_num)).trans hkappa1)
  have hkappa1R : (kappa : ℝ) ≤ 1 := by exact_mod_cast hkappa1
  have htau1R : (tau : ℝ) ≤ 1 := by exact_mod_cast htau1
  have hLwidth : L.radius ≤ B.radius / 3 := by
    have h := mul_le_mul_of_nonneg_right hkappa1R B.radius_nonneg
    linarith
  have hSwidth : S.radius ≤ L.radius :=
    hShi.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htau1R L.radius_nonneg)
  have h6 : Real.exp (-6 : ℝ) ≤ 1 / 6 := by
    have h : (6 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp 6]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have h12 : Real.exp (-12 : ℝ) ≤ 1 / 12 := by
    have h : (12 : ℝ) ≤ Real.exp 12 := by linarith [Real.add_one_le_exp 12]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have htauLog := coordinatedMatchingScale_exp_lower B.rank hM hcap hP hK hdelta hc hc1 hkappaLog
  have hBnonneg := B.radius_nonneg
  have hLlower : B.radius * Real.exp (-(K + 6)) ≤ L.radius := by
    calc
      _ = Real.exp (-K) * B.radius * Real.exp (-6) := by
        rw [neg_add, Real.exp_add]
        ring
      _ ≤ (kappa : ℝ) * B.radius * (1 / 6) := by gcongr
      _ = (kappa : ℝ) * B.radius / 6 := by ring
      _ ≤ _ := hLlo
  have hSlower : B.radius * Real.exp (-matchingWidthLoss B.rank P K delta c) ≤ S.radius := by
    calc
      _ = Real.exp (-K) * Real.exp (-coordinatedMatchingScaleLoss B.rank P K delta c) *
          B.radius * Real.exp (-12) := by
        unfold matchingWidthLoss
        rw [neg_add, Real.exp_add, neg_add, Real.exp_add]
        ring
      _ ≤ (kappa : ℝ) * (tau : ℝ) * B.radius * (1 / 12) := by gcongr
      _ = (kappa : ℝ) * (tau : ℝ) * B.radius / 12 := by ring
      _ ≤ _ := hSlo
  refine ⟨L, S, hLfreq, hSfreq.trans hLfreq.symm, hLreg, hSreg, hLpos, hSpos,
    hLwidth, hSwidth, hLlower, hSlower, hLB, hSL, ?_, ?_, ?_, hcompare⟩
  · apply hSL.trans
    apply CyclicBohr.Set.carrier_ndilate_mono
    simpa only [hLrank] using hmoment
  · simpa only [hLrank] using hsmall
  · simpa only [hLrank] using herror

end Erdos3.CellRefinement

end

end OAI
