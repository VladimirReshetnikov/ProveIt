import OAI.Combinatorics.Progressions.Fourier.CoordinatedBohrMatching

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

theorem matchingWidthLoss_outer (rank : ℕ) (P A E T delta c : ℝ) :
    matchingWidthLoss rank P (outerMatchingScaleLoss rank A E T) delta c =
      2 * T + 3 * rank + 2 * A + 2 * E + 2 * P +
        localMomentErrorBudget delta + unbalancedErrorBudget c + 4820 := by
  unfold matchingWidthLoss coordinatedMatchingScaleLoss outerMatchingScaleLoss
  ring

variable {N : ℕ} [NeZero N]

theorem exists_parent_controlled_matching
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {W A E M P T delta c : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp P) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1)
    (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    let kappa := outerMatchingScale B.rank W (Real.exp (-E)) scale
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    let K := outerMatchingScaleLoss B.rank A E T
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      L.radius ≤ B.radius / 3 ∧ S.radius ≤ L.radius ∧
      B.radius * Real.exp (-(K + 6)) ≤ L.radius ∧
      B.radius * Real.exp (-matchingWidthLoss B.rank P K delta c) ≤ S.radius ∧
      L.carrier ⊆ (B.ndilate scale).carrier ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  intro kappa tau K
  have hscale0 : 0 < scale := by exact_mod_cast (Real.exp_pos (-T)).trans_le hscale
  obtain ⟨_, hkappaScale, hkappa⟩ := outerMatchingScale_spec B.rank hW (Real.exp_pos (-E)) hscale0
  have hkappaLog := outerMatchingScale_exp_lower B.rank hW hWcap hA hE hT hscale
  have hK : 0 ≤ K := outerMatchingScaleLoss_nonneg B.rank hA hE hT
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hLwidth, hSwidth,
      hLlower, hSlower, hLB, hSL, hmoment, hsmall, herror, hcompare⟩ :=
    exists_coordinated_bohr_matching B hBpos hB hW (Real.exp_pos (-E)) hM hMcap hP hK
      hdelta hc hc1 kappa hkappa hkappaLog
  refine ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hLwidth, hSwidth,
    hLlower, hSlower, ?_, hSL, hmoment, hsmall, herror, hcompare⟩
  apply hLB.trans
  apply CyclicBohr.Set.carrier_ndilate_mono
  exact (div_le_self (show 0 ≤ kappa by positivity) (by norm_num : (1 : ℝ≥0) ≤ 3)).trans hkappaScale

end Erdos3.CellRefinement

end

end OAI
