import OAI.Combinatorics.Progressions.Estimates.MatchedFlatDecay
import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem matched_flat_integral_of_niltest_comparison
    (L : Finset (ZMod N)) (S : CyclicBohr.Set N)
    (hS : S.IsRankRegular) (hS1 : S.radius ≤ 1)
    (A B f g : ZMod N → ℝ) (z : ZMod N)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    {epsilon p C D R P M : ℝ} (hepsilon : 0 < epsilon) (hp : 1 ≤ p)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hMcap : M ≤ Real.exp (C * p)) (hwidth : Real.exp (-R) ≤ S.radius)
    {q : ℕ} (hq : 0 < q)
    (horder : (1 + C + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ Real.exp p)
    (hB : ∀ x, 0 ≤ B x ∧ B x ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S.carrier
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤
        flatComparisonDelta epsilon)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B) :
    matchedIntegral L S.carrier (fun x => A (z + x) - (1 + epsilon) * B (z + x)) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hp0 : 0 ≤ p := by linarith
  have hE : 0 ≤ (D + 2) * p := by positivity
  have hmean := S.small_sum_average_of_exponential_niltest_comparison hS hS1 A B
    (Real.exp_nonneg p) hp0 hE hR le_rfl hwidth
    (fun x => (hA x).1) (fun x => (hB x).2) hcomplexity hprecision hcompare z
  obtain ⟨hdelta, hdelta4, hcoeff⟩ := flatComparisonDelta_spec hepsilon
  have heta : Real.exp (-((D + 2) * p)) ≤ Real.exp (-(D * p)) / 4 := by
    have hfirst := exp_extra_decay_le_half (D := D + 1) hp
    have hsecond := exp_extra_decay_le_half (D := D) hp
    have heq : D + 1 + 1 = D + 2 := by ring
    rw [heq] at hfirst
    linarith
  apply matched_flat_integral_decay L S.carrier
    (fun x => A (z + x)) (fun x => B (z + x)) f g hu hv hu1 hv1 hq
    (Real.exp_nonneg p) hM hepsilon.le hdelta (hdelta4.trans (by norm_num)) hcoeff
    hp hC (by simp only [one_mul, le_refl]) hMcap heta horder
    (fun x => hA (z + x)) (fun x => hB (z + x)) hf hg hgcap hfsupport hfmean hflat
  simpa only [add_assoc] using hmean

end Erdos3.CellRefinement

end

end OAI
