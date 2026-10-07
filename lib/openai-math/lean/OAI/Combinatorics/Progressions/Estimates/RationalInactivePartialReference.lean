import OAI.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I A Z O : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O]

theorem rationalInactiveForecast_pointwise_test_summable
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (b : O → ZMod N) (test : Z → ℂ) :
    Summable (fun z => ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
      gridVolume : ℝ) : ℂ) * test z) := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.univ.image gridPoint) ?_).summable
  intro z hz
  simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
    zero_div, Complex.ofReal_zero, zero_mul]

theorem rationalInactiveForecast_pointwise_tsum_test
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (b : O → ZMod N) (test : Z → ℂ) :
    (∑' z, ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
      gridVolume : ℝ) : ℂ) * test z) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i)) := by
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul])]
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  exact (inactive.complexMean_fiber_factor_sum_image gridPoint
    (fun i => rationalOutputDensity (active i) (Y i) N b) test).symm

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalInactiveForecast_partial_reference
    {I A Z O K : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O] [Fintype K]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (b : K → O → ZMod N) (test : Z → K → ℂ) :
    (∑' z, 𝔼 k : K,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => 𝔼 k : K,
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) := by
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero])]
  rw [← Finset.expect_sum_comm]
  have he (k : K) : (∑ z ∈ Finset.univ.image gridPoint,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
        test (gridPoint i) k) := by
    simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
    exact (inactive.complexMean_fiber_factor_sum_image gridPoint
      (fun i => rationalOutputDensity (active i) (Y i) N (b k)) (fun z => test z k)).symm
  simp_rw [he]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp only [Finset.mul_expect]

end Erdos3

end

end OAI
