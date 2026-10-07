import OAI.Combinatorics.Progressions.Estimates.RationalInactivePartialReference

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I A Z O K : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O]

theorem rationalInactiveForecast_lattice_tsum_test
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (G : K → ℂ) (sK : Finset K) (hG : ∀ k ∉ sK, G k = 0)
    (b : K → O → ZMod N) (test : Z → K → ℂ) :
    (∑' z, ∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => ∑' k,
        G k * (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) := by
  let grid := Finset.univ.image gridPoint
  have hz (z : Z) (hz : z ∉ grid) (k : K) :
      rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) = 0 :=
    rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz (b k)
  rw [tsum_eq_sum (s := grid) (fun z h => by simp only [hz z h, zero_div,
    Complex.ofReal_zero, mul_zero, zero_mul, tsum_zero])]
  have hk (z : Z) : (∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      ∑ k ∈ sK, G k *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
          gridVolume : ℝ) : ℂ) * test z k :=
    tsum_eq_sum (fun k h => by rw [hG k h, zero_mul, zero_mul])
  simp_rw [hk]
  rw [Finset.sum_comm]
  have hzsum (k : K) :
      (∑ z ∈ grid, G k *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
          gridVolume : ℝ) : ℂ) * test z k) =
      G k * inactive.complexMean (fun i =>
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) := by
    rw [← rationalInactiveForecast_pointwise_tsum_test inactive active gridPoint Y N hV
      (b k) (fun z => test z k)]
    rw [tsum_eq_sum (s := grid) (fun z h => by simp only [hz z h k, zero_div,
      Complex.ofReal_zero, zero_mul])]
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [hzsum]
  have hi (i : I) : (∑' k, G k *
      (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) =
      ∑ k ∈ sK, G k *
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k :=
    tsum_eq_sum (fun k h => by rw [hG k h, zero_mul, zero_mul])
  simp_rw [hi, FiniteProbabilityWeights.complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rationalInactiveForecast_lattice_tsum_test_div
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (G : K → ℂ) (sK : Finset K) (hG : ∀ k ∉ sK, G k = 0)
    (b : K → O → ZMod N) (test : Z → K → ℂ) (v : ℂ) :
    (∑' z, ∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) / v =
      inactive.complexMean (fun i => (∑' k,
        G k * (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) / v) := by
  rw [rationalInactiveForecast_lattice_tsum_test inactive active gridPoint Y N hV G sK hG b test]
  simp only [FiniteProbabilityWeights.complexMean, Finset.sum_div, mul_div_assoc]

theorem rationalInactiveForecast_compactGrid_tsum_test_div {J : Type*} [Fintype J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ)
    (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (test : Z → (J → ℤ) → ℂ) :
    (∑' z, ∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) / ((∏ j, scale j : ℝ) : ℂ) =
      inactive.complexMean (fun i => (∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) / ((∏ j, scale j : ℝ) : ℂ)) := by
  apply rationalInactiveForecast_lattice_tsum_test_div inactive active gridPoint Y N hV
    _ (rectangularWeightIndices center scale R) _ b test
  intro k hk
  have h := rectangularWeight_zero_off_indices g center scale hscale hsupport k hk
  unfold rectangularWeight rectangularLatticePoint at h
  rw [h, Complex.ofReal_zero]

end Erdos3

end

end OAI
