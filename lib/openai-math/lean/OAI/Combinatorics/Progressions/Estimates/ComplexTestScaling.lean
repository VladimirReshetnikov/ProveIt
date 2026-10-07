import OAI.Combinatorics.Progressions.Sampling.MixedOutputGrid

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem complexTest_bound_of_unit {V : Type*} (s : Finset V)
    (E : (V → ℂ) → ℂ) (hscale : ∀ z ψ, E (fun v => z * ψ v) = z * E ψ)
    {ε : ℝ} (he : ∀ ψ, (∀ v ∈ s, ‖ψ v‖ ≤ 1) → ‖E ψ‖ ≤ ε)
    {M : ℝ} (hM : 0 < M) (φ : V → ℂ) (hφ : ∀ v ∈ s, ‖φ v‖ ≤ M) :
    ‖E φ‖ ≤ M * ε := by
  let ψ := fun v => φ v / (M : ℂ)
  have hm : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hψ : ∀ v ∈ s, ‖ψ v‖ ≤ 1 := by
    intro v hv
    dsimp [ψ]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le]
    exact (div_le_one hM).mpr (hφ v hv)
  have hback : (fun v => (M : ℂ) * ψ v) = φ := by
    funext v
    dsimp [ψ]
    field_simp
  rw [← hback, hscale, norm_mul, Complex.norm_real, Real.norm_of_nonneg hM.le]
  exact mul_le_mul_of_nonneg_left (he ψ hψ) hM.le

theorem finiteMean_density_test_smul {X V : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (s : Finset V) (c : X → V → ℝ)
    (z : ℂ) (φ : V → ℂ) :
    p.complexMean (fun x => ∑ v ∈ s, (c x v : ℂ) * (z * φ v)) =
      z * p.complexMean (fun x => ∑ v ∈ s, (c x v : ℂ) * φ v) := by
  rw [← p.complexMean_mul_left]
  congr 1
  funext x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem gridDensityTest_smul {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (a S : J → ℝ) (s : Finset (J → ℤ))
    (mask : (J → ℤ) → ℝ) (z : ℂ) (φ : (J → ℤ) → ℂ) :
    gridDensityTest f a S s mask (fun v => z * φ v) = z * gridDensityTest f a S s mask φ := by
  unfold gridDensityTest
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem finiteMean_density_test_bound {X V : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (s : Finset V) (c : X → V → ℝ)
    (T : (V → ℂ) → ℂ) (hT : ∀ z ψ, T (fun v => z * ψ v) = z * T ψ)
    {ε : ℝ} (he : ∀ ψ, (∀ v ∈ s, ‖ψ v‖ ≤ 1) →
      ‖p.complexMean (fun x => ∑ v ∈ s, (c x v : ℂ) * ψ v) - T ψ‖ ≤ ε)
    {M : ℝ} (hM : 0 < M) (φ : V → ℂ) (hφ : ∀ v ∈ s, ‖φ v‖ ≤ M) :
    ‖p.complexMean (fun x => ∑ v ∈ s, (c x v : ℂ) * φ v) - T φ‖ ≤ M * ε := by
  apply complexTest_bound_of_unit s _ _ he hM φ hφ
  intro z ψ
  rw [finiteMean_density_test_smul, hT, mul_sub]

end Erdos3

end

end OAI
