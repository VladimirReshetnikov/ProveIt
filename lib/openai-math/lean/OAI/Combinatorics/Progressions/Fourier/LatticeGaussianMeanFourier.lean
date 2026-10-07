import OAI.Combinatorics.Progressions.Lattices.LatticeGaussianPoisson
import OAI.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussian_fourier_summable_norm {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun ξ : euclideanDualLattice Λ =>
      ‖(Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x‖) := by
  simpa only [norm_mul, norm_euclideanCharacter, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_sub, norm_neg, div_eq_mul_inv] using
    lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussian_fourier_summable {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun ξ : euclideanDualLattice Λ =>
      (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x) :=
  (latticeGaussian_fourier_summable_norm Λ ht x).of_norm

theorem normalizedLatticeGaussian_zero_eq_dual {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian Λ t 0 = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 := by
  apply Complex.ofReal_injective
  rw [normalizedLatticeGaussian_poisson Λ ht]
  simp only [euclideanCharacter_zero, mul_one, latticeGaussianMass, Complex.ofReal_tsum,
    zero_sub, norm_neg, div_eq_mul_inv]

theorem normalizedLatticeGaussian_le_origin {t : ℝ} (ht : 0 < t) (x : E) :
    normalizedLatticeGaussian Λ t x ≤ normalizedLatticeGaussian Λ t 0 := by
  calc
    _ = ‖(normalizedLatticeGaussian Λ t x : ℂ)‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (normalizedLatticeGaussian_nonneg Λ t x)]
    _ = ‖∑' ξ : euclideanDualLattice Λ,
        (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x‖ := by
      rw [normalizedLatticeGaussian_poisson Λ ht]
    _ ≤ ∑' ξ : euclideanDualLattice Λ,
        ‖(Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x‖ :=
      norm_tsum_le_tsum_norm (latticeGaussian_fourier_summable_norm Λ ht x)
    _ = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 := by
      simp only [norm_mul, norm_euclideanCharacter, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), latticeGaussianMass,
        zero_sub, norm_neg, div_eq_mul_inv]
    _ = _ := (normalizedLatticeGaussian_zero_eq_dual Λ ht).symm

theorem normalizedLatticeGaussian_origin_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    normalizedLatticeGaussian Λ s 0 ≤ normalizedLatticeGaussian Λ t 0 := by
  rw [normalizedLatticeGaussian_zero_eq_dual Λ hs,
    normalizedLatticeGaussian_zero_eq_dual Λ (hs.trans_le hst)]
  exact latticeGaussianMass_antitone (euclideanDualLattice Λ) (inv_pos.mpr (hs.trans_le hst))
    (inv_le_inv₀ (hs.trans_le hst) hs |>.mpr hst) 0

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_fourier (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {t : ℝ} (ht : 0 < t) (k : ℕ) (α : E) (N : ℕ) :
    (latticeGaussianMean Λ t k α N : ℂ) =
      ∑' ξ : euclideanDualLattice Λ,
        (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * monomialCharacterMean k α N ξ := by
  unfold monomialCharacterMean
  simp only [← mul_div_assoc, Finset.mul_sum]
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun (n : ℤ) _ => latticeGaussian_fourier_summable Λ ht ((n : ℝ) ^ k • α))]
  simp only [← normalizedLatticeGaussian_poisson Λ ht]
  simp only [latticeGaussianMean, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end Erdos3

end

end OAI
