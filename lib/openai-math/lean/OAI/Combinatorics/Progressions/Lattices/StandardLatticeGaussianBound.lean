import OAI.Combinatorics.Progressions.Fourier.LatticeGaussianMeanFourier
import OAI.Combinatorics.Progressions.Lattices.IntegerGaussianGeometric
import OAI.Combinatorics.Progressions.Probability.FiniteProductMassBound

namespace OAI

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

theorem standardLatticeGaussian_mass_bound {t : ℝ} (ht : 0 < t) :
    latticeGaussianMass (standardEuclideanLattice ι) t⁻¹ 0 ≤ (1 + 2 * t) ^ Fintype.card ι := by
  classical
  have hpoint (z : ι → ℤ) :
      Real.exp (-Real.pi * t⁻¹ * ‖(0 : EuclideanSpace ℝ ι) -
          (standardEuclideanEquiv ι z : EuclideanSpace ℝ ι)‖ ^ 2) =
        ∏ i, Real.exp (-Real.pi / t * (z i : ℝ) ^ 2) := by
    change Real.exp (-Real.pi * t⁻¹ * ‖(0 : EuclideanSpace ℝ ι) -
      (standardEuclideanPoint ι z : EuclideanSpace ℝ ι)‖ ^ 2) = _
    rw [zero_sub, norm_neg, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
    simp only [standardEuclideanPoint_apply, div_eq_mul_inv]
  unfold latticeGaussianMass
  rw [← (standardEuclideanEquiv ι).tsum_eq]
  simp_rw [hpoint]
  apply Real.tsum_le_of_sum_le
  · intro z
    exact Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  · intro s
    exact finite_product_mass_bound (fun n : ℤ => Real.exp (-Real.pi / t * (n : ℝ) ^ 2))
      (fun _ => (Real.exp_pos _).le) (integer_gaussian_sum_bound ht) s

theorem standardLatticeGaussian_origin_bound {t : ℝ} (ht : 0 < t) :
    normalizedLatticeGaussian (standardEuclideanLattice ι) t 0 ≤ (1 + 2 * t) ^ Fintype.card ι := by
  rw [normalizedLatticeGaussian_zero_eq_dual _ ht, standardEuclideanLattice_self_dual]
  exact standardLatticeGaussian_mass_bound ι ht

end Erdos3

end

end OAI
