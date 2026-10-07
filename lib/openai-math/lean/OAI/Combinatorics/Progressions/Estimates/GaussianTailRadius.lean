import OAI.Combinatorics.Progressions.Fourier.WeightedFourierExtraction
import OAI.Combinatorics.Progressions.Lattices.GaussianLatticeDistance

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem normalizedLatticeGaussian_origin_ge_one {t : ℝ} (ht : 0 < t) :
    1 ≤ normalizedLatticeGaussian Λ t 0 := by
  rw [normalizedLatticeGaussian_zero_eq_dual Λ ht]
  have h := (lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0).le_tsum
    (0 : euclideanDualLattice Λ) (fun _ _ => (Real.exp_pos _).le)
  simpa only [latticeGaussianMass, Submodule.coe_zero, sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero] using h

theorem exists_short_dual_correlation {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (k : ℕ) (α : E) (N : ℕ)
    (htail : Real.exp (-Real.pi / t * R ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
      normalizedLatticeGaussian Λ t 0 ≤ 1 / 4)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧ ‖ξ‖ ≤ R ∧
      (8 * normalizedLatticeGaussian Λ t 0)⁻¹ < ‖monomialCharacterMean k α N ξ‖ := by
  classical
  let A := normalizedLatticeGaussian Λ t 0
  let w : euclideanDualLattice Λ → ℝ := fun ξ => Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2)
  let c : euclideanDualLattice Λ → ℂ := fun ξ => monomialCharacterMean k α N (ξ : E)
  have hA : 0 < A := normalizedLatticeGaussian_pos Λ ht 0
  have hw : Summable w := by
    simpa only [w, zero_sub, norm_neg, div_eq_mul_inv] using
      lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0
  have hwA : (∑' ξ, w ξ) = A := by
    rw [show A = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0 from
      normalizedLatticeGaussian_zero_eq_dual Λ ht]
    simp only [w, latticeGaussianMass, zero_sub, norm_neg, div_eq_mul_inv]
  have htailsum : (∑' ξ : euclideanDualLattice Λ, if ‖(ξ : E)‖ ≤ R then 0 else w ξ) ≤ (1 / 4 : ℝ) := by
    have h := latticeGaussianTail_bound (euclideanDualLattice Λ) (inv_pos.mpr ht) hR
    rw [← normalizedLatticeGaussian_zero_eq_dual Λ ht] at h
    have he : (∑' ξ : euclideanDualLattice Λ, if ‖(ξ : E)‖ ≤ R then 0 else w ξ) =
        latticeGaussianTail (euclideanDualLattice Λ) t⁻¹ R := by
      apply tsum_congr
      intro ξ
      simp only [w, ← not_lt, ite_not, div_eq_mul_inv]
    rw [he]
    exact h.trans (by simpa only [div_eq_mul_inv] using htail)
  have hδA : (8 * A)⁻¹ * A = (1 / 8 : ℝ) := by field_simp
  have hmean : (∑' ξ, (w ξ : ℂ) * c ξ).re = latticeGaussianMean Λ t k α N := by
    have h := congrArg Complex.re (latticeGaussianMean_fourier Λ ht k α N)
    simpa only [Complex.ofReal_re, w, c] using h.symm
  obtain ⟨ξ, hξ, hξR, hlarge⟩ := exists_large_allowed_coefficient w c
    (fun ξ => ‖(ξ : E)‖ ≤ R) (0 : euclideanDualLattice Λ)
    hw (fun ξ => (Real.exp_pos _).le) (by simp [w]) (by simp [c])
    (fun ξ => monomialCharacterMean_norm_le_one k α N ξ) (by positivity : 0 ≤ (8 * A)⁻¹)
    hwA.le htailsum (by rw [hmean, hδA]; linarith)
  refine ⟨ξ, ξ.property, ?_, hξR, hlarge⟩
  intro he
  exact hξ (Subtype.ext he)

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtRadiusFactor (d : ℕ) (A : ℝ) : ℝ :=
  4 * ((d : ℝ) + Real.log A + 1)

theorem schmidtRadiusFactor_pos (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    0 < schmidtRadiusFactor d A := by
  have hlog := Real.log_nonneg hA
  unfold schmidtRadiusFactor
  positivity

theorem gaussian_tail_radius_bound (d : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    Real.exp (-Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2) * (2 : ℝ) ^ d * A ≤ 1 / 4 := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlog := Real.log_nonneg hA
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have htwo : (2 : ℝ) ^ d ≤ Real.exp (d : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he d
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hexponent : -Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2 + d + Real.log A ≤ -4 := by
    have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hsq := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (schmidtRadiusFactor d A))
    unfold schmidtRadiusFactor at *
    nlinarith [sq_nonneg ((d : ℝ) + Real.log A)]
  have hsmall : Real.exp (-4 : ℝ) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 4)).mpr
    nlinarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ Real.exp (-Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2) * Real.exp (d : ℝ) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le) hApos.le
    _ = Real.exp (-Real.pi * (schmidtRadiusFactor d A) ^ 2 / 2 + d + Real.log A) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hApos]
    _ ≤ Real.exp (-4 : ℝ) := Real.exp_le_exp.mpr hexponent
    _ ≤ _ := hsmall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_logarithmically_short_dual_correlation (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) (k : ℕ) (α : E) (N : ℕ)
    (hsmall : latticeGaussianMean Λ t k α N < 1 / 2) :
    ∃ ξ : E, ξ ∈ euclideanDualLattice Λ ∧ ξ ≠ 0 ∧
      ‖ξ‖ ≤ Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0) ∧
      (8 * normalizedLatticeGaussian Λ t 0)⁻¹ < ‖monomialCharacterMean k α N ξ‖ := by
  have hA := normalizedLatticeGaussian_origin_ge_one Λ ht
  have hfactor := schmidtRadiusFactor_pos (Module.finrank ℝ E) hA
  apply exists_short_dual_correlation Λ ht (mul_nonneg (Real.sqrt_nonneg _) hfactor.le) k α N _ hsmall
  have h := gaussian_tail_radius_bound (Module.finrank ℝ E) hA
  have he : -Real.pi / t *
      (Real.sqrt t * schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0)) ^ 2 / 2 =
      -Real.pi * (schmidtRadiusFactor (Module.finrank ℝ E) (normalizedLatticeGaussian Λ t 0)) ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    field_simp
  rwa [he]

end Erdos3

end

end OAI
