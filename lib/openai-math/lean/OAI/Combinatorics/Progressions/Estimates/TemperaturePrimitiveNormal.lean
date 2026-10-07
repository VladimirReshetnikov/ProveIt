import OAI.Combinatorics.Progressions.Fourier.LatticeGaussianMeanFourier

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem dualLattice_sqrt_temperature_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ζ : E) (hζ : ζ ≠ 0) (hζdual : ζ ∈ euclideanDualLattice Λ)
    {t : ℝ} (ht : 0 < t) :
    Real.sqrt t ≤ ‖ζ‖ * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0) := by
  have h := latticeGaussianMass_mul_scaled_norm_ge (euclideanDualLattice Λ)
    ζ hζdual hζ (inv_pos.mpr ht)
  rw [← normalizedLatticeGaussian_zero_eq_dual Λ ht, Real.sqrt_inv] at h
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hmul := mul_le_mul_of_nonneg_left h hs.le
  have hid : Real.sqrt t *
      (Real.sqrt t⁻¹ * ‖ζ‖ * normalizedLatticeGaussian Λ t 0) =
      ‖ζ‖ * normalizedLatticeGaussian Λ t 0 := by
    rw [Real.sqrt_inv]
    field_simp
  rw [Real.sqrt_inv] at hid
  rw [hid] at hmul
  have hh := mul_le_mul_of_nonneg_left hmul (Real.exp_pos Real.pi).le
  have he : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = Real.exp Real.pi * (Real.sqrt t * Real.exp (-Real.pi)) := by rw [mul_left_comm, he, mul_one]
    _ ≤ Real.exp Real.pi * (‖ζ‖ * normalizedLatticeGaussian Λ t 0) := hh
    _ = _ := by ring

theorem exists_temperature_bounded_primitive_normal
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ξ : E) (hξ : ξ ≠ 0) (hξdual : ξ ∈ euclideanDualLattice Λ)
    {t L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) (hnorm : ‖ξ‖ ≤ Real.sqrt t * L) :
    ∃ (m : ℤ) (ζ w : E), m ≠ 0 ∧ ξ = (m : ℝ) • ζ ∧ ζ ≠ 0 ∧
      ‖ζ‖ ≤ Real.sqrt t * L ∧ ζ ∈ euclideanDualLattice Λ ∧
      w ∈ Λ ∧ inner ℝ ζ w = 1 ∧
      Real.sqrt t ≤ ‖ζ‖ * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0) ∧
      |(m : ℝ)| ≤ L * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0) := by
  obtain ⟨m, ζ, w, hm, hsplit, hζ, hζnorm, hint, hwΛ, hw⟩ :=
    exists_primitive_lattice_normal Λ (IsZLattice.span_top (K := ℝ)) ξ hξ
      ((mem_euclideanDualLattice Λ ξ).mp hξdual)
  have hζdual := (mem_euclideanDualLattice Λ ζ).mpr hint
  have hs := dualLattice_sqrt_temperature_le Λ ζ hζ hζdual ht
  refine ⟨m, ζ, w, hm, hsplit, hζ, hζnorm.trans hnorm, hζdual, hwΛ, hw, hs, ?_⟩
  have hbound : |(m : ℝ)| * ‖ζ‖ ≤
      (L * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0)) * ‖ζ‖ := by
    calc
      |(m : ℝ)| * ‖ζ‖ = ‖ξ‖ := by rw [hsplit, norm_smul, Real.norm_eq_abs]
      _ ≤ Real.sqrt t * L := hnorm
      _ ≤ (‖ζ‖ * (Real.exp Real.pi * normalizedLatticeGaussian Λ t 0)) * L :=
        mul_le_mul_of_nonneg_right hs hL
      _ = _ := by ring
  nlinarith [norm_pos_iff.mpr hζ]

end Erdos3

end

end OAI
