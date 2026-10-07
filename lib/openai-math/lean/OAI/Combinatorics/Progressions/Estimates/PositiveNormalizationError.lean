import OAI.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass

namespace OAI

section

namespace Erdos3

theorem complex_remove_normalization {N : ℂ} {Z : ℝ} (hZ : 0 < Z) (hN : ‖N‖ ≤ Z) :
    ‖N/(Z : ℂ)-N‖ ≤ |Z-1| := by
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hunit : ‖N/(Z : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
    exact (div_le_one hZ).mpr hN
  have he : N/(Z : ℂ)-N = (N/(Z : ℂ))*(1-(Z : ℂ)) := by field_simp
  rw [he, norm_mul]
  calc
    _ ≤ 1 * ‖1-(Z : ℂ)‖ := mul_le_mul_of_nonneg_right hunit (norm_nonneg _)
    _ = |Z-1| := by
      rw [one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]

theorem FiniteProbabilityWeights.norm_density_weighted_complexMean_le
    {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean (fun x => (D x : ℂ)*f x)‖ ≤ p.mean D := by
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply p.mean_mono
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD x)]
  exact (mul_le_mul_of_nonneg_left (hf x) (hD x)).trans_eq (mul_one _)

theorem selectedResidueDensityPMF_remove_normalization {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*((D z : ℂ)*f z))‖ ≤
        |selectedResidueDensityMass modulus T W D-1| := by
  rw [selectedResidueDensityPMF_complexMean]
  apply complex_remove_normalization hD
  rw [← selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ)*f z),
    ← selectedResidueFiniteLaw_densityMass modulus T W hW hZ D]
  exact FiniteProbabilityWeights.norm_density_weighted_complexMean_le
    (selectedResidueFiniteLaw modulus T W hW hZ)
    (fun z => D z.val) (fun z => hD0 z.val) (fun z => f z.val) (fun z => hf z.val)

theorem selectedResidueDensityPMF_error_of_bounded_test {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    {a : ℂ} {ε η : ℝ}
    (herror : ‖(∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      (f z*(D z : ℂ)))-a‖ ≤ ε)
    (hmass : |selectedResidueDensityMass modulus T W D-1| ≤ η) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z)-a‖ ≤ η+ε := by
  have hcomm : (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      ((D z : ℂ)*f z)) =
      ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*(f z*(D z : ℂ)) := by
    apply tsum_congr
    intro z
    rw [mul_comm (D z : ℂ) (f z)]
  have herror' : ‖(∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      ((D z : ℂ)*f z))-a‖ ≤ ε := by
    rw [hcomm]
    exact herror
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
    ((selectedResidueDensityPMF_remove_normalization modulus T W hW hZ D hD0 hD f hf).trans hmass)
    herror')

end Erdos3

end

end OAI
