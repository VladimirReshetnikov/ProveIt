import OAI.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison

namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityPMF_mean_congr_density
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (f g : (K × I → ℤ) → ℂ)
    (hfg : ∀ x, (D x : ℂ) * f x = (D x : ℂ) * g x) :
    (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) =
      ∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * g x := by
  rw [selectedResidueDensityPMF_complexMean, selectedResidueDensityPMF_complexMean]
  simp_rw [hfg]

theorem selectedResidueDensityPMF_masked_test
    {K I Y : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D A : Y → ℝ) (hA : ∀ y, 0 ≤ A y) (hAD : ∀ y, A y ≤ D y)
    (sample : (K × I → ℤ) → Y)
    (hD : 0 < selectedResidueDensityMass modulus G V (fun x => D (sample x)))
    (test : (K × I → ℤ) → ℂ)
    (hmask : ∀ x, (D (sample x) : ℂ) * test x = (A (sample x) : ℂ)) :
    (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ (fun x => D (sample x))
      (fun x => (hA (sample x)).trans (hAD (sample x))) hD x).toReal : ℂ) * test x) =
      ∑' x, ((selectedResidueDensityPMF modulus G V hV hZ (fun x => D (sample x))
        (fun x => (hA (sample x)).trans (hAD (sample x))) hD x).toReal : ℂ) *
          dominatedDensityRatio D A (sample x) := by
  apply selectedResidueDensityPMF_mean_congr_density
  intro x
  rw [hmask x, dominatedDensityRatio_mul D A hA hAD]

end Erdos3

end

end OAI
