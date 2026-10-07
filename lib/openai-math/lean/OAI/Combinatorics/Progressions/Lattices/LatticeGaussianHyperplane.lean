import OAI.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def latticeHyperplaneInclusion (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) :
    latticeHyperplane Λ f →ₗ[ℤ] Λ where
  toFun x := ⟨((x : f.ker) : E), (mem_latticeHyperplane Λ f (x : f.ker)).mp x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℝ E] in
theorem latticeHyperplaneInclusion_injective (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) :
    Function.Injective (latticeHyperplaneInclusion Λ f) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Λ => (z : E)) hxy

theorem latticeGaussianMass_hyperplane_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) {t : ℝ} (ht : 0 < t) (x : f.ker) :
    latticeGaussianMass (latticeHyperplane Λ f) t x ≤ latticeGaussianMass Λ t (x : E) := by
  have h := tsum_comp_le_tsum_of_inj (lattice_gaussian_summable Λ ht (x : E))
    (fun _ => (Real.exp_pos _).le) (latticeHyperplaneInclusion_injective Λ f)
  exact h

theorem latticeGaussianMass_hyperplane_translate_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) {t : ℝ} (ht : 0 < t) (x : E) (y : f.ker)
    (hxy : x - (y : E) ∈ Λ) :
    latticeGaussianMass (latticeHyperplane Λ f) t y ≤ latticeGaussianMass Λ t x := by
  rw [latticeGaussianMass_eq_of_sub_mem Λ t hxy]
  exact latticeGaussianMass_hyperplane_le Λ f ht y

end Erdos3

end

end OAI
