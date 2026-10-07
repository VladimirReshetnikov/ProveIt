import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalFunctional (ξ : E) : E →ₗ[ℝ] ℝ := (innerSL ℝ ξ).toLinearMap

@[simp]
theorem normalFunctional_apply (ξ x : E) : normalFunctional ξ x = inner ℝ ξ x := rfl

noncomputable def integralHyperplaneCorrection (ξ x : E) : E :=
  x - ((inner ℝ ξ x - (round (inner ℝ ξ x) : ℝ)) / ‖ξ‖ ^ 2) • ξ

theorem integralHyperplaneCorrection_inner (ξ x : E) (hξ : ξ ≠ 0) :
    inner ℝ ξ (integralHyperplaneCorrection ξ x) = (round (inner ℝ ξ x) : ℝ) := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  simp only [integralHyperplaneCorrection, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem integralHyperplaneCorrection_norm_sub (ξ x : E) (hξ : ξ ≠ 0) :
    ‖integralHyperplaneCorrection ξ x - x‖ =
      CircleFourier.integerDistance ((inner ℝ ξ x : ℝ) : CircleFourier.Circle) / ‖ξ‖ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rw [CircleFourier.integerDistance_coe]
  have hid : integralHyperplaneCorrection ξ x - x =
      -(((inner ℝ ξ x - (round (inner ℝ ξ x) : ℝ)) / ‖ξ‖ ^ 2) • ξ) := by
    unfold integralHyperplaneCorrection
    abel
  rw [hid, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖ξ‖)]
  field_simp

theorem exists_hyperplane_lattice_translate (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : E) (n : ℤ) (hx : f x = (n : ℝ)) :
    ∃ y : f.ker, x - (y : E) ∈ Λ := by
  refine ⟨hyperplaneRetraction f w hw x, ?_⟩
  change x - (x - f x • w) ∈ Λ
  rw [sub_sub_cancel, hx]
  simpa only [Int.cast_smul_eq_zsmul] using Λ.smul_mem n hwΛ

theorem exists_corrected_hyperplane_representative (Λ : Submodule ℤ E) (ξ : E) (hξ : ξ ≠ 0)
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) (x : E) :
    ∃ (β : E) (y : (normalFunctional ξ).ker),
      β - (y : E) ∈ Λ ∧
      ‖β - x‖ = CircleFourier.integerDistance ((inner ℝ ξ x : ℝ) : CircleFourier.Circle) / ‖ξ‖ := by
  let β := integralHyperplaneCorrection ξ x
  obtain ⟨y, hy⟩ := exists_hyperplane_lattice_translate Λ (normalFunctional ξ) w hwΛ hw β
    (round (inner ℝ ξ x)) (integralHyperplaneCorrection_inner ξ x hξ)
  exact ⟨β, y, hy, integralHyperplaneCorrection_norm_sub ξ x hξ⟩

end Erdos3

end

end OAI
