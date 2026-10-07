import OAI.Combinatorics.Progressions.Estimates.MixedRealPoint

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedRealCoordinates :
    EuclideanSpace ℝ D →ₗ[ℝ] ((I → ℝ) × (Fin n → ℝ)) :=
  ((orthonormalChart o).symm.toLinearMap.prodMap LinearMap.id).comp
    (normalizedOrthogonalChart W b).toLinearMap

theorem mixedRealCoordinates_point (x : (I → ℝ) × (Fin n → ℝ)) :
    mixedRealCoordinates W b o (mixedRealPoint W b o x) = x := by
  change ((orthonormalChart o).symm
      ((normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
        ((orthonormalChart o) x.1, x.2))).1,
    ((normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
        ((orthonormalChart o) x.1, x.2))).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem mixedRealPoint_coordinates (x : EuclideanSpace ℝ D) :
    mixedRealPoint W b o (mixedRealCoordinates W b o x) = x := by
  change (normalizedOrthogonalChart W b).symm
    ((orthonormalChart o) ((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1),
      ((normalizedOrthogonalChart W b) x).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

theorem mixedRealCoordinates_integer (u : I → ℝ) (z : Fin n → ℤ) :
    mixedRealCoordinates W b o (normalizedLatticePoint W b (orthonormalMixedChart o (u, z))) =
      (u, fun i => (z i : ℝ) / basisAxisScale b i) := by
  rw [← mixedRealPoint_integer W b o]
  exact mixedRealCoordinates_point W b o _

theorem mixedRealCoordinates_norm_le (x : EuclideanSpace ℝ D) :
    ‖mixedRealCoordinates W b o x‖ ≤ ‖normalizedOrthogonalChart W b x‖ := by
  change ‖((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1,
    ((normalizedOrthogonalChart W b) x).2)‖ ≤ _
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le_max (orthonormalChart_symm_norm_le o _) le_rfl

theorem mixedRealCoordinates_lipschitz {C : ℝ≥0}
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖) :
    LipschitzWith C (mixedRealCoordinates W b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact (mixedRealCoordinates_norm_le W b o _).trans (hC _)

end Erdos3

end

end OAI
