import OAI.Combinatorics.Progressions.Polynomial.MixedPolynomialChart

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedRealPoint : ((I → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm.toLinearMap.comp
    ((orthonormalChart o).toLinearMap.prodMap (LinearMap.id))

theorem mixedRealPoint_integer (u : I → ℝ) (z : Fin n → ℤ) :
    mixedRealPoint W b o (u, fun i => (z i : ℝ) / basisAxisScale b i) =
      normalizedLatticePoint W b (orthonormalMixedChart o (u, z)) := rfl

theorem mixedRealPoint_norm_le {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (u : I → ℝ) (z : Fin n → ℝ) (hu : ∀ i, |u i| ≤ R) (hz : ∀ i, |z i| ≤ R) :
    ‖mixedRealPoint W b o (u, z)‖ ≤ C * (((Fintype.card I : ℝ) + 1) * R) := by
  have hu' : ‖u‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hu)
  have hz' : ‖z‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hz)
  have ho := (orthonormalChart_norm_le o u).trans (mul_le_mul_of_nonneg_left hu' (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart o u, z)‖ ≤ ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  exact (hchart _).trans (mul_le_mul_of_nonneg_left hp hC)

theorem mixedRealPoint_scaled_coordinate_bound {C R S : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hS : 0 < S)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (u : I → ℝ) (z : Fin n → ℝ) (hu : ∀ i, |u i| * S ≤ R) (hz : ∀ i, |z i| * S ≤ R) (d : D) :
    |mixedRealPoint W b o (u, z) d| ≤ C * (((Fintype.card I : ℝ) + 1) * R) / S := by
  apply (le_div_iff₀ hS).mpr
  have hscale := mixedRealPoint_norm_le W b o hC hR hchart (S • u) (S • z)
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hS, mul_comm] using hu i)
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hS, mul_comm] using hz i)
  have he : mixedRealPoint W b o (S • u, S • z) = S • mixedRealPoint W b o (u, z) :=
    (mixedRealPoint W b o).map_smul S (u, z)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hS] at hscale
  have hd : |mixedRealPoint W b o (u, z) d| ≤ ‖mixedRealPoint W b o (u, z)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (mixedRealPoint W b o (u, z)) d
  exact (mul_le_mul_of_nonneg_right hd hS.le).trans (by simpa only [mul_comm] using hscale)

end Erdos3

end

end OAI
