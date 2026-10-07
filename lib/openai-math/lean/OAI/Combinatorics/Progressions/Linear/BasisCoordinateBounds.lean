import OAI.Combinatorics.Progressions.Geometry.CoordinateSupNorm
import OAI.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear

namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]

theorem basisCoordinateMap_apply_eq_sum (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ[ℝ] M) (v : ι → ℝ) (k : κ) :
    basisCoordinateMap e f φ v k = ∑ i, f.repr (φ (e i)) k * v i := by
  rw [basisCoordinateMap_apply, Basis.equivFun_symm_apply]
  change f.repr (φ (∑ i, v i • e i)) k = _
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem basisCoordinateMap_L2_bound (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ[ℝ] M) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (basisCoordinateMap e f φ v) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have heq : basisCoordinateMap e f φ v = fun k => ∑ i, f.repr (φ (e i)) k * v i :=
    funext (basisCoordinateMap_apply_eq_sum e f φ v)
  rw [heq]
  exact coordinateL2Norm_matrix_entry_bound (fun k i => f.repr (φ (e i)) k) B hB hφ v

end Erdos3

end

end OAI
