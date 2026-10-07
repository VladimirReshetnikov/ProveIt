/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Matrix
open scoped ComplexOrder

theorem one_le_eigenvalues_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) (i : ι) :
    1 ≤ hM.eigenvalues i := by
  let v := hM.eigenvectorBasis i
  have hv : star (⇑v) ⬝ᵥ ⇑v = (1 : ℝ) := by
    rw [dotProduct_comm]
    change inner ℝ v v = 1
    rw [real_inner_self_eq_norm_sq, hM.eigenvectorBasis.orthonormal.1 i, one_pow]
  have he : star (⇑v) ⬝ᵥ (M *ᵥ ⇑v) = hM.eigenvalues i := by
    simpa only [RCLike.re_to_real] using (hM.eigenvalues_eq i).symm
  have hp := h.dotProduct_mulVec_nonneg (⇑v)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, he, hv] at hp
  linarith

theorem one_le_det_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) :
    1 ≤ M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  exact Finset.one_le_prod₀ (fun i _ => one_le_eigenvalues_of_sub_one_posSemidef hM h i)

theorem eigenvalues_le_det_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) (i : ι) :
    hM.eigenvalues i ≤ M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  have heigen := one_le_eigenvalues_of_sub_one_posSemidef hM h
  have hp := Finset.prod_le_prod_of_subset_of_one_le₀
    (f := hM.eigenvalues) (Finset.subset_univ ({i} : Finset ι))
    (fun j _ => zero_le_one.trans (heigen j)) (fun j _ _ => heigen j)
  simpa only [Finset.prod_singleton, RCLike.ofReal_real_eq_id, id_eq] using hp

theorem det_smul_one_sub_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) :
    (M.det • (1 : Matrix ι ι ℝ) - M).PosSemidef := by
  let U : Matrix ι ι ℝ := hM.eigenvectorUnitary
  have hdiag : (Matrix.diagonal (fun i => M.det - hM.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i =>
      sub_nonneg.mpr (eigenvalues_le_det_of_sub_one_posSemidef hM h i))
  have hd : Matrix.diagonal (fun i => M.det - hM.eigenvalues i) =
      M.det • (1 : Matrix ι ι ℝ) - Matrix.diagonal hM.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hs : M = U * Matrix.diagonal hM.eigenvalues * U.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq, Matrix.star_eq_conjTranspose] using
      hM.spectral_theorem
  have hU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hp := hdiag.mul_mul_conjTranspose_same U
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hU, ← hs] at hp
  exact hp

end Erdos3

end

end OAI
