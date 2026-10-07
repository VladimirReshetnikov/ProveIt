/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. Import paths are adapted to Mathlib v4.32.0. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Equiv

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_abs_le_row_bounds (A : Matrix ι ι ℝ) (H : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ H i) :
    |A.det| ≤ (Fintype.card ι).factorial * ∏ i, H i := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, H i := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ i, H (σ i) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, H i := Equiv.prod_comp σ H
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem matrix_det_abs_le_uniform_bound (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) :
    |A.det| ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    matrix_det_abs_le_row_bounds A (fun _ => H) hA

theorem matrix_adjugate_entry_abs_le (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (i j : ι) :
    |A.adjugate i j| ≤ (Fintype.card ι).factorial * H ^ (Fintype.card ι - 1) := by
  rw [Matrix.adjugate_apply]
  let K : ι → ℝ := fun k => if k = j then 1 else H
  have hentry : ∀ k l, |(A.updateRow j (Pi.single i 1)) k l| ≤ K k := by
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self, K, ite_true, Pi.single_apply]
      split_ifs <;> norm_num
    · simpa only [Matrix.updateRow_ne hk, K, hk, ite_false] using hA k l
  have hprod : (∏ k, K k) = H ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ K (Finset.mem_univ j)]
    have hj : K j = 1 := by simp [K]
    rw [hj, one_mul]
    calc
      (∏ k ∈ Finset.univ.erase j, K k) = ∏ _k ∈ Finset.univ.erase j, H := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [K, Finset.ne_of_mem_erase hk, ite_false]
      _ = _ := by simp
  simpa only [hprod] using matrix_det_abs_le_row_bounds _ K hentry

theorem matrix_inverse_entry_abs_le (A : Matrix ι ι ℝ) {H κ : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (hκ : 0 < κ) (hdet : κ ≤ |A.det|)
    (i j : ι) :
    |A⁻¹ i j| ≤ ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv]
  have hcof := matrix_adjugate_entry_abs_le A hA i j
  have hinv : |A.det|⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ hdet
  calc
    _ ≤ κ⁻¹ * ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) :=
      mul_le_mul hinv hcof (abs_nonneg _) (inv_nonneg.mpr hκ.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def matrixSupCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  A.mulVecLin.toContinuousLinearMap

theorem matrixSupCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : κ → ℝ) : matrixSupCLM A x = A.mulVec x := rfl

theorem matrixSupCLM_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) {H : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    ‖matrixSupCLM A‖ ≤ Fintype.card κ * H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, A i j * x j‖ ≤ _
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hx : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
      exact mul_le_mul (hA i j) hx (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

theorem matrixSupCLM_mul {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixSupCLM (A * B) = (matrixSupCLM A).comp (matrixSupCLM B) := by
  ext x i
  change ((A * B).mulVec x) i = (A.mulVec (B.mulVec x)) i
  rw [Matrix.mulVec_mulVec]

theorem matrixSupCLM_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixSupCLM (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  ext x i
  change ((1 : Matrix ι ι ℝ).mulVec x) i = x i
  simp

theorem matrixSupCLM_inverse_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (matrixSupCLM A).IsInvertible ∧ (matrixSupCLM A).inverse = matrixSupCLM A⁻¹ := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hright : (matrixSupCLM A).comp (matrixSupCLM A⁻¹) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← matrixSupCLM_mul, A.mul_nonsing_inv hunit, matrixSupCLM_one]
  have hleft : (matrixSupCLM A⁻¹).comp (matrixSupCLM A) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← matrixSupCLM_mul, A.nonsing_inv_mul hunit, matrixSupCLM_one]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft,
    ContinuousLinearMap.inverse_eq hright hleft⟩

theorem matrixSupCLM_inverse_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {H κ : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H)
    (hκ : 0 < κ) (hdet : κ ≤ |A.det|) :
    (matrixSupCLM A).IsInvertible ∧
      ‖(matrixSupCLM A).inverse‖ ≤
        Fintype.card ι * (((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ) := by
  have hne : A.det ≠ 0 := abs_pos.mp (hκ.trans_le hdet)
  obtain ⟨hinv, heq⟩ := matrixSupCLM_inverse_spec A hne
  refine ⟨hinv, ?_⟩
  rw [heq]
  exact matrixSupCLM_norm_le A⁻¹ (by positivity) (matrix_inverse_entry_abs_le A hA hκ hdet)

end Erdos3

end

end OAI
