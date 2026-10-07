import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def basisAxisScale (b : Basis I ℝ E) (i : I) : ℕ := ⌈‖b i‖⁻¹⌉₊

theorem basisAxisScale_pos (b : Basis I ℝ E) (i : I) : 0 < basisAxisScale b i := by
  apply Nat.ceil_pos.mpr
  exact inv_pos.mpr (norm_pos_iff.mpr (b.ne_zero i))

theorem basisAxisScale_eq_max (b : Basis I ℝ E) (i : I) :
    basisAxisScale b i = max 1 ⌈‖b i‖⁻¹⌉₊ := by
  exact (max_eq_right (basisAxisScale_pos b i)).symm

theorem basisAxisScale_mul_norm (b : Basis I ℝ E) (i : I) :
    1 ≤ (basisAxisScale b i : ℝ) * ‖b i‖ ∧
      (basisAxisScale b i : ℝ) * ‖b i‖ < ‖b i‖ + 1 := by
  have hpos : 0 < ‖b i‖ := norm_pos_iff.mpr (b.ne_zero i)
  have hlo := mul_le_mul_of_nonneg_right (Nat.le_ceil ‖b i‖⁻¹) hpos.le
  have hhi := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (inv_nonneg.mpr hpos.le)) hpos
  constructor
  · simpa only [basisAxisScale, inv_mul_cancel₀ hpos.ne'] using hlo
  · have he : (‖b i‖⁻¹ + 1) * ‖b i‖ = ‖b i‖ + 1 := by
      rw [add_mul, inv_mul_cancel₀ hpos.ne', one_mul, add_comm]
    simpa only [basisAxisScale, he] using hhi

noncomputable def normalizedAxisBasis (b : Basis I ℝ E) : Basis I ℝ E :=
  b.unitsSMul (fun i => Units.mk0 (basisAxisScale b i : ℝ)
    (Nat.cast_ne_zero.mpr (basisAxisScale_pos b i).ne'))

theorem normalizedAxisBasis_apply (b : Basis I ℝ E) (i : I) :
    normalizedAxisBasis b i = (basisAxisScale b i : ℝ) • b i := by
  simp only [normalizedAxisBasis, Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]

theorem normalizedAxisBasis_norm (b : Basis I ℝ E) (i : I) :
    ‖normalizedAxisBasis b i‖ = (basisAxisScale b i : ℝ) * ‖b i‖ := by
  rw [normalizedAxisBasis_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

theorem normalizedAxisBasis_norm_bounds (b : Basis I ℝ E) {B : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ B) (i : I) :
    1 ≤ ‖normalizedAxisBasis b i‖ ∧ ‖normalizedAxisBasis b i‖ ≤ B + 1 := by
  rw [normalizedAxisBasis_norm]
  refine ⟨(basisAxisScale_mul_norm b i).1, ?_⟩
  have h := (basisAxisScale_mul_norm b i).2
  have hi := hb i
  linarith

variable [Fintype I]

theorem normalizedAxisBasis_coordinates (b : Basis I ℝ E) (x : E) (i : I) :
    (normalizedAxisBasis b).equivFun x i = b.equivFun x i / (basisAxisScale b i : ℝ) := by
  simp only [normalizedAxisBasis, Basis.equivFun_apply, Basis.repr_unitsSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

theorem normalizedAxisBasis_norm_product (b : Basis I ℝ E) :
    (∏ i, ‖normalizedAxisBasis b i‖) = (∏ i, (basisAxisScale b i : ℝ)) * ∏ i, ‖b i‖ := by
  simp only [normalizedAxisBasis_norm, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
