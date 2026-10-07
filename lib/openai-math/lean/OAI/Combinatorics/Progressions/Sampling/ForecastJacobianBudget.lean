import Mathlib.Analysis.Complex.Exponential
import Mathlib.Basic.NNReal.Basic

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem forecastJacobian_exp_error (κ : ℝ≥0) {Pκ E : ℝ}
    (hκ : (κ : ℝ) ≤ Real.exp Pκ) :
    (κ : ℝ) * Real.exp (-(E + Pκ)) ≤ Real.exp (-E) := by
  calc
    (κ : ℝ) * Real.exp (-(E + Pκ)) ≤
        Real.exp Pκ * Real.exp (-(E + Pκ)) :=
      mul_le_mul_of_nonneg_right hκ (Real.exp_nonneg _)
    _ = Real.exp (-E) := by
      rw [← Real.exp_add, neg_add, add_left_comm, add_neg_cancel, add_zero]

theorem forecastJacobian_exp_mass (κ : ℝ≥0) {Pκ M mass : ℝ}
    (hκ : (κ : ℝ) ≤ Real.exp Pκ) (hmass : mass ≤ Real.exp M) :
    (κ : ℝ) * mass ≤ Real.exp (Pκ + M) := by
  calc
    (κ : ℝ) * mass ≤ (κ : ℝ) * Real.exp M :=
      mul_le_mul_of_nonneg_left hmass κ.coe_nonneg
    _ ≤ Real.exp Pκ * Real.exp M :=
      mul_le_mul_of_nonneg_right hκ (Real.exp_nonneg _)
    _ = Real.exp (Pκ + M) := (Real.exp_add Pκ M).symm

theorem forecastJacobian_complex_norm (κ : ℝ≥0) :
    ‖((κ : ℝ) : ℂ)‖ = (κ : ℝ) := by
  rw [Complex.norm_real, Real.norm_of_nonneg κ.coe_nonneg]

end Erdos3.VectorPolynomial

namespace Erdos3

theorem forecastJacobian_error_exp_bound {κ Pκ E : ℝ}
    (hκbound : κ ≤ Real.exp Pκ) :
    κ * Real.exp (-(E + Pκ)) ≤ Real.exp (-E) := by
  calc
    κ * Real.exp (-(E + Pκ)) ≤ Real.exp Pκ * Real.exp (-(E + Pκ)) :=
      mul_le_mul_of_nonneg_right hκbound (Real.exp_nonneg _)
    _ = Real.exp (-E) := by
      rw [← Real.exp_add, neg_add, add_left_comm, add_neg_cancel, add_zero]

theorem forecastJacobian_mass_exp_bound {κ Pκ M mass : ℝ}
    (hκ : 0 ≤ κ) (hκbound : κ ≤ Real.exp Pκ) (hmass : mass ≤ Real.exp M) :
    κ * mass ≤ Real.exp (Pκ + M) := by
  calc
    κ * mass ≤ κ * Real.exp M := mul_le_mul_of_nonneg_left hmass hκ
    _ ≤ Real.exp Pκ * Real.exp M :=
      mul_le_mul_of_nonneg_right hκbound (Real.exp_nonneg _)
    _ = Real.exp (Pκ + M) := (Real.exp_add Pκ M).symm

end Erdos3

end

end OAI
