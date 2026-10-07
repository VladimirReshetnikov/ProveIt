import Mathlib.Algebra.Lie.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℝ L]

noncomputable def inverseScaledBasis (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) : Basis ι ℝ L :=
  e.unitsSMul (fun i => (Units.mk0 (d i) (hd i).ne')⁻¹)

theorem inverseScaledBasis_apply (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (i : ι) :
    inverseScaledBasis e d hd i = (d i)⁻¹ • e i := by
  simp only [inverseScaledBasis, Basis.unitsSMul_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0]

theorem inverseScaledBasis_repr (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (x : L) (i : ι) :
    (inverseScaledBasis e d hd).repr x i = d i * e.repr x i := by
  simp only [inverseScaledBasis, Basis.repr_unitsSMul, inv_inv,
    Units.smul_def, Units.val_mk0, smul_eq_mul]

theorem inverseScaledBasis_bracket (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hcompat : ∀ i j k, e.repr ⁅e i, e j⁆ k ≠ 0 → d k = d i * d j)
    (i j k : ι) :
    (inverseScaledBasis e d hd).repr
      ⁅inverseScaledBasis e d hd i, inverseScaledBasis e d hd j⁆ k =
        e.repr ⁅e i, e j⁆ k := by
  rw [inverseScaledBasis_repr, inverseScaledBasis_apply, inverseScaledBasis_apply]
  simp only [smul_lie, lie_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : e.repr ⁅e i, e j⁆ k = 0
  · simp only [h, mul_zero]
  · rw [hcompat i j k h]
    field_simp [(hd i).ne', (hd j).ne']

end Erdos3

end

end OAI
