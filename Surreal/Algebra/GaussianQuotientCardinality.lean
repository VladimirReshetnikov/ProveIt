import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Cardinalities of ordinary Gaussian integer quotients

The ordinary arithmetic step of `osq:thm:quotients`. A Gaussian integer
acts on the integer basis (1,i) with determinant re²+im². Mathlib's ideal
norm theorem identifies that determinant with the quotient cardinality.
-/

namespace Surreal.GaussianQuotientCardinality
noncomputable section

/-- The native Gaussian additive group has its usual two integer coordinates. -/
def coordinates : GaussianInt ≃+ (Fin 2 → ℤ) where
  toFun z := ![z.re, z.im]
  invFun f := ⟨f 0, f 1⟩
  left_inv _ := rfl
  right_inv f := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl

/-- The ordinary integer basis consisting of one and the imaginary unit. -/
def basis : Module.Basis (Fin 2) ℤ GaussianInt :=
  (Pi.basisFun ℤ (Fin 2)).map coordinates.toIntLinearEquiv.symm

@[simp] theorem basis_zero : basis 0 = (1 : GaussianInt) := by
  ext <;> simp [basis, coordinates]

@[simp] theorem basis_one : basis 1 = (Zsqrtd.sqrtd : GaussianInt) := by
  ext <;> simp [basis, coordinates]

@[simp] theorem basis_repr_zero (z : GaussianInt) : basis.repr z 0 = z.re := by
  simp [basis, coordinates]

@[simp] theorem basis_repr_one (z : GaussianInt) : basis.repr z 1 = z.im := by
  simp [basis, coordinates]

local instance : Module.Free ℤ GaussianInt := Module.Free.of_basis basis
local instance : Module.Finite ℤ GaussianInt := Module.Finite.of_basis basis

/-- Multiplication by a Gaussian integer has the standard two-by-two matrix. -/
theorem leftMulMatrix (z : GaussianInt) :
    Algebra.leftMulMatrix basis z = !![z.re, -z.im; z.im, z.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul]

/-- The native algebra norm is the ordinary sum of two integer squares. -/
theorem algebra_norm (z : GaussianInt) : Algebra.norm ℤ z = z.norm := by
  rw [Algebra.norm_eq_matrix_det basis, leftMulMatrix, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Zsqrtd.norm]
  ring

/-- The quotient cardinality is the Gaussian norm, including the infinite zero-modulus case. -/
theorem card_quotient (d : GaussianInt) :
    Nat.card (GaussianInt ⧸ Ideal.span {d}) = d.norm.natAbs := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, algebra_norm]

/-- A nonzero Gaussian modulus gives a genuinely finite quotient. -/
theorem finite_quotient (d : GaussianInt) (hd : d ≠ 0) :
    Finite (GaussianInt ⧸ Ideal.span {d}) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient]
  exact Int.natAbs_ne_zero.mpr (GaussianInt.norm_eq_zero.not.mpr hd)

/-- In real notation the cardinality is literally the squared complex modulus. -/
theorem card_quotient_eq_normSq (d : GaussianInt) :
    (Nat.card (GaussianInt ⧸ Ideal.span {d}) : ℝ) = Complex.normSq (GaussianInt.toComplex d) := by
  rw [card_quotient, GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm]

end
end Surreal.GaussianQuotientCardinality
