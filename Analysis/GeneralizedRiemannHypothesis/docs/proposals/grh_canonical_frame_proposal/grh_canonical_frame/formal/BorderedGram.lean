import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic certificates for canonical negative frames

This standalone file checks the noncommutative completed-square identity
underlying the bordered Hua integral in the accompanying proposal.
It does not import the GRH project or claim to formalize the integral.
-/

noncomputable section

namespace CanonicalFrame

open Matrix

variable {R : Type*} [Field R]
variable {I K : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K]

/-- Append one distinguished column, indexed by `Unit`. -/
def appendColumn (X : Matrix K I R) (v : Matrix K Unit R) : Matrix K (I ⊕ Unit) R :=
  fun a j => Sum.elim (X a) (v a) j

omit [Fintype I] [DecidableEq I] in
/-- Complete the square in the Schur complement of a bordered Gram matrix.
The statement is algebraic and does not assume conjugation or positivity.
In the Hermitian application, `Y = Xᴴ`, `c = bᴴ`, `w = vᴴ`, and
`d = h + ‖v‖²`. -/
theorem bordered_completion
    (A : Matrix I I R) (b : Matrix I Unit R) (c : Matrix Unit I R)
    (X : Matrix K I R) (Y : Matrix I K R)
    (v : Matrix K Unit R) (w : Matrix Unit K R)
    {h d : R} (hh : h ≠ 0) (hd : d ≠ 0)
    (hwv : w * v = (d - h) • (1 : Matrix Unit Unit R)) :
    A + Y * X - d⁻¹ • ((b + Y * v) * (c + w * X)) =
      (A - h⁻¹ • (b * c)) +
        (Y - h⁻¹ • (b * w)) *
          (1 - d⁻¹ • (v * w)) *
          (X - h⁻¹ • (v * c)) := by
  have hwvc : w * (v * c) = (d - h) • c := by
    rw [← Matrix.mul_assoc, hwv, Matrix.smul_mul, Matrix.one_mul]
  have hwvw : w * (v * w) = (d - h) • w := by
    rw [← Matrix.mul_assoc, hwv, Matrix.smul_mul, Matrix.one_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_assoc, hwvc, hwvw, smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp <;> ring

/-- Schur determinant expansion at a scalar one-dimensional corner. -/
theorem det_scalar_corner
    (A : Matrix I I R) (b : Matrix I Unit R) (c : Matrix Unit I R)
    {h : R} (hh : h ≠ 0) :
    (fromBlocks A b c (h • (1 : Matrix Unit Unit R))).det =
      h * (A - h⁻¹ • (b * c)).det := by
  let : Invertible (h • (1 : Matrix Unit Unit R)) :=
    { invOf := h⁻¹ • 1
      invOf_mul_self := by simp [smul_smul, hh]
      mul_invOf_self := by simp [smul_smul, hh] }
  have hi : ⅟(h • (1 : Matrix Unit Unit R)) = h⁻¹ • 1 := rfl
  rw [det_fromBlocks₂₂, hi]
  simp [Matrix.det_unique, Matrix.mul_smul, Matrix.smul_mul]

/-- The full bordered determinant identity, without positivity assumptions. -/
theorem bordered_determinant
    (A : Matrix I I R) (b : Matrix I Unit R) (c : Matrix Unit I R)
    (X : Matrix K I R) (Y : Matrix I K R)
    (v : Matrix K Unit R) (w : Matrix Unit K R)
    {h d : R} (hh : h ≠ 0) (hd : d ≠ 0)
    (hwv : w * v = (d - h) • (1 : Matrix Unit Unit R)) :
    (fromBlocks (A + Y * X) (b + Y * v) (c + w * X)
      (d • (1 : Matrix Unit Unit R))).det =
    d * ((A - h⁻¹ • (b * c)) +
      (Y - h⁻¹ • (b * w)) * (1 - d⁻¹ • (v * w)) *
        (X - h⁻¹ • (v * c))).det := by
  rw [det_scalar_corner _ _ _ hd,
    bordered_completion A b c X Y v w hh hd hwv]

/-- Specialize the completed square to the actual Hermitian Gram expression.
The upper-left matrix need not be positive definite for this algebraic identity. -/
theorem hermitian_bordered_determinant [StarRing R]
    (A : Matrix I I R) (b : Matrix I Unit R)
    (X : Matrix K I R) (v : Matrix K Unit R)
    {h d : R} (hh : h ≠ 0) (hd : d ≠ 0) (hhstar : star h = h)
    (hvv : vᴴ * v = (d - h) • (1 : Matrix Unit Unit R)) :
    (fromBlocks A b bᴴ (h • (1 : Matrix Unit Unit R)) +
      (appendColumn X v)ᴴ * appendColumn X v).det =
    d * ((A - h⁻¹ • (b * bᴴ)) +
      (X - h⁻¹ • (v * bᴴ))ᴴ * (1 - d⁻¹ • (v * vᴴ)) *
        (X - h⁻¹ • (v * bᴴ))).det := by
  have hcorner : h • (1 : Matrix Unit Unit R) + vᴴ * v = d • 1 := by
    rw [hvv]
    module
  have hgram : (appendColumn X v)ᴴ * appendColumn X v =
      fromBlocks (Xᴴ * X) (Xᴴ * v) (vᴴ * X) (vᴴ * v) := by
    ext a j
    cases a <;> cases j <;> rfl
  rw [hgram, fromBlocks_add, hcorner]
  simpa [conjTranspose_sub, conjTranspose_smul, conjTranspose_mul,
    star_inv, hhstar] using bordered_determinant A b bᴴ X Xᴴ v vᴴ hh hd hvv

omit [Fintype I] [DecidableEq I] in
/-- The rank-one matrix in the completed square has determinant `h / d`. -/
theorem rank_one_determinant
    (v : Matrix K Unit R) (w : Matrix Unit K R)
    {h d : R} (hd : d ≠ 0)
    (hwv : w * v = (d - h) • (1 : Matrix Unit Unit R)) :
    (1 - d⁻¹ • (v * w)).det = h / d := by
  calc
    _ = (1 - v * (d⁻¹ • w)).det := by rw [Matrix.mul_smul]
    _ = (1 - (d⁻¹ • w) * v).det := det_one_sub_mul_comm _ _
    _ = (1 - (d⁻¹ * (d - h)) • (1 : Matrix Unit Unit R)).det := by
      rw [Matrix.smul_mul, hwv, smul_smul]
    _ = h / d := by simp [Matrix.det_unique]; field_simp; ring

/-- The complex Jacobian and bordered determinant factors cancel exactly.
Here `z = det H`, `h / d = det P`, and `z / h = det S`.
The exponents count complex matrix rows and columns; their squares have
already been incorporated in these positive determinant factors. -/
theorem jacobian_cancellation (i k : ℕ) {h d z : R}
    (hh : h ≠ 0) (hd : d ≠ 0) (hz : z ≠ 0) :
    d⁻¹ ^ (k + i) * (z / h)⁻¹ ^ (k + i) *
      (h / d)⁻¹ ^ i * (z / h) ^ k = z⁻¹ ^ i * d⁻¹ ^ k := by
  simp only [pow_add, div_pow, inv_pow]
  field_simp

#print axioms bordered_completion
#print axioms det_scalar_corner
#print axioms bordered_determinant
#print axioms hermitian_bordered_determinant
#print axioms rank_one_determinant
#print axioms jacobian_cancellation

end CanonicalFrame
