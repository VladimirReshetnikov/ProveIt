import Surreal.Algebra.BinaryFormRigidity
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Projective factors of a nonsingular binary quadratic

The factor prerequisite for `odg:cor:conics`. Nonzero discriminant gives
two distinct projective factors, including the case with zero X² coefficient.
The discriminant condition is the nonsingularity of the symmetric coefficient matrix.
-/

namespace Surreal.BinaryFormRigidity

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The native homogeneous quadratic aX²+bXY+cY². -/
def binaryQuadratic (a b c : K) : MvPolynomial (Fin 2) K :=
  C a * X 0 ^ 2 + C b * X 0 * X 1 + C c * X 1 ^ 2

/-- Four times the determinant of the symmetric matrix is the negative discriminant. -/
theorem binaryQuadratic_matrix_det (a b c : K) :
    4 * Matrix.det (!![a, b / 2; b / 2, c]) = -(b ^ 2 - 4 * a * c) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The coefficient discriminant is nonzero precisely when the symmetric matrix is nonsingular. -/
theorem binaryQuadratic_discriminant_ne_zero_iff (a b c : K) :
    b ^ 2 - 4 * a * c ≠ 0 ↔ Matrix.det (!![a, b / 2; b / 2, c]) ≠ 0 := by
  have h := binaryQuadratic_matrix_det a b c
  constructor
  · intro hn hz
    rw [hz, mul_zero] at h
    exact hn (neg_eq_zero.mp h.symm)
  · intro hn hz
    rw [hz, neg_zero] at h
    exact hn ((mul_eq_zero.mp h).resolve_left (by norm_num))

/-- Rank two of the native symmetric matrix is exactly the nonzero-discriminant condition. -/
theorem binaryQuadratic_rank_two_iff (a b c : K) :
    Matrix.rank (!![a, b / 2; b / 2, c]) = 2 ↔ b ^ 2 - 4 * a * c ≠ 0 := by
  rw [binaryQuadratic_discriminant_ne_zero_iff, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    change Function.Surjective ((!![a, b / 2; b / 2, c]).mulVecLin)
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    change Matrix.rank (!![a, b / 2; b / 2, c]) = Module.finrank K (Fin 2 → K)
    simpa using h
  · intro h
    simpa using Matrix.rank_of_isUnit _ h

/-- A binary quadratic with nonzero discriminant has two projectively distinct factors
over an algebraically closed field of characteristic zero. -/
theorem binaryQuadratic_hasTwoProjectiveFactors [IsAlgClosed K] (a b c : K)
    (hd : b ^ 2 - 4 * a * c ≠ 0) : HasTwoProjectiveFactors (binaryQuadratic a b c) := by
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by simpa using hd
    have he : binaryQuadratic 0 b c = linearForm 0 1 * linearForm b c := by
      simp only [binaryQuadratic, linearForm, map_zero, map_one]
      ring
    refine ⟨0, 1, b, c, by simpa using hb, ?_, ?_⟩
    · rw [he]; exact dvd_mul_right _ _
    · rw [he]; exact dvd_mul_left _ _
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - 4 * a * c) zero_lt_two
    have hrn : r ≠ 0 := by
      intro hz
      apply hd
      rw [← hr, hz, zero_pow (by decide)]
    have he : linearForm (2 * a) (b + r) * linearForm (2 * a) (b - r) =
        C (4 * a) * binaryQuadratic a b c := by
      have hp : (C r : MvPolynomial (Fin 2) K) ^ 2 = C (b ^ 2 - 4 * a * c) := by
        rw [← map_pow, hr]
      simp only [map_sub, map_pow, map_mul, map_ofNat] at hp
      simp only [linearForm, binaryQuadratic, map_add, map_sub, map_mul, map_ofNat]
      linear_combination -(X 1) ^ 2 * hp
    have hu : IsUnit (C (4 * a) : MvPolynomial (Fin 2) K) :=
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) ha)).map C
    refine ⟨2 * a, b + r, 2 * a, b - r, ?_, ?_, ?_⟩
    · intro hz
      have hprod : (4 : K) * a * r = 0 := by linear_combination -hz
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hrn hprod
    · apply hu.dvd_mul_left.mp
      rw [← he]
      exact dvd_mul_right _ _
    · apply hu.dvd_mul_left.mp
      rw [← he]
      exact dvd_mul_left _ _

end
end Surreal.BinaryFormRigidity
