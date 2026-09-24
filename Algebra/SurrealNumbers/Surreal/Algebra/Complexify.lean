import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite algebra for surcomplexification

This is Layer A of `docs/foundations-and-computation/foundations/article.tex`.
The carrier is mathlib's quadratic algebra with relation `i² = -1`, so its
multiplication has the cross terms in `found:eq:pairmul`.

The field construction below proves the ordered-field part of
`found:prop:complex`. It does not assert algebraic closedness or construct the
surreal field. Norm squares take values in the base field.
-/

namespace Surreal

/-- The quadratic algebra `F[i]`, with its own multiplication. -/
abbrev Complexify (F : Type*) [CommRing F] := QuadraticAlgebra F (-1) 0

namespace Complexify

section Ring

variable {F : Type*} [CommRing F]

/-- The imaginary unit of the quadratic algebra. -/
def I : Complexify F := ⟨0, 1⟩

@[simp] theorem I_re : (I : Complexify F).re = 0 := rfl
@[simp] theorem I_im : (I : Complexify F).im = 1 := rfl

/-- The real component of `found:eq:pairmul`. -/
@[simp] theorem mul_re (z w : Complexify F) :
    (z * w).re = z.re * w.re - z.im * w.im := by
  simp [QuadraticAlgebra.re_mul, sub_eq_add_neg]

/-- The imaginary component of `found:eq:pairmul`. -/
@[simp] theorem mul_im (z w : Complexify F) :
    (z * w).im = z.re * w.im + z.im * w.re := by
  simp [QuadraticAlgebra.im_mul]

/-- `found:eq:conj`: conjugation fixes the real coordinate. -/
@[simp] theorem conj_re (z : Complexify F) : (star z).re = z.re := by simp

/-- `found:eq:conj`: conjugation negates the imaginary coordinate. -/
@[simp] theorem conj_im (z : Complexify F) : (star z).im = -z.im := by simp

@[simp] theorem I_sq : (I : Complexify F) ^ 2 = -1 := by
  ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- Conjugation is an involution, with no order hypothesis. -/
theorem conj_conj (z : Complexify F) : star (star z) = z := star_star z

theorem conj_mul (z w : Complexify F) : star (z * w) = star z * star w := by
  rw [star_mul, mul_comm]

/-- The base-field-valued norm square, requiring no square roots. -/
def normSq (z : Complexify F) : F := z.re ^ 2 + z.im ^ 2

theorem normSq_eq_norm (z : Complexify F) : normSq z = QuadraticAlgebra.norm z := by
  simp [normSq, QuadraticAlgebra.norm_def, pow_two]

@[simp] theorem normSq_zero : normSq (0 : Complexify F) = 0 := by simp [normSq]
@[simp] theorem normSq_one : normSq (1 : Complexify F) = 1 := by
  simp [normSq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
@[simp] theorem normSq_I : normSq (I : Complexify F) = 1 := by simp [normSq]

/-- The sum-of-two-squares identity used in `a:prop:triangle`. -/
theorem normSq_mul (z w : Complexify F) : normSq (z * w) = normSq z * normSq w := by
  simp only [normSq_eq_norm, map_mul]

@[simp] theorem normSq_conj (z : Complexify F) : normSq (star z) = normSq z := by
  simp [normSq]

@[simp] theorem normSq_neg (z : Complexify F) : normSq (-z) = normSq z := by
  simp [normSq]

/-- `z * conjugate z` is the embedded norm square. -/
theorem mul_conj (z : Complexify F) :
    z * star z = algebraMap F (Complexify F) (normSq z) := by
  rw [normSq_eq_norm, QuadraticAlgebra.algebraMap_norm_eq_mul_star]

/-- The two-dimensional Gram identity, `found:eq:gram`. -/
theorem gram_identity (a b c d : F) :
    (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring

end Ring

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The irreducibility condition required by the quadratic-algebra field
instance follows from order; real closedness is not needed. -/
instance noRootNegOne : Fact (∀ r : F, r ^ 2 ≠ (-1 : F) + 0 * r) :=
  ⟨fun r h => by have := sq_nonneg r; simp only [zero_mul, add_zero] at h; linarith⟩

/-- The ordered-field part of `found:prop:complex`. -/
noncomputable example : Field (Complexify F) := inferInstance

theorem normSq_nonneg (z : Complexify F) : 0 ≤ normSq z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

@[simp] theorem normSq_eq_zero_iff (z : Complexify F) : normSq z = 0 ↔ z = 0 := by
  rw [normSq_eq_norm, QuadraticAlgebra.norm_eq_zero_iff_eq_zero]

theorem normSq_pos {z : Complexify F} (hz : z ≠ 0) : 0 < normSq z :=
  lt_of_le_of_ne (normSq_nonneg z) (Ne.symm (mt (normSq_eq_zero_iff z).mp hz))

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Inversion is conjugation divided by the norm square (`found:eq:pairinv`). -/
theorem inv_eq (z : Complexify F) : z⁻¹ = (normSq z)⁻¹ • star z := by
  rw [normSq_eq_norm]
  rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem inv_re (z : Complexify F) : (z⁻¹).re = z.re / normSq z := by
  simp [inv_eq, div_eq_mul_inv, mul_comm]

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem inv_im (z : Complexify F) : (z⁻¹).im = -z.im / normSq z := by
  simp [inv_eq, div_eq_mul_inv, mul_comm]

/-- `found:eq:cauchyschwarz`, without a square-root operation. -/
theorem cauchy_schwarz_sq (a b c d : F) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have := gram_identity a b c d
  have := sq_nonneg (a * d - b * c)
  linarith

end OrderedField

end Complexify
end Surreal
