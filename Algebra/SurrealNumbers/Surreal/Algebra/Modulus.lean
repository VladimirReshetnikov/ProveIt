import Surreal.Algebra.Complexify
import Surreal.Algebra.OrderedSquareRoots
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Base-field-valued modulus

The modulus identities of `a:prop:triangle` in
`docs/surcomplex/analysis/article.tex`, over any ordered field in which
nonnegative elements have square roots (in particular, any real closed field).
This is the square-root part of Layer A. No real-valued norm or topology is
installed on the quadratic extension.
-/

namespace Surreal.Complexify

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F]

/-- The square-root property supplies a nonnegative root. -/
theorem exists_nonneg_sq {x : F} (hx : 0 ≤ x) : ∃ y : F, 0 ≤ y ∧ y ^ 2 = x := by
  exact HasNonnegSquareRoots.exists_nonneg_sq hx

/-- The modulus has values in `F`, including its infinite and infinitesimal scales. -/
noncomputable def modulus (z : Complexify F) : F :=
  Classical.choose (exists_nonneg_sq (normSq_nonneg z))

theorem modulus_nonneg (z : Complexify F) : 0 ≤ modulus z :=
  (Classical.choose_spec (exists_nonneg_sq (normSq_nonneg z))).1

@[simp] theorem modulus_sq (z : Complexify F) : modulus z ^ 2 = normSq z :=
  (Classical.choose_spec (exists_nonneg_sq (normSq_nonneg z))).2

theorem modulus_eq_of_nonneg_sq {z : Complexify F} {r : F}
    (hr : 0 ≤ r) (hsq : r ^ 2 = normSq z) : modulus z = r :=
  (sq_eq_sq₀ (modulus_nonneg z) hr).mp ((modulus_sq z).trans hsq.symm)

@[simp] theorem modulus_zero : modulus (0 : Complexify F) = 0 :=
  modulus_eq_of_nonneg_sq le_rfl (by simp)

@[simp] theorem modulus_one : modulus (1 : Complexify F) = 1 :=
  modulus_eq_of_nonneg_sq zero_le_one (by simp)

@[simp] theorem modulus_I : modulus (I : Complexify F) = 1 :=
  modulus_eq_of_nonneg_sq zero_le_one (by simp)

@[simp] theorem modulus_eq_zero_iff (z : Complexify F) : modulus z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply (normSq_eq_zero_iff z).mp
    rw [← modulus_sq, hz, zero_pow (by decide : 2 ≠ 0)]
  · rintro rfl
    exact modulus_zero

theorem modulus_pos {z : Complexify F} (hz : z ≠ 0) : 0 < modulus z :=
  lt_of_le_of_ne (modulus_nonneg z) (Ne.symm (mt (modulus_eq_zero_iff z).mp hz))

@[simp] theorem modulus_conj (z : Complexify F) : modulus (star z) = modulus z :=
  modulus_eq_of_nonneg_sq (modulus_nonneg z) (by simp)

@[simp] theorem modulus_neg (z : Complexify F) : modulus (-z) = modulus z :=
  modulus_eq_of_nonneg_sq (modulus_nonneg z) (by simp)

@[simp] theorem modulus_algebraMap (x : F) :
    modulus (algebraMap F (Complexify F) x) = |x| :=
  modulus_eq_of_nonneg_sq (abs_nonneg x) (by simp [normSq])

/-- The multiplicative identity in `a:prop:triangle`. -/
theorem modulus_mul (z w : Complexify F) : modulus (z * w) = modulus z * modulus w :=
  modulus_eq_of_nonneg_sq (mul_nonneg (modulus_nonneg z) (modulus_nonneg w))
    (by simp [mul_pow, normSq_mul])

theorem re_dot_le (z w : Complexify F) :
    z.re * w.re + z.im * w.im ≤ modulus z * modulus w := by
  apply (le_abs_self _).trans
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (modulus_nonneg z) (modulus_nonneg w))).mp
  simpa [mul_pow, normSq] using cauchy_schwarz_sq z.re z.im w.re w.im

/-- The triangle inequality in `a:prop:triangle`. -/
theorem modulus_add_le (z w : Complexify F) : modulus (z + w) ≤ modulus z + modulus w := by
  apply (sq_le_sq₀ (modulus_nonneg _) (add_nonneg (modulus_nonneg z) (modulus_nonneg w))).mp
  have h := re_dot_le z w
  have hz := modulus_sq z
  have hw := modulus_sq w
  rw [modulus_sq]
  simp only [normSq, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] at *
  nlinarith

/-- The real-coordinate estimate in `a:prop:triangle`. -/
theorem abs_re_le_modulus (z : Complexify F) : |z.re| ≤ modulus z := by
  apply (sq_le_sq₀ (abs_nonneg _) (modulus_nonneg z)).mp
  simp only [sq_abs, modulus_sq, normSq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The imaginary-coordinate estimate in `a:prop:triangle`. -/
theorem abs_im_le_modulus (z : Complexify F) : |z.im| ≤ modulus z := by
  apply (sq_le_sq₀ (abs_nonneg _) (modulus_nonneg z)).mp
  simp only [sq_abs, modulus_sq, normSq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The inverse formula in `a:prop:triangle`, including the zero convention. -/
theorem inv_eq_modulus (z : Complexify F) : z⁻¹ = (modulus z ^ 2)⁻¹ • star z := by
  rw [modulus_sq, inv_eq]

end Surreal.Complexify
