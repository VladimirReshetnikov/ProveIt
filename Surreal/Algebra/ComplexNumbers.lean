import Surreal.Algebra.Complexify
import Mathlib.Data.Complex.Basic

/-!
# The real quadratic algebra and Mathlib's complex numbers

The coefficient fields in `polynomial:eq:workspace` are Mathlib's `ℝ` and
`ℂ`. This file identifies the project's quadratic-algebra model over `ℝ`
with `ℂ`, preserving the real embedding, imaginary unit, and conjugation.
-/

namespace Surreal.Complexify

noncomputable section

/-- The coordinate-preserving identification `ℝ[i] ≃+* ℂ`. -/
def complexEquiv : Complexify ℝ ≃+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' z w := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  map_add' _ _ := rfl

@[simp] theorem complexEquiv_re (z : Complexify ℝ) :
    (complexEquiv z).re = z.re := rfl

@[simp] theorem complexEquiv_im (z : Complexify ℝ) :
    (complexEquiv z).im = z.im := rfl

@[simp] theorem complexEquiv_symm_re (z : ℂ) :
    (complexEquiv.symm z).re = z.re := rfl

@[simp] theorem complexEquiv_symm_im (z : ℂ) :
    (complexEquiv.symm z).im = z.im := rfl

@[simp] theorem complexEquiv_algebraMap (r : ℝ) :
    complexEquiv (algebraMap ℝ (Complexify ℝ) r) = (r : ℂ) := rfl

@[simp] theorem complexEquiv_I : complexEquiv (I : Complexify ℝ) = Complex.I := rfl

@[simp] theorem complexEquiv_conj (z : Complexify ℝ) :
    complexEquiv (star z) = star (complexEquiv z) := by
  apply Complex.ext <;> simp

end

end Surreal.Complexify
