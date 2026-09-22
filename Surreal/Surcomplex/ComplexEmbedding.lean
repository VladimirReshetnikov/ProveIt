import Surreal.Foundations.SignSequenceReal
import Surreal.Surcomplex.Modulus
import Mathlib.Analysis.Complex.Norm

/-!
# Ordinary complex constants in the actual surcomplex field

The ordinary constants in `a:eq:st` use Mathlib's complex numbers. Their
embedding applies the constructed real embedding to both coordinates.
It preserves conjugation and sends the ordinary real norm to the actual
surreal-valued modulus. This is an algebraic embedding; continuity for
the ordinary topology is a separate question.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Embed ordinary complex constants by the actual real embedding in each coordinate. -/
def ofComplex : ℂ →+* Surcomplex.{u} where
  toFun z := ⟨SignSequence.ofReal z.re, SignSequence.ofReal z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by apply Surcomplex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by ext <;> simp [Complex.add_re, Complex.add_im]
  map_mul' z w := by apply Surcomplex.ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

@[simp] theorem ofComplex_re (z : ℂ) : (ofComplex z).re = SignSequence.ofReal z.re := rfl
@[simp] theorem ofComplex_im (z : ℂ) : (ofComplex z).im = SignSequence.ofReal z.im := rfl

theorem ofComplex_injective : Function.Injective (ofComplex : ℂ → Surcomplex.{u}) :=
  ofComplex.injective

@[simp] theorem ofComplex_inj {z w : ℂ} :
    (ofComplex z : Surcomplex.{u}) = ofComplex w ↔ z = w := ofComplex_injective.eq_iff

@[simp] theorem ofComplex_ofReal (r : ℝ) :
    (ofComplex (r : ℂ) : Surcomplex.{u}) = ofReal (SignSequence.ofReal r) := by
  ext <;> simp

@[simp] theorem ofComplex_I : (ofComplex Complex.I : Surcomplex.{u}) = I := by
  ext <;> simp

@[simp] theorem ofComplex_conj (z : ℂ) :
    (ofComplex (star z) : Surcomplex.{u}) = conj (ofComplex z) := by
  ext <;> simp

@[simp] theorem normSq_ofComplex (z : ℂ) :
    normSq (ofComplex z : Surcomplex.{u}) = SignSequence.ofReal (Complex.normSq z) := by
  simp [normSq_eq, Complex.normSq_apply, pow_two]

/-- The norm of an ordinary complex constant, interpreted in the actual sign field. -/
@[simp] theorem modulus_ofComplex (z : ℂ) :
    modulus (ofComplex z : Surcomplex.{u}) = SignSequence.ofReal (norm z) := by
  apply modulus_eq_of_nonneg_sq
  · exact map_nonneg SignSequence.ofReal (norm_nonneg z)
  · rw [normSq_ofComplex, ← map_pow, Complex.sq_norm]

end

end Surreal.Surcomplex
