import Surreal.Surcomplex.SineSquareExpansion
import Surreal.Surcomplex.TrigonometricPolynomialDerivative

/-!
# Laurent presentations of the sine-square sharpness examples

The witnesses for `trigonometry:prop:sharp` belong to the same Mathlib
Laurent-polynomial class as the stability theorem. Their coefficients are
finite, and constant perturbations have exactly their scalar valuation.
-/

universe u

namespace Surreal.Surcomplex.SineSquare

open Foundations

noncomputable section

/-- The three Fourier frequencies of `sin² θ - b`. -/
def fourier (b : SignSequence.{u}) : LaurentPolynomial Surcomplex.{u} :=
  LaurentPolynomial.C (ofReal (1 / 2 - b)) +
    LaurentPolynomial.C (ofReal (-1 / 4)) * LaurentPolynomial.T 2 +
    LaurentPolynomial.C (ofReal (-1 / 4)) * LaurentPolynomial.T (-2)

private theorem phaseUnit_zpow_re (a : SignSequence.FiniteElement.{u}) (k : ℤ) :
    ((phaseUnit a ^ k).val).re = finiteCos (k • a) := by
  rw [Units.val_zpow_eq_zpow_val, phaseUnit_val, ← finitePhase_zsmul]
  rfl

/-- The Laurent polynomial evaluates to the actual sine-square family at every finite angle. -/
theorem trigonometricFunction_fourier (b : SignSequence.{u}) (a : SignSequence.FiniteElement.{u}) :
    trigonometricFunction (fourier b) a.val = function b a.val := by
  rw [trigonometricFunction_eq, function_eval]
  simp only [trigonometricPolynomial, fourier, LaurentPolynomial.smeval_add,
    LaurentPolynomial.smeval_C, LaurentPolynomial.smeval_C_mul_T_n, smul_eq_mul,
    mul_one, QuadraticAlgebra.re_add, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    phaseUnit_zpow_re]
  have hpos : (2 : ℤ) • a = 2 * a := by simp [two_smul, two_mul]
  have hneg : (-2 : ℤ) • a = -(2 * a) := by rw [neg_smul, hpos]
  rw [hpos, hneg, finiteCos_neg, finiteCos_two_mul]
  linear_combination -(finiteCos_sq_add_finiteSin_sq a) / 2

/-- The Fourier witness has the expected actual fine derivative at every finite angle. -/
theorem fineHasDerivAt_fourier (b : SignSequence.{u}) (a : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (trigonometricFunction (fourier b)) (slope a) a.val := by
  apply (fineHasDerivAt_function b a).congr_of_eventuallyEq
  filter_upwards [SignSequence.isOpen_setOf_isFinite.mem_nhds a.property] with x hx
  exact (trigonometricFunction_fourier b ⟨x, hx⟩).symm

/-- Every Fourier coefficient is finite whenever the subtracted constant is finite. -/
theorem fourier_finite (b : SignSequence.{u}) (hb : SignSequence.IsFinite b) (n : ℤ) :
    IsFinite ((fourier b).coeff n) := by
  classical
  have hhalf : SignSequence.IsFinite (1 / 2 : SignSequence.{u}) := by
    simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)
  have hquarter : SignSequence.IsFinite (-1 / 4 : SignSequence.{u}) := by
    simpa only [map_div₀, map_neg, map_one, map_ofNat] using SignSequence.finite_ofReal (-1 / 4 : ℝ)
  have hc : IsFinite (ofReal (1 / 2 - b)) :=
    ⟨SignSequence.finite_sub hhalf hb, SignSequence.finite_zero⟩
  have hq : IsFinite (ofReal (-1 / 4) : Surcomplex.{u}) := ⟨hquarter, SignSequence.finite_zero⟩
  have hC : IsFinite ((LaurentPolynomial.C (ofReal (1 / 2 - b))).coeff n) := by
    rw [LaurentPolynomial.C_apply]
    split_ifs
    · exact hc
    · exact finiteSubring.zero_mem
  have hT (k : ℤ) : IsFinite ((LaurentPolynomial.C (ofReal (-1 / 4)) *
      LaurentPolynomial.T k : LaurentPolynomial Surcomplex.{u}).coeff n) := by
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact hq
    · exact finiteSubring.zero_mem
  exact finiteSubring.add_mem (finiteSubring.add_mem hC (hT 2)) (hT (-2))

/-- The one-frequency Laurent polynomial for a real constant perturbation. -/
def constant (d : SignSequence.{u}) : LaurentPolynomial Surcomplex.{u} :=
  LaurentPolynomial.C (ofReal d)

@[simp] theorem trigonometricFunction_constant (d : SignSequence.{u})
    (a : SignSequence.FiniteElement.{u}) : trigonometricFunction (constant d) a.val = d := by
  rw [trigonometricFunction_eq]
  simp only [trigonometricPolynomial, constant, LaurentPolynomial.smeval_C,
    smul_eq_mul, mul_one, ofReal_re]

/-- A constant Fourier perturbation has the specified coefficient valuation bound. -/
theorem constant_coefficient_valuation (d s : SignSequence.{u})
    (hd : SignSequence.valuation d = ↑s) (n : ℤ) :
    (s : WithTop SignSequence.{u}) ≤ valuation ((constant d).coeff n) := by
  classical
  rw [constant, LaurentPolynomial.C_apply]
  split_ifs
  · rw [valuation_ofReal, hd]
  · simp

/-- In particular the nonzero constant frequency attains its stated valuation exactly. -/
@[simp] theorem constant_coefficient_zero_valuation (d : SignSequence.{u}) :
    valuation ((constant d).coeff 0) = SignSequence.valuation d := by
  simp [constant, LaurentPolynomial.C_apply, valuation_ofReal]

end
end Surreal.Surcomplex.SineSquare
