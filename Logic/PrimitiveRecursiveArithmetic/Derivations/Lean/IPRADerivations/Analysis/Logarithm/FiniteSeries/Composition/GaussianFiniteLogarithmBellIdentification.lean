import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmCoefficientRecursion
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmLinearRecursion

/-!
# Literal finite exponential coefficients are the original Bell coefficients

Both sides of the actual bounded coefficient recursion are proved by
constructors: the SAME H_d finite composition and a concrete two-entry
1+X buffer. Checked bounded uniqueness identifies their low coefficients.
The comparison is then linked to the ORIGINAL signed Bell program's
numerator and factorial denominator, normalized as a Gaussian-rational
value. All cutoffs are explicit. No analytic C4 limit is asserted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmBellIdentification

open_ipra
open GaussianRationalHorner (ofGaussian represents canonical canonical_unique)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical canonicalCoefficients rescale_to)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianFiniteLogarithmPolynomial (composition polynomial)
open GaussianFiniteLogarithmLinearRecursion (linear linear_length linear_canonical linear_low linear_high)
open GaussianRationalCoefficientRecursion (prefixEqual)
open GaussianRationalEulerCoefficients (euler)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedFraction (c D : PTm n) : PTm n :=
  ofGaussian (ComplexLogarithmRemainder.code (LogarithmExponentialCoefficients.value c) (ZT.ofNat zero)) D
def bellValue (e : PTm n) : PTm n := signedFraction
  (fstT (ap1 LogarithmExponentialCoefficients.rationalCoefficientF e))
  (sndT (ap1 LogarithmExponentialCoefficients.rationalCoefficientF e))
ipra_subst signedFraction
ipra_subst bellValue
theorem signed_fraction_congr {c c' D D' : PTm n} (hc : Γ ⊢[PRAAx] c ≐ c') (hD : Γ ⊢[PRAAx] D ≐ D') :
    Γ ⊢[PRAAx] signedFraction c D ≐ signedFraction c' D' := by
  ipra_congr (signedFraction (var 0) (var 1) : PTm 2) with [hc, hD]
theorem bell_congr {e f : PTm n} (h : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx] bellValue e ≐ bellValue f :=
  signed_fraction_congr (congrFst (congrAp1 LogarithmExponentialCoefficients.rationalCoefficientF h))
    (congrSnd (congrAp1 LogarithmExponentialCoefficients.rationalCoefficientF h))

theorem bell_formula (e : PTm n) : Γ ⊢[PRAAx] bellValue e ≐
    signedFraction (LogarithmExponentialCoefficients.coefficientCode e) (fact e) :=
  signed_fraction_congr
    (LogarithmExponentialCoefficients.rationalCoefficient_at e).fstE
    (LogarithmExponentialCoefficients.rationalCoefficient_at e).sndE

theorem signed_fraction_one (c D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] ZT.eq (LogarithmExponentialCoefficients.value c) (ZT.ofNat D)) :
    Γ ⊢[PRAAx] signedFraction c D ≐ qone := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.code (LogarithmExponentialCoefficients.value c) (ZT.ofNat zero))
      (ComplexLogarithmRemainder.scale D ComplexLogarithmRemainder.oneCode) := by
    have h := ZT.toZ_eq hc
    apply GaussianRootAlgebra.equal_of_values
    · simpa only [ComplexLogarithmRemainder.eval_re_code,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,mul_one] using h
    · simp only [ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat,
        Q.mk_zero,map_zero]
      ring
  exact canonical_unique _ _ _ D (GaussianRationalHorner.ofGaussian_canonical _ _ hD) qone_canonical hD
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hD))
    (rescale_to _ _ one D D (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one)) (one_mul D))

theorem signed_fraction_zero (c D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] ZT.eq (LogarithmExponentialCoefficients.value c) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] signedFraction c D ≐ GaussianRationalHorner.qzero := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.code (LogarithmExponentialCoefficients.value c) (ZT.ofNat zero))
      ComplexLogarithmRemainder.zeroCode := by
    apply GaussianRootAlgebra.equal_of_values
    · simpa [ComplexLogarithmRemainder.eval_re_code,GaussianRootAlgebra.re_zero,ZT.toZ_natLit] using ZT.toZ_eq hc
    · simp only [ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_zero,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  exact canonical_unique _ _ _ D (GaussianRationalHorner.ofGaussian_canonical _ _ hD) qzero_canonical hD
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hD)) (GaussianRationalHorner.zero_represents D)

theorem bell_zero : Γ ⊢[PRAAx] bellValue (zero : PTm n) ≐ qone :=
  (bell_formula zero).eqTrans (signed_fraction_one _ _ (GaussianRationalPolynomialExponential.factorial_positive zero)
    LogarithmExponentialCoefficients.rational_initial_zero)
theorem bell_one : Γ ⊢[PRAAx] bellValue (one : PTm n) ≐ qone :=
  (bell_formula one).eqTrans (signed_fraction_one _ _ (GaussianRationalPolynomialExponential.factorial_positive one)
    LogarithmExponentialCoefficients.rational_initial_one)
theorem bell_high (e : PTm n) (he : Γ ⊢[PRAAx] le two e) : Γ ⊢[PRAAx] bellValue e ≐ GaussianRationalHorner.qzero :=
  (bell_formula e).eqTrans (signed_fraction_zero _ _ (GaussianRationalPolynomialExponential.factorial_positive e)
    (LogarithmExponentialCoefficients.coefficient_vanish_above e he))

theorem bell_linear (e : PTm n) : Γ ⊢[PRAAx] bellValue e ≐ exponentCoefficient linear one e := by
  refine .orE (zero_or_succ e) ?_ ?_
  · exact ((bell_congr Prf.hyp0).eqTrans bell_zero).eqTrans
      ((linear_low zero (zero_le one)).eqSymm.eqTrans
        (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))
  · refine .orE (zero_or_succ (pred e)) ?_ ?_
    · have hE : ((pred e ≐ zero) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact ((bell_congr hE).eqTrans bell_one).eqTrans
        ((linear_low one (le_refl one)).eqSymm.eqTrans
          (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) hE.eqSymm))
    · have hE : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx]
          e ≐ succ (succ (pred (pred e))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hTwo : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le two e :=
        le_congr (.eqRefl _) hE.eqSymm (le_of_eq_add (d := pred (pred e)) (by ipra_ring))
      exact (bell_high e hTwo).eqTrans (linear_high e hTwo).eqSymm

theorem composition_linear_prefix (d K R : PTm n) (hd : Γ ⊢[PRAAx] le R d) (hK : Γ ⊢[PRAAx] le R K) : Γ ⊢[PRAAx]
    prefixEqual (composition d K) (K*d) linear one R :=
  GaussianRationalCoefficientRecursion.uniqueness _ _ _ _ _ _ R
    (GaussianRationalPolynomialExponential.polynomial_length _ _ _) (GaussianRationalPolynomialExponential.polynomial_canonical _ _ _)
    linear_length linear_canonical (GaussianFiniteLogarithmCoefficientRecursion.logarithm_recursion d K R hd hK)
    (GaussianFiniteLogarithmLinearRecursion.linear_recursion d R hd)
    ((GaussianFiniteLogarithmCoefficientRecursion.logarithm_constant d K).eqTrans (linear_low zero (zero_le one)).eqSymm)

theorem composition_bell (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (composition d K) (K*d) e ≐ bellValue e :=
  (GaussianRationalCoefficientRecursion.prefix_at _ _ _ _ e e (composition_linear_prefix d K e he hK) (le_refl e)).eqTrans
    (bell_linear e).eqSymm

theorem composition_low (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K)
    (hLow : Γ ⊢[PRAAx] le e one) : Γ ⊢[PRAAx] exponentCoefficient (composition d K) (K*d) e ≐ qone :=
  (composition_bell d K e he hK).eqTrans ((bell_linear e).eqTrans (linear_low e hLow))
theorem composition_high (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K)
    (hHigh : Γ ⊢[PRAAx] le two e) : Γ ⊢[PRAAx] exponentCoefficient (composition d K) (K*d) e ≐ GaussianRationalHorner.qzero :=
  (composition_bell d K e he hK).eqTrans (bell_high e hHigh)

def bellF : PR 1 := PTm.toPR (bellValue (var 0))
def output (d K e : PTm n) : PTm n := pairT (composition d K) (bellValue e)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d K e : PTm n) : PTm n := ap3 outputF d K e
ipra_subst output
ipra_subst run

theorem bell_program_at (e : PTm n) : Γ ⊢[PRAAx] ap1 bellF e ≐ bellValue e := by
  simpa [bellF,ap1] using toPR_eq (Γ := Γ) (bellValue (var 0) : PTm 1) ![e]
theorem program_at (d K e : PTm n) : Γ ⊢[PRAAx] run d K e ≐ output d K e := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,K,e]
theorem returned_composition (d K e : PTm n) : Γ ⊢[PRAAx] fstT (run d K e) ≐ composition d K :=
  (program_at d K e).fstE
theorem returned_bell (d K e : PTm n) : Γ ⊢[PRAAx] sndT (run d K e) ≐ bellValue e :=
  (program_at d K e).sndE
theorem returned_identification (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (fstT (run d K e)) (K*d) e ≐ sndT (run d K e) :=
  (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_composition d K e) (.eqRefl _) (.eqRefl _)).eqTrans
    ((composition_bell d K e he hK).eqTrans (returned_bell d K e).eqSymm)

theorem original_finite_composition_linear_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ prefixEqual (composition (var 0) (var 1)) (var 1*var 0) linear one (var 2)) :=
  closeUniv 3 (.impI (.impI (composition_linear_prefix _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_finite_composition_bell_identification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ exponentCoefficient (composition (var 0) (var 1)) (var 1*var 0) (var 2) ≐ bellValue (var 2)) :=
  closeUniv 3 (.impI (.impI (composition_bell _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_finite_composition_initial_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ le (var 2) one ⟶
      exponentCoefficient (composition (var 0) (var 1)) (var 1*var 0) (var 2) ≐ qone) :=
  closeUniv 3 (.impI (.impI (.impI (composition_low _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem original_finite_composition_higher_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ le two (var 2) ⟶
      exponentCoefficient (composition (var 0) (var 1)) (var 1*var 0) (var 2) ≐ GaussianRationalHorner.qzero) :=
  closeUniv 3 (.impI (.impI (.impI (composition_high _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_original_bell_initial_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (bellValue (zero : PTm 0) ≐ qone ⋏ bellValue (one : PTm 0) ≐ qone) := .andI bell_zero bell_one
theorem actual_original_signed_bell_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (bellValue (var 0) ≐ signedFraction (LogarithmExponentialCoefficients.coefficientCode (var 0)) (fact (var 0))) :=
  closeUniv 1 (bell_formula _)
theorem actual_original_bell_value_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 bellF (var 0) ≐ bellValue (var 0)) := closeUniv 1 (bell_program_at _)
theorem actual_finite_composition_bell_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem original_returned_finite_composition_bell_identification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ exponentCoefficient (fstT (run (var 0) (var 1) (var 2))) (var 1*var 0) (var 2) ≐
      sndT (run (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (returned_identification _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmBellIdentification
