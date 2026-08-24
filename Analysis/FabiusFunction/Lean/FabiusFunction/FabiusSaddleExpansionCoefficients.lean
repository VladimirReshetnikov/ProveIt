import FabiusFunction.FabiusSaddlePolynomialCoefficients
import FabiusFunction.GaussianPolynomialContraction
import FabiusFunction.SaddleLogExpansionAlgebra
import FabiusFunction.FabiusFirstSaddleCorrection
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Gaussian mass and logarithmic coefficients for the Fabius saddle expansion

The polynomial exponent coefficients are first exponentiated by the generic
`SaddleExpansion.expCoeff` recurrence and then contracted against normalized
Gaussian moments.  Odd half-orders disappear before this module, so the
public mass coefficients are indexed by integer powers `lambda⁻¹`: order `j`
contracts exponential coefficient `2 * j`.

Coefficientwise conjugation proves that every contracted mass coefficient is
real.  A continuous-polynomial lift packages the same recurrence over
continuous maps, proving continuity; one-periodicity then gives global
boundedness.  Applying the generic `logCoeff` recurrence produces the real
logarithmic coefficients with the same regularity.  Finally, the first
coefficient is identified with the closed periodic correction already used
by the first-order saddle theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open SaddleExpansion

noncomputable section

/-- Complex Gaussian mass coefficient at order `lambda^{-j}`. -/
def fabiusSaddleMassCoefficientComplex (j : ℕ) (t : ℝ) : ℂ :=
  gaussianPolynomialContraction
    (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) (2 * j))

theorem fabiusSaddleMassCoefficientComplex_star (j : ℕ) (t : ℝ) :
    star (fabiusSaddleMassCoefficientComplex j t) =
      fabiusSaddleMassCoefficientComplex j t := by
  apply gaussianPolynomialContraction_star_eq_self
  exact negativeLaplaceExpCoeff_even_conj j t

/-- The real Gaussian mass coefficient at order `lambda^{-j}`. -/
def fabiusSaddleMassCoefficient (j : ℕ) (t : ℝ) : ℝ :=
  (fabiusSaddleMassCoefficientComplex j t).re

theorem ofReal_fabiusSaddleMassCoefficient (j : ℕ) (t : ℝ) :
    (fabiusSaddleMassCoefficient j t : ℂ) =
      fabiusSaddleMassCoefficientComplex j t := by
  exact Complex.conj_eq_iff_re.mp (by
    simpa only [Complex.star_def] using
      fabiusSaddleMassCoefficientComplex_star j t)

@[simp] theorem fabiusSaddleMassCoefficientComplex_zero (t : ℝ) :
    fabiusSaddleMassCoefficientComplex 0 t = 1 := by
  unfold fabiusSaddleMassCoefficientComplex
  simp only [mul_zero, expCoeff_zero]
  simpa only [Polynomial.C_1] using gaussianPolynomialContraction_C (1 : ℂ)

@[simp] theorem fabiusSaddleMassCoefficient_zero (t : ℝ) :
    fabiusSaddleMassCoefficient 0 t = 1 := by
  simp [fabiusSaddleMassCoefficient]

theorem fabiusSaddleMassCoefficientComplex_periodic (j : ℕ) :
    Function.Periodic (fabiusSaddleMassCoefficientComplex j) 1 := by
  intro t
  unfold fabiusSaddleMassCoefficientComplex
  exact congrArg gaussianPolynomialContraction
    (negativeLaplaceExpCoeff_periodic (2 * j) t)

theorem fabiusSaddleMassCoefficient_periodic (j : ℕ) :
    Function.Periodic (fabiusSaddleMassCoefficient j) 1 := by
  intro t
  unfold fabiusSaddleMassCoefficient
  rw [fabiusSaddleMassCoefficientComplex_periodic j t]

private def negativeLaplaceBoundedExponentJetContinuousMap
    (n : ℕ) : C(ℝ, ℂ) where
  toFun t := (negativeLaplaceBoundedExponentJet n t : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (contDiff_infty_negativeLaplaceBoundedExponentJet n).continuous

private def negativeLaplaceExponentPolynomialContinuous
    (m : ℕ) : Polynomial C(ℝ, ℂ) :=
  match m with
  | 0 => 0
  | n + 1 =>
      Polynomial.C
          ((Complex.I ^ (n + 1) / ((n + 1).factorial : ℕ)) •
            negativeLaplaceBoundedExponentJetContinuousMap n) *
            Polynomial.X ^ (n + 1) +
        Polynomial.C (ContinuousMap.const ℝ
          (Complex.I ^ (n + 3) * (negativeLaplaceJetSlope (n + 2) : ℂ) /
            ((n + 3).factorial : ℕ))) * Polynomial.X ^ (n + 3)

private theorem negativeLaplaceExponentPolynomialContinuous_map
    (m : ℕ) (t : ℝ) :
    (negativeLaplaceExponentPolynomialContinuous m).map
        (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom =
      negativeLaplaceExponentPolynomial m t := by
  cases m with
  | zero => simp [negativeLaplaceExponentPolynomialContinuous,
      negativeLaplaceExponentPolynomial]
  | succ n =>
      simp [negativeLaplaceExponentPolynomialContinuous,
        negativeLaplaceExponentPolynomial,
        negativeLaplaceBoundedExponentJetContinuousMap]
      rw [← Polynomial.C_mul]
      congr 1
      ring

private def gaussianPolynomialContractionContinuous
    (p : Polynomial C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  p.sum fun n c =>
    c * ContinuousMap.const ℝ (normalizedGaussianMoment n)

private theorem gaussianPolynomialContractionContinuous_apply
    (p : Polynomial C(ℝ, ℂ)) (t : ℝ) :
    gaussianPolynomialContractionContinuous p t =
      gaussianPolynomialContraction
        (p.map (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      unfold gaussianPolynomialContractionContinuous
      rw [Polynomial.sum_add_index]
      · change gaussianPolynomialContractionContinuous p t +
            gaussianPolynomialContractionContinuous q t = _
        rw [hp, hq, Polynomial.map_add, map_add]
      · intro n
        simp
      · intro n a b
        simp [add_mul]
  | monomial n c =>
      simp [gaussianPolynomialContractionContinuous,
        gaussianPolynomialContraction_monomial]

private def fabiusSaddleMassCoefficientComplexContinuousMap
    (j : ℕ) : C(ℝ, ℂ) :=
  gaussianPolynomialContractionContinuous
    (expCoeff negativeLaplaceExponentPolynomialContinuous (2 * j))

private theorem fabiusSaddleMassCoefficientComplexContinuousMap_apply
    (j : ℕ) (t : ℝ) :
    fabiusSaddleMassCoefficientComplexContinuousMap j t =
      fabiusSaddleMassCoefficientComplex j t := by
  rw [fabiusSaddleMassCoefficientComplexContinuousMap,
    gaussianPolynomialContractionContinuous_apply]
  unfold fabiusSaddleMassCoefficientComplex
  change gaussianPolynomialContraction
      ((Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
        (expCoeff negativeLaplaceExponentPolynomialContinuous (2 * j))) = _
  rw [map_expCoeff
    (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
    negativeLaplaceExponentPolynomialContinuous (2 * j)]
  congr 1
  apply expCoeff_congr (2 * j)
  intro m _hm
  exact negativeLaplaceExponentPolynomialContinuous_map m t

theorem continuous_fabiusSaddleMassCoefficientComplex (j : ℕ) :
    Continuous (fabiusSaddleMassCoefficientComplex j) := by
  have hfun :
      (fabiusSaddleMassCoefficientComplexContinuousMap j : ℝ → ℂ) =
        fabiusSaddleMassCoefficientComplex j := by
    funext t
    exact fabiusSaddleMassCoefficientComplexContinuousMap_apply j t
  rw [← hfun]
  exact (fabiusSaddleMassCoefficientComplexContinuousMap j).continuous

theorem continuous_fabiusSaddleMassCoefficient (j : ℕ) :
    Continuous (fabiusSaddleMassCoefficient j) := by
  exact Complex.continuous_re.comp
    (continuous_fabiusSaddleMassCoefficientComplex j)

theorem isBounded_range_fabiusSaddleMassCoefficientComplex (j : ℕ) :
    Bornology.IsBounded (Set.range (fabiusSaddleMassCoefficientComplex j)) :=
  (fabiusSaddleMassCoefficientComplex_periodic j).isBounded_of_continuous
    one_ne_zero (continuous_fabiusSaddleMassCoefficientComplex j)

theorem isBounded_range_fabiusSaddleMassCoefficient (j : ℕ) :
    Bornology.IsBounded (Set.range (fabiusSaddleMassCoefficient j)) :=
  (fabiusSaddleMassCoefficient_periodic j).isBounded_of_continuous
    one_ne_zero (continuous_fabiusSaddleMassCoefficient j)

/-- Logarithmic coefficient at order `lambda^{-j}`. -/
def fabiusSaddleLogCoefficient (j : ℕ) (t : ℝ) : ℝ :=
  logCoeff (fun k => fabiusSaddleMassCoefficient k t) j

@[simp] theorem fabiusSaddleLogCoefficient_zero (t : ℝ) :
    fabiusSaddleLogCoefficient 0 t = 0 := by
  simp [fabiusSaddleLogCoefficient]

@[simp] theorem fabiusSaddleLogCoefficient_one (t : ℝ) :
    fabiusSaddleLogCoefficient 1 t = fabiusSaddleMassCoefficient 1 t := by
  simp [fabiusSaddleLogCoefficient]

theorem fabiusSaddleLogCoefficient_periodic (j : ℕ) :
    Function.Periodic (fabiusSaddleLogCoefficient j) 1 := by
  intro t
  unfold fabiusSaddleLogCoefficient
  apply logCoeff_congr j
  intro k _hk
  exact fabiusSaddleMassCoefficient_periodic k t

private def fabiusSaddleMassCoefficientContinuousMap
    (j : ℕ) : C(ℝ, ℝ) where
  toFun := fabiusSaddleMassCoefficient j
  continuous_toFun := continuous_fabiusSaddleMassCoefficient j

private def fabiusSaddleLogCoefficientContinuousMap
    (j : ℕ) : C(ℝ, ℝ) :=
  logCoeff fabiusSaddleMassCoefficientContinuousMap j

private theorem fabiusSaddleLogCoefficientContinuousMap_apply
    (j : ℕ) (t : ℝ) :
    fabiusSaddleLogCoefficientContinuousMap j t =
      fabiusSaddleLogCoefficient j t := by
  unfold fabiusSaddleLogCoefficientContinuousMap fabiusSaddleLogCoefficient
  change (ContinuousMap.evalAlgHom ℚ ℝ t)
      (logCoeff fabiusSaddleMassCoefficientContinuousMap j) = _
  rw [map_logCoeff (ContinuousMap.evalAlgHom ℚ ℝ t)
    fabiusSaddleMassCoefficientContinuousMap j]
  rfl

theorem continuous_fabiusSaddleLogCoefficient (j : ℕ) :
    Continuous (fabiusSaddleLogCoefficient j) := by
  have hfun : (fabiusSaddleLogCoefficientContinuousMap j : ℝ → ℝ) =
      fabiusSaddleLogCoefficient j := by
    funext t
    exact fabiusSaddleLogCoefficientContinuousMap_apply j t
  rw [← hfun]
  exact (fabiusSaddleLogCoefficientContinuousMap j).continuous

theorem isBounded_range_fabiusSaddleLogCoefficient (j : ℕ) :
    Bornology.IsBounded (Set.range (fabiusSaddleLogCoefficient j)) :=
  (fabiusSaddleLogCoefficient_periodic j).isBounded_of_continuous
    one_ne_zero (continuous_fabiusSaddleLogCoefficient j)

private theorem negativeLaplaceExponentPolynomial_one (t : ℝ) :
    negativeLaplaceExponentPolynomial 1 t =
      Polynomial.C ((fabiusFirstSaddleOddLinear t : ℂ) * Complex.I) *
          Polynomial.X +
        Polynomial.C ((1 / 3 : ℂ) * Complex.I) * Polynomial.X ^ 3 := by
  simp only [negativeLaplaceExponentPolynomial]
  unfold fabiusFirstSaddleOddLinear
  rw [negativeLaplaceBoundedExponentJet_zero]
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  norm_num [negativeLaplaceJetSlope]
  ring

private theorem negativeLaplaceExponentPolynomial_two (t : ℝ) :
    negativeLaplaceExponentPolynomial 2 t =
      Polynomial.C (fabiusFirstSaddleEvenQuadratic t : ℂ) *
          Polynomial.X ^ 2 +
        Polynomial.C (1 / 4 : ℂ) * Polynomial.X ^ 4 := by
  simp only [negativeLaplaceExponentPolynomial]
  unfold fabiusFirstSaddleEvenQuadratic
  rw [negativeLaplaceBoundedExponentJet_one]
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  norm_num [negativeLaplaceJetSlope]
  ring_nf
  simp

private theorem expCoeff_two (E : ℕ → Polynomial ℂ) :
    expCoeff E 2 = E 2 + (1 / 2 : ℂ) • (E 1 * E 1) := by
  have hone : expCoeff E 1 = E 1 := by
    rw [show 1 = 0 + 1 by omega, expCoeff_succ]
    norm_num
  rw [show 2 = 1 + 1 by omega, expCoeff_succ]
  norm_num [Finset.sum_range_succ]
  rw [hone]
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply]
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  norm_num
  ring

private theorem expCoeff_two_negativeLaplaceExponentPolynomial (t : ℝ) :
    expCoeff (fun m => negativeLaplaceExponentPolynomial m t) 2 =
      Polynomial.C
          ((fabiusFirstSaddleEvenQuadratic t : ℂ) -
            (1 / 2 : ℂ) * (fabiusFirstSaddleOddLinear t : ℂ) ^ 2) *
          Polynomial.X ^ 2 +
        Polynomial.C
            ((1 / 4 : ℂ) -
              (1 / 3 : ℂ) * (fabiusFirstSaddleOddLinear t : ℂ)) *
            Polynomial.X ^ 4 +
          Polynomial.C (-1 / 18 : ℂ) * Polynomial.X ^ 6 := by
  rw [expCoeff_two, negativeLaplaceExponentPolynomial_one,
    negativeLaplaceExponentPolynomial_two]
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Algebra.smul_def,
    Polynomial.algebraMap_apply]
  norm_num
  ring_nf
  norm_num [Complex.I_sq]

private theorem gaussianPolynomialContraction_C_mul_X_pow
    (c : ℂ) (n : ℕ) :
    gaussianPolynomialContraction (Polynomial.C c * Polynomial.X ^ n) =
      c * normalizedGaussianMoment n := by
  rw [Polynomial.C_mul']
  simp

theorem fabiusSaddleMassCoefficientComplex_one (t : ℝ) :
    fabiusSaddleMassCoefficientComplex 1 t =
      (fabiusFirstSaddleCorrection t : ℂ) := by
  unfold fabiusSaddleMassCoefficientComplex
  rw [show 2 * 1 = 2 by omega,
    expCoeff_two_negativeLaplaceExponentPolynomial]
  simp only [map_add, gaussianPolynomialContraction_C_mul_X_pow]
  norm_num [normalizedGaussianMoment]
  have hcorrection := congrArg Complex.ofReal
    (fabiusFirstSaddleCorrection_eq_gaussian_contraction t)
  norm_num at hcorrection ⊢
  rw [hcorrection]
  ring

theorem fabiusSaddleMassCoefficient_one (t : ℝ) :
    fabiusSaddleMassCoefficient 1 t = fabiusFirstSaddleCorrection t := by
  apply Complex.ofReal_injective
  rw [ofReal_fabiusSaddleMassCoefficient,
    fabiusSaddleMassCoefficientComplex_one]

theorem fabiusSaddleLogCoefficient_one_eq_firstSaddleCorrection (t : ℝ) :
    fabiusSaddleLogCoefficient 1 t = fabiusFirstSaddleCorrection t := by
  rw [fabiusSaddleLogCoefficient_one, fabiusSaddleMassCoefficient_one]

end

end Fabius
