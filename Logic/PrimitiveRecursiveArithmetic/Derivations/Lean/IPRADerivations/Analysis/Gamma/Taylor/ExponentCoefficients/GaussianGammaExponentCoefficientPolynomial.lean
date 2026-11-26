import IPRADerivations.Analysis.Gamma.Taylor.FinitePolynomials.GaussianGammaLinearCoefficient
import IPRADerivations.Analysis.Gamma.Zeta.Coefficients.GaussianGammaZetaWeightedNorm
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianFiniteExponentialCoefficientMajorant
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponentBound

/-!
# The original finite Gamma exponent coefficient buffer and mass

Actual padding and coefficient addition join the original sampled
(gamma-H_N)z term to the original sampled zeta-tail polynomial. Its
weighted coefficient mass is at most R(N+1)+R^2/N. At the original
cutoff N=2R this is at most the unchanged numerical radius 2R^2+2R.
Consequently its actual finite exponential polynomial has coefficient
mass at most 3^(2R^2+2R), uniformly in all internal sample and Taylor
indices. The full Euler-head polynomial and infinite coefficient
consistency remain separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaExponentCoefficientPolynomial

open_ipra
open GaussianRationalHorner (qadd qmul evaluate ofGaussian)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalPolynomialBuffers (leftPad added)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalSyntheticBounds (natCode)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianGammaCanonicalExponentBound (numericalRadius)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linear (q N L : PTm n) : PTm n := leftPad (GaussianGammaLinearCoefficient.polynomial q N) (succ L)
def polynomial (q N L : PTm n) : PTm n := added (linear q N L) (GaussianGammaZetaCoefficientPolynomial.polynomial q N L) (succ (degree L))
def massNumerator (R N : PTm n) : PTm n := R*succ N*N+R*R
def exponential (q R L K : PTm n) : PTm n := GaussianRationalPolynomialExponential.polynomial (polynomial q (two*R) L) (degree L) K
ipra_subst linear
ipra_subst polynomial
ipra_subst massNumerator
ipra_subst exponential

theorem linear_length (q N L : PTm n) : Γ ⊢[PRAAx] length (linear q N L) ≐ succ (degree L) :=
  (GaussianRationalPolynomialBuffers.pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) (GaussianGammaLinearCoefficient.monomial_length _)).eqTrans (by unfold degree; ipra_ring))
theorem polynomial_length (q N L : PTm n) : Γ ⊢[PRAAx] length (polynomial q N L) ≐ succ (degree L) :=
  GaussianRationalPolynomialBuffers.added_length _ _ _

theorem polynomial_evaluation (q z B N L : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial q N L) (ofGaussian z B) ≐
      qadd (qmul (GaussianGammaLinearCoefficient.coefficient q N) (ofGaussian z B))
        (GaussianRationalFiniteSum.sum GaussianGammaZetaDegreeName.coefficientBody (succ L)
          (GaussianGammaZetaDegreeName.coefficientData q z B N)) :=
  (GaussianRationalPolynomialBuffers.added_evaluation _ _ _ _ (linear_length q N L)
    (GaussianGammaZetaCoefficientPolynomial.polynomial_length q N L)).eqTrans
      (qadd_congr ((GaussianRationalPolynomialBuffers.pad_evaluation _ _ _).eqTrans
        (GaussianGammaLinearCoefficient.monomial_evaluation _ _))
          (GaussianGammaZetaCoefficientPolynomial.polynomial_evaluation q z B N L))

theorem original_tail_observation_binding (p z R B N L : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial (GaussianGammaZetaDegreeName.clock p R) N L) (ofGaussian z B) ≐
      qadd (qmul (GaussianGammaLinearCoefficient.coefficient (GaussianGammaZetaDegreeName.clock p R) N) (ofGaussian z B))
        (GaussianGammaZetaDegreeName.sample p z R B N L) :=
  (polynomial_evaluation _ _ _ _ _).eqTrans
    (qadd_congr (.eqRefl _) (GaussianGammaZetaDegreeName.sample_at _ _ _ _ _ _).eqSymm)

theorem linear_mass (q N L R : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (linear q N L) (degree L) (radiusPoint R one)) (natCode (R*succ N)) := by
  have padding : Γ ⊢[PRAAx] weightedNorm (linear q N L) (degree L) (radiusPoint R one) ≐
      weightedNorm (GaussianGammaLinearCoefficient.polynomial q N) one (radiusPoint R one) :=
    (GaussianFiniteExponentialWeightedNorm.weighted_congr (.eqRefl _)
      (show Γ ⊢[PRAAx] degree L ≐ succ L+one by unfold degree; ipra_ring) (.eqRefl _)).eqTrans
        (GaussianRationalPolynomialDilation.weighted_padding _ one _ (succ L)
          (GaussianGammaLinearCoefficient.monomial_length _))
  exact RationalArgmin.rationalLE_congr padding.eqSymm (.eqRefl _)
    (GaussianGammaLinearCoefficient.polynomial_weighted_bound q N R)

theorem scalar_mass_sum (R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.add (natCode (R*succ N)) (fraction (R*R) N) ≐ fraction (massNumerator R N) N := by
  have rep := RationalRepresentations.represents_add (Γ := Γ) (natCode (R*succ N)) (fraction (R*R) N)
    (ZT.ofNat (R*succ N)) (ZT.ofNat (R*R)) one N
    (GaussianRationalSyntheticBounds.natCode_represents _) (fraction_represents _ _ hN)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hN) rep (fraction_represents _ _ hN)
    (GaussianRationalHorner.positive_product _ _ (le_refl one) hN) hN
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  unfold massNumerator
  ipra_simps
  ring

theorem polynomial_weighted_bound (q N L R : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hh : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial q N L) (degree L) (radiusPoint R one)) (fraction (massNumerator R N) N) := by
  have first := GaussianRationalPolynomialDilation.weighted_added_bound (Γ := Γ)
    (linear q N L) (GaussianGammaZetaCoefficientPolynomial.polynomial q N L) (degree L) (radiusPoint R one)
  have second := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ (linear_mass q N L R)
    (GaussianGammaZetaWeightedNorm.original_tail_weighted_norm q N L R hN hh)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (scalar_mass_sum R N hN) (RationalArgmin.transitive first second)

alias original_cutoff_positive := Common.one_le_two_mul

/-- The exact original C7 numerical exponent radius bounds the actual
original sampled coefficient buffer, independently of sample and degree. -/
theorem original_C7_coefficient_mass (q R L : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial q (two*R) L) (degree L) (radiusPoint R one)) (natCode (numericalRadius R)) :=
  RationalArgmin.transitive (polynomial_weighted_bound q (two*R) L R (original_cutoff_positive R hR) (le_refl _))
    (fraction_order _ _ _ _ (original_cutoff_positive R hR) (le_refl one)
      (le_of_eq_add (d := R*R) (by unfold massNumerator numericalRadius; ipra_ring)))

theorem exponential_coefficient_mass (q R L K : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (exponential q R L K) (K*degree L) (radiusPoint R one))
      (natCode (pw (num 3) (numericalRadius R))) :=
  GaussianFiniteExponentialCoefficientMajorant.polynomial_numerical_majorant _ _ _ _ _
    (polynomial_length q (two*R) L) (original_C7_coefficient_mass q R L hR)

theorem original_exponential_evaluation (q z B R L K : PTm n) : Γ ⊢[PRAAx]
    evaluate (exponential q R L K) (ofGaussian z B) ≐
      GaussianRationalPolynomialExponential.scalarSum
        (qadd (qmul (GaussianGammaLinearCoefficient.coefficient q (two*R)) (ofGaussian z B))
          (GaussianRationalFiniteSum.sum GaussianGammaZetaDegreeName.coefficientBody (succ L)
            (GaussianGammaZetaDegreeName.coefficientData q z B (two*R)))) K :=
  (GaussianRationalPolynomialExponential.polynomial_evaluation _ _ _ _ (polynomial_length q (two*R) L)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl (succ K)) (polynomial_evaluation q z B (two*R) L))

def exponentialF : PR 4 := PTm.toPR (exponential (var 0) (var 1) (var 2) (var 3))
theorem exponential_program (q R L K : PTm n) : Γ ⊢[PRAAx]
    PTm.app exponentialF ![q,R,L,K] ≐ exponential q R L K := by
  simpa [exponentialF] using toPR_eq (Γ := Γ) (exponential (var 0) (var 1) (var 2) (var 3) : PTm 4) ![q,R,L,K]

theorem original_sampled_Gamma_exponent_coefficient_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ rationalLE
      (weightedNorm (polynomial (var 0) (two*var 1) (var 2)) (degree (var 2)) (radiusPoint (var 1) one))
      (natCode (numericalRadius (var 1)))) :=
  closeUniv 3 (.impI (original_C7_coefficient_mass _ _ _ Prf.hyp0))

theorem original_sampled_Gamma_exponential_coefficient_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ rationalLE
      (weightedNorm (exponential (var 0) (var 1) (var 2) (var 3)) (var 3*degree (var 2)) (radiusPoint (var 1) one))
      (natCode (pw (num 3) (numericalRadius (var 1))))) :=
  closeUniv 4 (.impI (exponential_coefficient_mass _ _ _ _ Prf.hyp0))

theorem original_sampled_Gamma_exponential_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app exponentialF ![var 0,var 1,var 2,var 3] ≐ exponential (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (exponential_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaExponentCoefficientPolynomial
