import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaLinearCoefficient
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaExponentStep

/-!
# The original Euler factor as an actual stored coefficient buffer

The original reciprocal point 1/(i+1) supplies the linear coefficient.
Its actual two-entry polynomial evaluates to the unchanged original
Euler factor 1+(z/B)/(i+1), and has weighted coefficient mass at radius R
at most 1+R. Numerical i and R are arbitrary internal indices.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerFactorPolynomial

open_ipra
open GaussianRationalHorner (qadd qmul evaluate ofGaussian)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianRationalPolynomialBuffers (leftPad added)
open GaussianRationalMonicReduction (singleton)
open GaussianGammaLinearCoefficient (monomial monomial_length)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalSyntheticBounds (natCode)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianRationalL1 (qL1)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def constant : PTm n := leftPad (singleton qone) one
def polynomial (i : PTm n) : PTm n := added (monomial (reciprocalPoint i)) constant two
ipra_subst constant
ipra_subst polynomial

theorem reciprocal_norm (i : PTm n) : Γ ⊢[PRAAx] rationalLE (qL1 (reciprocalPoint i)) (natCode one) :=
  RationalArgmin.rationalLE_congr
    (GaussianFiniteLogarithmWeightedNorm.l1_from_representation _ _ _ _ (zero_lt_succ i)
      (GaussianRationalHorner.ofGaussian_represents _ _ (zero_lt_succ i)) GaussianL1.norm1_one).eqSymm (.eqRefl _)
        (fraction_order one (succ i) one one (zero_lt_succ i) (le_refl one)
          (le_congr (by ipra_ring) (by ipra_ring) (zero_lt_succ i)))

theorem constant_length : Γ ⊢[PRAAx] length (constant : PTm n) ≐ two :=
  (GaussianRationalPolynomialBuffers.pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) (GaussianRationalMonicReduction.singleton_length qone)).eqTrans (by ipra_ring))
theorem polynomial_length (i : PTm n) : Γ ⊢[PRAAx] length (polynomial i) ≐ two :=
  GaussianRationalPolynomialBuffers.added_length _ _ _

theorem constant_evaluation (z : PTm n) : Γ ⊢[PRAAx] evaluate constant z ≐ qone :=
  (GaussianRationalPolynomialBuffers.pad_evaluation _ _ _).eqTrans
    ((GaussianRationalMonicReduction.singleton_evaluation qone z).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ GaussianRationalSyntheticDivision.qone_canonical))

theorem original_factor_evaluation (i z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (polynomial i) (ofGaussian z B) ≐ GaussianGammaEulerHead.factor i z B :=
  (GaussianRationalPolynomialBuffers.added_evaluation _ _ _ _ (monomial_length _) constant_length).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_evaluation _ _) (constant_evaluation _)).eqTrans
      ((qadd_congr (GaussianGammaExponentStep.reciprocal_times_point z B i hB) (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qadd_commutative _ _)))

theorem constant_mass (R : PTm n) : Γ ⊢[PRAAx] weightedNorm constant one (radiusPoint R one) ≐ natCode one :=
  (GaussianFiniteExponentialWeightedNorm.weighted_congr (.eqRefl _)
    (show Γ ⊢[PRAAx] one ≐ one+zero by ipra_ring) (.eqRefl _)).eqTrans
      ((GaussianRationalPolynomialDilation.weighted_padding (singleton qone) zero _ one
        (GaussianRationalMonicReduction.singleton_length qone)).eqTrans
          (GaussianFiniteExponentialWeightedNorm.singleton_weighted_norm _))

theorem linear_mass (i R : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (monomial (reciprocalPoint i)) one (radiusPoint R one)) (natCode R) := by
  have first := GaussianGammaLinearCoefficient.monomial_weighted_bound (Γ := Γ) (reciprocalPoint i) R
  have second := GaussianFiniteExponentialWeightedNorm.multiply_bounds (Γ := Γ)
    (qL1 (reciprocalPoint i)) (natCode R) (natCode one) (natCode R)
    (GaussianRationalSyntheticBounds.natCode_nonnegative R) (GaussianRationalSyntheticBounds.natCode_nonnegative one)
    (reciprocal_norm i) (RationalArgmin.reflexive _)
  have budget := (GaussianRationalSyntheticBounds.natCode_multiply (Γ := Γ) one R).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (show Γ ⊢[PRAAx] one*R ≐ R by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) budget (RationalArgmin.transitive first second)

theorem polynomial_mass (i R : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial i) one (radiusPoint R one)) (natCode (one+R)) := by
  have first := GaussianRationalPolynomialDilation.weighted_added_bound (Γ := Γ)
    (monomial (reciprocalPoint i)) constant one (radiusPoint R one)
  have second := GaussianRationalSyntheticBounds.add_monotone (Γ := Γ) _ _ _ _ (linear_mass i R)
    (RationalArgmin.rationalLE_congr (constant_mass R).eqSymm (.eqRefl _) (RationalArgmin.reflexive _))
  have budget := (GaussianRationalSyntheticBounds.natCode_add (Γ := Γ) R one).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (show Γ ⊢[PRAAx] R+one ≐ one+R by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) budget (RationalArgmin.transitive first second)

theorem original_Euler_factor_polynomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ evaluate (polynomial (var 0)) (ofGaussian (var 1) (var 2)) ≐
      GaussianGammaEulerHead.factor (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (original_factor_evaluation _ _ _ Prf.hyp0))
theorem original_Euler_factor_coefficient_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (weightedNorm (polynomial (var 0)) one (radiusPoint (var 1) one)) (natCode (one+var 1))) :=
  closeUniv 2 (polynomial_mass _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerFactorPolynomial
