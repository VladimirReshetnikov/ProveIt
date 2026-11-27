import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletReciprocalRow
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalRowElimination
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail

/-!
# The original Dirichlet row at two

The inverse exponential is the original exponential at the reciprocal
base. At native exponent two its logarithmic input is the sum of two
original logarithm names. Exponentiating identifies the actual row
with the literal embedded rational reciprocal square.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletSquareRow

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPositiveScalingConstant (exponentF exponentData exponent_regular inverseF inverseData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianNameArithmetic (addF addData add_fast multiplyModulus)
open GaussianNameBounds (U U_positive)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (add_sample_error multiply_sample_error equivalent_of_envelope through_identity three)
open GaussianRationalHorner (qadd qmul ofGaussian canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "LogData" => GaussianPositiveRationalLogarithm.data

def nativeTwo : PTm n := shifted oneCode one
def squareData (j : PTm n) : PTm n := embed (RationalReciprocalPowerTail.reciprocalPower two j)

@[simp] theorem subst_nativeTwo {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (nativeTwo : PTm n) = nativeTwo := by simp [nativeTwo,one]
ipra_subst squareData [RationalReciprocalPowerTail.reciprocalPower, two, one]

theorem native_two_coefficient : Γ ⊢[PRAAx] ofGaussian (nativeTwo : PTm n) one ≐ qadd qone qone :=
  ((GaussianEulerIntegrationByPartsLinear.coefficient_plus_one nativeTwo one (le_refl one)).eqSymm.eqTrans
    (qadd_congr (.eqRefl _) (GaussianEulerPositiveScalingConstant.shifted_coefficient oneCode one (le_refl one))))

private theorem product_twice (v : PTm n) (hv : Γ ⊢[PRAAx] canonical v) :
    Γ ⊢[PRAAx] qmul (ofGaussian nativeTwo one) v ≐ qadd v v := by
  have e := GaussianPolynomialDeterminantTerms.one_mul_canonical v hv
  exact (qmul_congr native_two_coefficient (.eqRefl _)).eqTrans
    ((GaussianRationalRowElimination.distribute_right qone qone v).eqTrans (qadd_congr e e))

private def exponentBudget (j : PTm n) : PTm n :=
  (multiplyModulus constantF L (ofGaussian nativeTwo one) (LogData one j)+one)+three

private theorem exponent_diagonal (p j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] distanceBounded (ap2 exponentF p (exponentData nativeTwo one one j))
      (ap2 (addF L L) p (addData (LogData one j) (LogData one j))) (exponentBudget j) (unit p) := by
  let c := ofGaussian (nativeTwo : PTm n) one
  let x := LogData one j
  let u := ap2 L p x
  have reg := GaussianPositiveRationalLogarithm.name_regular one j (.andI (le_refl one) hj)
  have first := multiply_sample_error constantF L c x p (constant_regular c) reg
  have first' := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _) first
  have second := add_sample_error L L x x p reg reg
  exact through_identity _ _ _ _ _ _ _ (unit_positive p) first' second
    (product_twice u (GaussianPositiveRationalLogarithm.sample_canonical p one j))

theorem exponent_doubles_log (j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent exponentF (addF L L) (exponentData nativeTwo one one j)
      (addData (LogData one j) (LogData one j)) := by
  have reg := GaussianPositiveRationalLogarithm.name_regular one j (.andI (le_refl one) hj)
  refine equivalent_of_envelope _ _ _ _ (exponentBudget j)
    (exponent_regular nativeTwo one one j (.andI (le_refl one) (.andI (le_refl one) hj))) (add_fast _ _ _ _ reg reg) (.allI ?_)
  have h : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift j) := by
    simpa [Fm.shift,Syn.shift,one] using hj.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,exponentBudget,subst_nativeTwo,
    GaussianEulerPositiveScalingConstant.subst_exponentData,GaussianNameArithmetic.subst_addData,
    GaussianNameArithmetic.subst_multiplyModulus,GaussianRationalHorner.subst_ofGaussian,
    GaussianPositiveRationalLogarithm.subst_data,PTm.subst_add,three,two,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using exponent_diagonal (var 0) (Syn.shift j) h

theorem fraction_square (j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] qmul (GaussianPositiveRationalLogarithm.fraction one j) (GaussianPositiveRationalLogarithm.fraction one j) ≐
      squareData j := by
  have w := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) one j hj
  have e : Γ ⊢[PRAAx] j*j ≐ pw j two :=
    (congrMul (pw_one j).eqSymm (.eqRefl _)).eqTrans (pw_succ j one).eqSymm
  have hJ := GaussianPolynomialPerturbation.power_positive j two hj
  exact (qmul_congr w w).eqTrans ((GaussianDominantPairAlgebra.radius_multiply one j one j hj hj).eqTrans
    ((GaussianDominantPairAlgebra.radius_congr (one_mul one) e).eqTrans
      ((GaussianEulerDecayFactorBounds.fraction_is_radius_point one (pw j two) hJ).eqSymm.eqTrans
        (GaussianEulerDecayOrder.fraction_embedding one (pw j two) hJ).eqSymm)))

/-- Each actual exponential Dirichlet row at s=2 is the literal rational square reciprocal. -/
theorem original_square_row (j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent inverseF constantF (inverseData nativeTwo one j one) (squareData j) := by
  let x := LogData one j
  let R := U L x
  let a := GaussianPositiveRationalLogarithm.fraction one j
  let y := exponentData nativeTwo one one j
  let S := GaussianEulerPositiveScalingConstant.radius nativeTwo one one j
  have hlog : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one j := .andI (le_refl one) hj
  have hi := GaussianPositiveRationalLogarithm.exponential_input one j hlog
  have sumInput := GaussianExponentialReference.add_input L L R x x hi hi
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF (addF L L) S (R+R) y
    (addData x x) (GaussianEulerPositiveScalingConstant.original_input nativeTwo one one j (.andI (le_refl one) hlog))
    sumInput (exponent_doubles_log j hj)
  have square := GaussianArctangentExponentialPeriod.double_exponential_constant L R x a (squareData j) (U_positive L x)
    hi (GaussianPositiveRationalLogarithm.exponential_fraction one j hlog) (fraction_square j hj)
  exact cross_trans _ _ _ _ _ _
    (GaussianGammaZetaDirichletReciprocalRow.inverse_reciprocal nativeTwo one j one (.andI (le_refl one) (.andI hj (le_refl one))))
    (cross_trans _ _ _ _ _ _ exp square)

theorem actual_original_Dirichlet_square_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent inverseF constantF (inverseData nativeTwo one (var 0) one) (squareData (var 0))) :=
  closeUniv 1 (.impI (original_square_row _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletSquareRow
