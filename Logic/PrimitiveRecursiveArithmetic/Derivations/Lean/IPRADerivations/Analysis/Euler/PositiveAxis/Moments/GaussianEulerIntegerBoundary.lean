import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Normalization.GaussianEulerUnitNormalizationIntegrand
import IPRADerivations.Analysis.Euler.Integration.Parts.Recurrences.GaussianEulerIntegrationByPartsParameterShiftObservation
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues

/-!
# Original Euler boundary values at the actual positive integer trajectory

At each fixed requested p, genuine numerical QF induction compares the
original integrand at argument i with the literal time power i times the
original decay observation. Its primitive-recursive accumulated error is
explicit. Both original normalized names are regular, so a fixed envelope
removes that coefficient and gives exact independent named observations.
No Gamma or incomplete-Gamma integer formula is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegerBoundary

open_ipra
open GaussianGammaFactorialValues (argument)
open GaussianPositiveRationalLogarithm (source fraction)
open GaussianEulerIntegrandName (nameF data sample decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianRationalReciprocal (power)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def integerData (i a b : PTm n) : PTm n := data (argument i) one a b
def point (p i a b : PTm n) : PTm n := sample p (argument i) one a b
def monomial (i a b : PTm n) : PTm n := power (fraction a b) i
def rawProduct (p i a b : PTm n) : PTm n := qmul (monomial i a b) (ap2 decayF p (decayData a b))
def productF : PR 2 := GaussianNameArithmetic.multiplyF constantF decayF
def productData (i a b : PTm n) : PTm n := GaussianNameArithmetic.multiplyData constantF decayF (monomial i a b) (decayData a b)
def productModulus (i a b : PTm n) : PTm n := GaussianNameArithmetic.multiplyModulus constantF decayF (monomial i a b) (decayData a b)
def errorF : PR 2 := rec2 (zero : PTm 1) ((var 2)*var 1+(var 2+one))
def error (i a _b : PTm n) : PTm n := ap2 errorF i a
def errorLaw (p i a b : PTm n) : Fm PTm n := distanceBounded (point p i a b) (rawProduct p i a b) (error i a b) (unit p)
def envelope (i a b : PTm n) : PTm n := error i a b+(productModulus i a b+one)

ipra_subst integerData
ipra_subst point
ipra_subst monomial
ipra_subst rawProduct
ipra_subst productData
ipra_subst productModulus
ipra_subst error
ipra_subst errorLaw
ipra_subst envelope

theorem error_zero (a b : PTm n) : Γ ⊢[PRAAx] error zero a b ≐ zero := by
  simpa [error,errorF] using rec2_zero (Γ := Γ) (zero : PTm 1) ((var 2)*var 1+(var 2+one)) a

theorem error_succ (i a b : PTm n) : Γ ⊢[PRAAx] error (succ i) a b ≐ a*error i a b+(a+one) := by
  have h := rec2_succ (Γ := Γ) (zero : PTm 1) ((var 2)*var 1+(var 2+one)) i a
  simpa only [error,errorF,PTm.subst_add,PTm.subst_mul,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h

theorem integerData_succ (i a b : PTm n) : Γ ⊢[PRAAx]
    integerData (succ i) a b ≐ data (GaussianGammaEulerHeadShift.shifted (argument i) one) one a b := by
  simpa [integerData,argument] using Prf.eqCongr1 (Γ := Γ)
    (data (var 0) one (Syn.shift a) (Syn.shift b))
    (GaussianGammaShiftTrajectory.point_succ ComplexLogarithmRemainder.oneCode one i)

private theorem sample_argument_congr (p z w a b : PTm n) (h : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx]
    sample p z one a b ≐ sample p w one a b := by
  ipra_congr (sample (var 0) (var 1) one (var 2) (var 3) : PTm 4) with [.eqRefl p, h, .eqRefl a, .eqRefl b]

theorem raw_zero (p a b : PTm n) : Γ ⊢[PRAAx] rawProduct p zero a b ≐ ap2 decayF p (decayData a b) := by
  have canonical : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 decayF p (decayData a b)) :=
    GaussianRadiusExponentialName.sample_canonical constantF
      (GaussianNameBounds.U constantF (GaussianEulerIntegrandName.decayPoint a b)) p (GaussianEulerIntegrandName.decayPoint a b)
  exact (qmul_congr (GaussianRationalReciprocal.power_zero _) (.eqRefl _)).eqTrans
    (GaussianPolynomialDeterminantTerms.one_mul_canonical _ canonical)

theorem raw_succ (p i a b : PTm n) : Γ ⊢[PRAAx]
    qmul (fraction a b) (rawProduct p i a b) ≐ rawProduct p (succ i) a b :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    (qmul_congr ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalReciprocal.power_succ _ _).eqSymm) (.eqRefl _))

theorem fixed_precision_base (p a b : PTm n) : Γ ⊢[PRAAx] errorLaw p zero a b := by
  have exactPoint : Γ ⊢[PRAAx] point p zero a b ≐ ap2 decayF p (decayData a b) :=
    (sample_argument_congr p _ _ a b (GaussianGammaShiftTrajectory.point_zero ComplexLogarithmRemainder.oneCode one)).eqTrans
    (GaussianEulerUnitNormalizationIntegrand.original_sample_is_decay p a b)
  exact distance_congr exactPoint.eqSymm (raw_zero p a b).eqSymm (error_zero a b).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero _ (unit p) (unit_positive p))

theorem successor_observation (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (point p (succ i) a b) (qmul (fraction a b) (point p i a b)) (a+one) (unit p) := by
  have native := sample_argument_congr (Γ := Γ) p _ _ a b
    (GaussianGammaShiftTrajectory.point_succ ComplexLogarithmRemainder.oneCode one i)
  have upper : Γ ⊢[PRAAx] le a (a*b) := le_congr (one_mul a) (mul_comm b a) (mul_le_mul_right a h.andE₂)
  exact distance_congr native.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerIntegrationByPartsParameterShiftObservation.original_diagonal p (argument i) one a b a (.andI (le_refl one) h) upper)

theorem fixed_precision_step (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b)
    (ih : Γ ⊢[PRAAx] errorLaw p i a b) : Γ ⊢[PRAAx] errorLaw p (succ i) a b := by
  have timeBound := GaussianEulerExponentCompactBounds.fraction_bound a b a h.andE₂
    (le_congr (one_mul a) (mul_comm b a) (mul_le_mul_right a h.andE₂))
  have product := GaussianApproximateInverseDistance.multiply_distance (fraction a b) (point p i a b) (rawProduct p i a b)
    a (error i a b) (unit p) (unit_positive p) timeBound ih
  have next := distance_congr (.eqRefl _) (raw_succ p i a b) (.eqRefl _) (.eqRefl _) product
  have total := distance_triangle_same _ _ _ _ _ _ (unit_positive p) (successor_observation p i a b h) next
  exact distance_congr (.eqRefl _) (.eqRefl _)
    ((by ipra_ring : Γ ⊢[PRAAx] (a+one)+a*error i a b ≐ a*error i a b+(a+one)).eqTrans (error_succ i a b).eqSymm) (.eqRefl _) total

/-- This induction fixes the actual observation p and ranges only over
one numerical Gaussian distance formula at the original integer input. -/
theorem original_fixed_precision_error (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] errorLaw p i a b := by
  have hall : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift p) (var 0) (Syn.shift a) (Syn.shift b)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using fixed_precision_base (Γ := Γ) p a b
    · have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using h.shift
      simpa only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        fixed_precision_step (Syn.shift p) (var 0) (Syn.shift a) (Syn.shift b) hs.wk Prf.hyp0
  simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

theorem sample_error (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (integerData i a b))
      (qmul (monomial i a b) (ap2 decayF p (decayData a b))) (error i a b) (unit p) :=
  distance_congr (GaussianEulerIntegrandName.sample_at p (argument i) one a b) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (original_fixed_precision_error p i a b h)

theorem product_regular (i a b : PTm n) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN productF (productData i a b) :=
  GaussianNameArithmetic.multiply_fast constantF decayF _ _ (constant_regular _) (GaussianEulerHalfDecayProduct.decay_regular a b)

theorem original_diagonal (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (integerData i a b)) (ap2 productF p (productData i a b)) (envelope i a b) (unit p) := by
  have product := GaussianNameRingLaws.multiply_sample_error (Γ := Γ) constantF decayF (monomial i a b) (decayData a b) p
    (constant_regular _) (GaussianEulerHalfDecayProduct.decay_regular a b)
  have raw : Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData i a b)) (rawProduct p i a b) (productModulus i a b+one) (unit p) :=
    distance_congr (.eqRefl _) (qmul_congr (constant_at p _) (.eqRefl _)) (.eqRefl _) (.eqRefl _) product
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (integerData i a b)) (rawProduct p i a b) (error i a b) (unit p) :=
    sample_error p i a b h
  exact distance_triangle_same (ap2 nameF p (integerData i a b)) (rawProduct p i a b) (ap2 productF p (productData i a b))
    (error i a b) (productModulus i a b+one) (unit p) (unit_positive p) first
    (distance_symmetric _ _ _ _ (unit_positive p) raw)

theorem original_integer_boundary (i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent nameF productF (integerData i a b) (productData i a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope nameF productF (integerData i a b) (productData i a b) (envelope i a b)
    (GaussianEulerIntegrandName.name_regular (argument i) one a b (.andI (le_refl one) h)) (product_regular i a b)
  unfold GaussianValueNormalizerExtensionality.rawDiagonal
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [subst_integerData,subst_productData,subst_envelope,Syn.shift,GaussianCoefficientNameBounds.unit,
    GaussianEuclideanPointDistance.unit] using
    original_diagonal (var 0) (Syn.shift i) (Syn.shift a) (Syn.shift b) hs

theorem original_observations (p q i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (point p i a b) (ap2 productF q (productData i a b)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (GaussianEulerIntegrandName.sample_at p (argument i) one a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cross_at _ _ _ _ p q (original_integer_boundary i a b h))

theorem actual_original_integer_Euler_boundary_fixed_query_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 2) (var 3) ⟶ errorLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (original_fixed_precision_error _ _ _ _ Prf.hyp0))
theorem actual_original_integer_Euler_boundary_identification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶ crossEquivalent nameF productF (integerData (var 0) (var 1) (var 2)) (productData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_integer_boundary _ _ _ Prf.hyp0))
theorem actual_original_successor_integer_Euler_boundary_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 3) (var 4) ⟶ distanceBounded (point (var 0) (succ (var 2)) (var 3) (var 4))
      (ap2 productF (var 1) (productData (succ (var 2)) (var 3) (var 4)))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (original_observations _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegerBoundary
