import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaCofinalCoefficientName
import IPRADerivations.Analysis.Gamma.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTravelScaling
import IPRADerivations.Core.CongruenceTactic

/-!
# Original C7 observations versus an actual computed C19 coefficient prefixValue

The larger-disk cofinal polynomial is truncated through degree d at
precision q+d, guaranteeing enough actual stored coefficients. Its exact
finite M_(2R)*2^(-d-1) tail is transported to the original encoded z/B.
Original C7 radius overlap and whole-polynomial name compatibility give
the independent-observation error M_(2R)*2^(-d-1)+2^(-p)+2^(-q).
The computed coefficient prefixValue is not assumed to have stabilized.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaOriginalC19Prefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul evaluate ofGaussian)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalPowerExpansion (partialSum)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianGammaCanonicalExponent (source)
open GaussianGammaC9Bound (majorant)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (cross_trans cross_symm cross_at)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stage (q d : PTm n) : PTm n := q+d
def buffer (q R d : PTm n) : PTm n := GaussianGammaFiniteCoefficientPolynomial.polynomial
  (GaussianGammaCofinalCoefficientName.coefficientPrecision (stage q d) (two*R)) (two*R)
  (GaussianGammaCofinalCoefficientName.degreeCutoff (stage q d) (two*R))
  (GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q d) (two*R))
def totalDegree (q R d : PTm n) : PTm n := GaussianGammaFiniteCoefficientPolynomial.totalDegree (two*R)
  (GaussianGammaCofinalCoefficientName.degreeCutoff (stage q d) (two*R))
  (GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q d) (two*R))
def prefixValue (q z R B d : PTm n) : PTm n := partialSum (buffer q R d) (totalDegree q R d) (ofGaussian z B) (succ d)
def denominator (d : PTm n) : PTm n := pw two (succ d)
def halfQuery (z R B : PTm n) : PTm n := qmul (radiusPoint one (two*R)) (ofGaussian z B)
@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (q z R B d : PTm n) :
    Syn.subst σ (prefixValue q z R B d) = prefixValue (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp [prefixValue,buffer,totalDegree,stage,GaussianGammaCofinalCoefficientName.coefficientPrecision,
    GaussianGammaCofinalCoefficientName.degreeCutoff,GaussianGammaCofinalCoefficientName.exponentialCutoff,
    GaussianGammaCofinalCoefficientName.exponentClock,GaussianGammaCofinalCoefficientName.inputClock,GaussianGammaCofinalCoefficientName.outerClock]

theorem larger_source (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (two*R) B :=
  .andI (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R h.andE₁)
    (.andI h.andE₂.andE₁ (ComplexLogarithmRemainder.bounded_mono h.andE₂.andE₂
      (le_of_eq_add (d := R*B) (by ipra_ring))))

theorem degree_dominates (q R d : PTm n) : Γ ⊢[PRAAx] le d (totalDegree q R d) := by
  let K := GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q d) (two*R)
  let L := GaussianGammaCofinalCoefficientName.degreeCutoff (stage q d) (two*R)
  have hK : Γ ⊢[PRAAx] le d K := le_trans (le_add_left d q) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (stage q d) (two*R))
  have hL := le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive (Γ := Γ) L)
  have mulBound : Γ ⊢[PRAAx] le K (K*GaussianGammaReciprocalDegreeCells.degree L) :=
    le_congr (by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl K) hL)
  exact le_trans hK (le_trans mulBound (le_add_left _ _))

theorem half_query_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] bounded (halfQuery z R B) one two := by
  have hN := GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R h.andE₁
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hN (le_refl one)
    (GaussianDominantPairAlgebra.radius_bounded one (two*R) hN) (GaussianGammaSynchronousExponentName.query_bound z R B h)
  apply GaussianMonicResidualRadius.bounded_cancel _ one two R (le_succ_self one) h.andE₁
  exact bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) product

theorem query_recovery (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    qmul (radiusPoint (two*R) one) (halfQuery z R B) ≐ ofGaussian z B := by
  have inv := (GaussianRationalPowerAlgebra.qmul_commutative (Γ := Γ) (radiusPoint (two*R) one) (radiusPoint one (two*R))).eqTrans
    (GaussianRationalTravelScaling.inverse_radius (two*R) one
      (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R h.andE₁) (le_refl one))
  exact (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr inv (.eqRefl _)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianRationalHorner.ofGaussian_canonical _ _ h.andE₂.andE₁)))

theorem prefix_query_congr (C N u v k : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx] partialSum C N u k ≐ partialSum C N v k := by
  ipra_congr (partialSum (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl C, .eqRefl N, h, .eqRefl k]

theorem finite_prefix_tail (q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaCofinalCoefficientName.sample (stage q d) z (two*R) B)
      (prefixValue q z R B d) (majorant (two*R)) (denominator d) := by
  have hS := larger_source z R B h
  have finite := GaussianGammaFiniteCoefficientPolynomial.original_finite_C19_tail
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (stage q d) (two*R)) (two*R)
    (GaussianGammaCofinalCoefficientName.degreeCutoff (stage q d) (two*R))
    (GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q d) (two*R)) d (halfQuery z R B)
    hS.andE₁ (degree_dominates q R d) (half_query_bound z R B h)
  have actual := distance_congr (GaussianRationalMonicReduction.evaluate_congr (.eqRefl (buffer q R d)) (query_recovery z R B h))
    (prefix_query_congr (buffer q R d) (totalDegree q R d) _ _ (succ d) (query_recovery z R B h)) (.eqRefl _) (.eqRefl _) finite
  exact distance_congr (GaussianGammaCofinalCoefficientName.actual_polynomial_observation (stage q d) z (two*R) B h.andE₂.andE₁)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) actual

theorem original_to_polynomial (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B)
      (GaussianGammaCofinalCoefficientName.sample (stage q d) z (two*R) B) (unit p+unit q) (unit p*unit q) := by
  have hS := larger_source z R B h
  have he := cross_trans _ _ _ _ _ _ (GaussianGammaCofinalCoefficientName.original_C7_identity z (two*R) B hS)
    (GaussianGammaRadiusOverlap.original_P_overlap z (two*R) R B hS h)
  have original := cross_at _ _ _ _ p (stage q d) (cross_symm _ _ _ _ he)
  have later : Γ ⊢[PRAAx] le (unit q) (unit (stage q d)) :=
    GaussianFactorBudget.power_monotone_length two q (stage q d) (le_succ_self one) (le_add_right q d)
  have budget : Γ ⊢[PRAAx] le ((unit p+unit (stage q d))*(unit p*unit q))
      ((unit p+unit q)*(unit p*unit (stage q d))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit p*unit q*unit (stage q d)) (mul_le_mul_right (unit p*unit p) later))
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive (stage q d)))
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)) budget original

/-- The ORIGINAL C7 name is compared to the actual computed prefixValue at
independent observation precisions, with the exact original C19 constant. -/
theorem original_C19_observation_bound (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (prefixValue q z R B d)
      (rateNumerator (majorant (two*R)) (denominator d) p q) (rateDenominator (denominator d) p q) := by
  let Z := rateDenominator (denominator d) p q
  have hD : Γ ⊢[PRAAx] le one (denominator d) := unit_positive (succ d)
  have hU := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have hZ := GaussianNamedInverseRate.denominator_positive (Γ := Γ) (denominator d) p q hD
  have before := distance_radius_mono _ _ _ _ ((denominator d)*(unit p+unit q)) Z hU hZ
    (le_of_eq_add (d := zero) (by dsimp only [Z]; unfold rateDenominator; ipra_ring)) (original_to_polynomial p q z R B d h)
  have after := distance_radius_mono _ _ _ _ (majorant (two*R)*unit p*unit q) Z hD hZ
    (le_of_eq_add (d := zero) (by dsimp only [Z]; unfold rateDenominator; ipra_ring)) (finite_prefix_tail q z R B d h)
  exact bound_congr (.eqRefl _) (by unfold rateNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ before after)

def prefixF : PR 5 := PTm.toPR (prefixValue (var 0) (var 1) (var 2) (var 3) (var 4))
theorem prefix_program (q z R B d : PTm n) : Γ ⊢[PRAAx] PTm.app prefixF ![q,z,R,B,d] ≐ prefixValue q z R B d := by
  simpa [prefixF] using toPR_eq (Γ := Γ) (prefixValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![q,z,R,B,d]

theorem original_C7_computed_coefficient_prefix_C19_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) ⟶ distanceBounded
      (GaussianGammaC7Name.sample (var 0) (var 2) (var 3) (var 4)) (prefixValue (var 1) (var 2) (var 3) (var 4) (var 5))
      (rateNumerator (majorant (two*var 3)) (denominator (var 5)) (var 0) (var 1))
      (rateDenominator (denominator (var 5)) (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_C19_observation_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaOriginalC19Prefix
