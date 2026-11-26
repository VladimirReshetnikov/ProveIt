import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap

/-!
# Retiming the stored Barnes exponent at a fixed finite tail cutoff

Only the frozen prefactor samples can change between the two readings.
The literal constant and higher coefficients agree exactly, and the
linear and quadratic rows share their entire finite tail contributions.
The same coefficient mass budget therefore applies at every fixed cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorFixedCutoff

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer
  (buffer coefficient entry_at linearCoefficient quadraticCoefficient highCoefficient prefactorLinear prefactorQuadratic)
open GaussianBarnesCanonicalExponentTaylorCoefficientCauchy (stored clockNumerator clockDenominator linearGain)
open GaussianBarnesCanonicalExponentTaylorCoefficientMassGap (difference massError)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefactor (negativeHalf quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorExponentDerivative (twicePoint)
open GaussianBarnesCanonicalPrefactorLipschitz (halfGain)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCoefficientUniformNorm (difference_uniform_of_degree_bounds)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianNameBounds (sample_bound)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (sum_left_error sum_right_error)
open GaussianNamedDifferenceQuotient (scale_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian qmul qzero positive_product)
open GaussianEuclideanDistanceName (fraction_order)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Signum (sg)
open RationalArithmetic (select select_zero select_one)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem clock_denominator_positive (q t : PTm n) : Γ ⊢[PRAAx] le one (clockDenominator q t) :=
  positive_product _ _ (unit_positive q) (unit_positive t)

private theorem half_bound : Γ ⊢[PRAAx] bounded (negativeHalf : PTm n) halfGain one :=
  bound_congr (constant_at zero negativeHalf) (.eqRefl _) (.eqRefl _)
    (sample_bound constantF negativeHalf zero (constant_regular negativeHalf))

private theorem quadratic_gap (q t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (prefactorQuadratic q) (prefactorQuadratic t)
      (clockNumerator q t halfGain) (clockDenominator q t) :=
  scale_distance negativeHalf _ _ halfGain (unit q+unit t) (clockDenominator q t)
    (clock_denominator_positive q t) half_bound
    (point_at quadraticCoefficientF quadraticCoefficientData q t quadratic_coefficient_regular)

private theorem linear_gap (q t z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (prefactorLinear q z B) (prefactorLinear t z B)
      (clockNumerator q t (linearGain R)) (clockDenominator q t) := by
  let D := clockDenominator q t
  let A := unit q+unit t
  let c := twicePoint z B
  let x := ofGaussian z B
  have dpos := clock_denominator_positive (Γ := Γ) q t
  have hx := GaussianGammaEulerHead.fraction_disk z R B hz.andE₁ hz.andE₂
  have hc : Γ ⊢[PRAAx] bounded c (R+R) one :=
    GaussianRationalPowerDifference.bounded_sum_same x x R R one (le_refl one) hx hx
  have stirling := point_at GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero) q t
    (GaussianStirlingConstant.name_regular (Γ := Γ) zero)
  have quadratic := point_at quadraticCoefficientF quadraticCoefficientData q t
    (quadratic_coefficient_regular (Γ := Γ))
  have mul := scale_distance c _ _ (R+R) A D dpos hc quadratic
  have sum := sum_right_error qone _ _ _ _ dpos mul
  have pref := scale_distance negativeHalf _ _ halfGain ((R+R)*A) D dpos half_bound sum
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold clockNumerator linearGain A; ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ dpos stirling pref)

private theorem enlarge_gain (q t x y A K : PTm n) (hK : Γ ⊢[PRAAx] le A K)
    (h : Γ ⊢[PRAAx] distanceBounded x y (clockNumerator q t A) (clockDenominator q t)) : Γ ⊢[PRAAx]
    distanceBounded x y (clockNumerator q t K) (clockDenominator q t) :=
  distance_radius_mono _ _ _ _ _ _ (clock_denominator_positive q t) (clock_denominator_positive q t)
    (mul_le_mul_right _ (mul_le_mul_right _ hK)) h

private theorem select_distance (bit a b c d A D : PTm n)
    (hBit : Γ ⊢[PRAAx] (bit ≐ zero) ⋎ (bit ≐ one))
    (hZero : Γ ⊢[PRAAx] distanceBounded a c A D) (hOne : Γ ⊢[PRAAx] distanceBounded b d A D) : Γ ⊢[PRAAx]
    distanceBounded (select bit a b) (select bit c d) A D :=
  .orE hBit
    (distance_congr (select_zero bit a b Prf.hyp0).eqSymm (select_zero bit c d Prf.hyp0).eqSymm
      (.eqRefl _) (.eqRefl _) hZero.wk)
    (distance_congr (select_one bit a b Prf.hyp0).eqSymm (select_one bit c d Prf.hyp0).eqSymm
      (.eqRefl _) (.eqRefl _) hOne.wk)

private theorem coefficient_gap (q t z R B r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (coefficient q z R B r e) (coefficient t z R B r e)
      (clockNumerator q t (prefactorGain R)) (clockDenominator q t) := by
  let D := clockDenominator q t
  let K := prefactorGain R
  let A := clockNumerator q t K
  have dpos := clock_denominator_positive (Γ := Γ) q t
  have fixed (x : PTm n) : Γ ⊢[PRAAx] distanceBounded x x A D :=
    distance_radius_mono _ _ _ _ _ _ dpos dpos
      (le_congr (zero_mul D).eqSymm (.eqRefl _) (zero_le _))
      (GaussianRationalPowerDifference.distance_refl_zero x D dpos)
  have add_linear := sum_left_error (prefactorLinear q z B) (prefactorLinear t z B)
    (GaussianBarnesCanonicalHeadCorrectionDerivative.slope z B (initial R)) _ D dpos (linear_gap q t z R B hz)
  have linear : Γ ⊢[PRAAx] distanceBounded (linearCoefficient q z R B r) (linearCoefficient t z R B r) A D :=
    enlarge_gain q t _ _ _ K (le_add_right _ _)
      (sum_left_error _ _ (GaussianBarnesCanonicalDerivativeTail.value z B (initial R) r) _ D dpos add_linear)
  have add_quadratic := sum_left_error (prefactorQuadratic q) (prefactorQuadratic t)
    (qmul (radiusPoint one two) (harmonicPoint (initial R))) _ D dpos (quadratic_gap q t)
  have quadratic : Γ ⊢[PRAAx] distanceBounded (quadraticCoefficient q z R B r) (quadraticCoefficient t z R B r) A D :=
    enlarge_gain q t _ _ _ K (le_add_left _ _)
      (sum_left_error _ _ (qmul (radiusPoint one two) (GaussianBarnesCanonicalSecondDerivativeTail.value z B (initial R) r))
        _ D dpos add_quadratic)
  have high := fixed (highCoefficient z R B r (monus e (num 3)))
  exact select_distance (sg e) _ _ _ _ A D (Common.sg_zero_or_one e) (fixed qzero)
    (select_distance (sg (monus e one)) _ _ _ _ A D (Common.sg_zero_or_one _) linear
      (select_distance (sg (monus e two)) _ _ _ _ A D (Common.sg_zero_or_one _) quadratic high))

theorem entry_gap (q t z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) : Γ ⊢[PRAAx]
    distanceBounded (stored q z R B r M e) (stored t z R B r M e)
      (clockNumerator q t (prefactorGain R)) (clockDenominator q t) :=
  distance_congr (entry_at q z R B r M e he).eqSymm (entry_at t z R B r M e he).eqSymm (.eqRefl _) (.eqRefl _)
    (coefficient_gap q t z R B r e hz)

theorem late_entry_gap (p q t z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (stored q z R B r M e) (stored t z R B r M e) two (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (clock_denominator_positive q t) (unit_positive p)
    (le_congr (by unfold clockNumerator; ipra_ring) (by unfold clockDenominator; ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit t) hq) (mul_le_mul_right (unit q) ht)))
    (entry_gap q t z R B r M e hz he)

theorem late_mass_gap (p q t z R B r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (difference q t z R B r r M)) (massError p M) := by
  refine RationalArgmin.transitive
    (difference_uniform_of_degree_bounds (buffer q z R B r M) (buffer t z R B r M)
      (previous M) two (unit p) (unit_positive p) ?_) ?_
  · intro sh Δ e he
    have h' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.wk
    have shift_clock {w : PTm n} (h : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit w)) :
        Δ ⊢[PRAAx] le (prefactorGain (sh R)*unit (sh p)) (unit (sh w)) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,prefactorGain,linearGain,halfGain,negativeHalf,one,two] using h.shift.wk
    simpa only [Δ,sh,Syn.shift,stored,GaussianBarnesCanonicalExponentTaylorBuffer.subst_buffer,
      GaussianBarnesCanonicalHigherRows.subst_previous,GaussianCoefficientNameBounds.subst_unit,two,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      late_entry_gap (sh p) (sh q) (sh t) (sh z) (sh R) (sh B) (sh r) (sh M) e
        h' he (shift_clock hq) (shift_clock ht)
  · exact fraction_order _ _ _ _ (unit_positive p) (unit_positive p)
      (le_of_eq_add (d := num 4*succ (previous M)*unit p) (by ipra_ring))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorFixedCutoff
