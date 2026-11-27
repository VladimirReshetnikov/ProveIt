import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialInverseSamples
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.Squared.GaussianSineSquaredResidual

/-!
# Numerical readback of the original named multiple-angle sine

The original sine samples at a bounded natural multiple are close to
the exact zero-safe recurrence on an inverse rational pair. No division
by the original sine or by a difference of exponentials is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace LeanProofs.IPRA.Analysis.GaussianNamedSineMultipleAngleSamples

open_ipra
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianBoundedIntegerExponentialSample (stage_input)
open GaussianBoundedIntegerExponentialStages (scaledF stageData radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialInverse (negative_input)
open GaussianExponentialInverseSamples (positive negative exact_pair positive_canonical negative_canonical
  positive_sample negative_sample baseNegativeRadius positive_power negative_power positiveRadius negativeRadius)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameRingLaws (negativeF negativeData multiply_sample_error)
open GaussianNamedSineFromExponential (sineF sineData differenceF differenceData multiplier)
open GaussianRadiusExponentialName (input nameF data name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (canonical qadd qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (qone power)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianSineMultipleAngleRecurrence (value power_difference)
open GaussianSineSquaredTrace (sineValue)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def readbackRadius (f : PR 2) (R x H K : PTm n) : PTm n :=
  (multiplyModulus constantF (differenceF f) multiplier (differenceData R x)+one)+(num 6+(H+K))

ipra_subst readbackRadius [one]

theorem multiplier_unit_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_succ_self one) (le_refl one)
    (le_congr (one_mul one).eqSymm (one_mul two).eqSymm (le_succ_self one))
    GaussianSineSquaredResidual.multiplier_bound

theorem readback (f : PR 2) (p R x A B H K : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (ha : Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data R x)) A H (unit p))
    (hb : Γ ⊢[PRAAx] distanceBounded (ap2 (nameF (negativeF f)) p (data R (negativeData x))) B K (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF f) p (sineData f R x)) (sineValue A B) (readbackRadius f R x H K) (unit p) := by
  let e := nameF f
  let g := nameF (negativeF f)
  let X := data R x
  let Y := data R (negativeData x)
  let D := differenceData R x
  let v := ap2 (differenceF f) p D
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have he := name_regular f R x h
  have hg := name_regular (negativeF f) R (negativeData x) (negative_input f R x h)
  have first := multiply_sample_error constantF (differenceF f) multiplier D p (constant_regular multiplier)
    (GaussianNamedDifference.name_regular e g X Y he hg)
  have left := distance_congr (.eqRefl _) (qmul_congr (constant_at p multiplier) (.eqRefl v))
    (.eqRefl _) (.eqRefl _) first
  have inner := distance_triangle_same _ _ _ _ _ _ hu (GaussianNamedDifference.sample_error e g X Y p he hg)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hu ha hb)
  have right := distance_congr (.eqRefl _) (.eqRefl _) (one_mul (num 6+(H+K))) (.eqRefl _)
    (multiply_distance multiplier v (qsub A B) one (num 6+(H+K)) u hu multiplier_unit_bound inner)
  exact distance_triangle_same _ _ _ _ _ _ hu left right

theorem raw_multiple_angle (A B k : PTm n) (ha : Γ ⊢[PRAAx] canonical A) (hb : Γ ⊢[PRAAx] canonical B)
    (h : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qmul (sineValue A B) (value (qadd A B) k) ≐ sineValue (power A (succ k)) (power B (succ k)) :=
  (qmul_associative multiplier (qsub A B) (value (qadd A B) k)).eqTrans
    (qmul_congr (.eqRefl _) (power_difference A B k ha hb h))

def baseRadius (f : PR 2) (R x : PTm n) : PTm n := readbackRadius f R x two (baseNegativeRadius f R x)
def scaledRadius (f : PR 2) (E k R x : PTm n) : PTm n :=
  readbackRadius (scaledF f) (radius E R) (stageData E (succ k) x)
    (positiveRadius E (succ k) R) (negativeRadius f E (succ k) R x)

ipra_subst baseRadius [two, one]
ipra_subst scaledRadius

theorem base_sample (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF f) p (sineData f R x))
      (sineValue (positive f p R x) (negative f p R x)) (baseRadius f R x) (unit p) :=
  readback f p R x _ _ _ _ h (positive_sample f p R x h) (negative_sample f p R x h)

theorem scaled_sample (f : PR 2) (p E k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hi : Γ ⊢[PRAAx] le (succ k) E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF (scaledF f)) p (sineData (scaledF f) (radius E R) (stageData E (succ k) x)))
      (qmul (sineValue (positive f p R x) (negative f p R x))
        (value (qadd (positive f p R x) (negative f p R x)) k)) (scaledRadius f E k R x) (unit p) := by
  let i := succ k
  let A := positive f p R x
  let B := negative f p R x
  have hE := le_trans (zero_lt_succ k) hi
  have e := raw_multiple_angle A B k (positive_canonical f p R x) (negative_canonical f p R x) (exact_pair f p R x h)
  exact distance_congr (.eqRefl _) e.eqSymm (.eqRefl _) (.eqRefl _)
    (readback (scaledF f) p (radius E R) (stageData E i x) (power A i) (power B i)
      (positiveRadius E i R) (negativeRadius f E i R x) (stage_input f E i R x h hi)
      (positive_power f p E i R x h hi hE) (negative_power f p E i R x h hi hE))

end LeanProofs.IPRA.Analysis.GaussianNamedSineMultipleAngleSamples
