import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBoseDenominator
import IPRADerivations.Analysis.Exponential.GaussianExponentialLinearRemainder

/-!
# The exact linear readback of the original Bose denominator

Each finite exponential observation is compared to its own original
Pi observation. The quadratic error therefore carries two factors of
the time width without any absolute observation error to divide by
that width.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLinearApproximation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseDenominator (nameF data sampleClock)
open GaussianBinetBoseExponential (expF expRadius expData piClock scaleF scaleData scale_readback scale_positive)
open GaussianBinetKernelPi (sample sample_fraction sample_margins sample_distance denominator_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_congr radius_bounded radius_multiply radiusNumerator radius_represents radius_numerator_norm)
open GaussianStirlingConstant (piNumerator piDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qone qadd_sub_cancel qmul_congr qsub_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def coefficient (k : PTm n) : PTm n := radiusPoint (two*piNumerator k) (piDenominator k)
def queryClock (p A : PTm n) : PTm n := GaussianRadiusExponentialName.inputPrecision (expRadius A) (sampleClock p)
def coefficientClock (p A : PTm n) : PTm n := piClock (queryClock p A) A
def query (p A B : PTm n) : PTm n := ap2 scaleF (queryClock p A) (scaleData false A B)

theorem coefficient_clock_later (p A : PTm n) : Γ ⊢[PRAAx] le p (coefficientClock p A) := by
  have first : Γ ⊢[PRAAx] le p (sampleClock p) := le_add_right _ _
  have middle : Γ ⊢[PRAAx] le (sampleClock p) (queryClock p A) :=
    GaussianRadiusExponentialLipschitzRate.original_clock_later _ _
  have last : Γ ⊢[PRAAx] le (queryClock p A) (coefficientClock p A) := le_add_right _ _
  exact le_trans first (le_trans middle last)

theorem fraction_lower (a b A B : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le one B)
    (hle : Γ ⊢[PRAAx] le (A*b) (B*a)) : Γ ⊢[PRAAx] lower (radiusPoint a b) A B := by
  apply lower_from_representation _ (radiusNumerator a) b A B hb hB (radius_represents a b hb)
  exact le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] (B*a)*(B*a) ≐ B*B*(a*a)).eqTrans
    (congrMul (.eqRefl _) (radius_numerator_norm a).eqSymm)) (sq_le_sq hle)

theorem coefficient_lower (k : PTm n) : Γ ⊢[PRAAx] lower (coefficient k) one one := by
  apply fraction_lower _ _ one one (denominator_positive k) (le_refl one)
  ipra_le 2*sl (sample_margins (Γ := Γ) k).andE₁+3*𝔞(piDenominator k)

theorem coefficient_bound (k : PTm n) : Γ ⊢[PRAAx] bounded (coefficient k) (num 10) one := by
  let a := two*piNumerator k
  let b := piDenominator k
  have hb := denominator_positive (Γ := Γ) k
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hb (le_refl one) ?_ (radius_bounded a b hb)
  dsimp only [a,b]
  ipra_le 2*sl (sample_margins (Γ := Γ) k).andE₂

theorem coefficient_readback (k : PTm n) :
    Γ ⊢[PRAAx] coefficient k ≐ qmul (fraction two one) (sample k) := by
  let a := piNumerator k
  let b := piDenominator k
  have hb := denominator_positive (Γ := Γ) k
  have first := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) two one (le_refl (one : PTm n))
  have second := (sample_fraction (Γ := Γ) k).eqTrans
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb)
  exact ((qmul_congr first second).eqTrans
    ((radius_multiply two one a b (le_refl one) hb).eqTrans (radius_congr (.eqRefl _) (one_mul b)))).eqSymm

theorem coefficient_distance (p q : PTm n) : Γ ⊢[PRAAx] distanceBounded (coefficient p) (coefficient q)
    (two*(GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q))
    (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) := by
  have h := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) two one (le_refl one)).eqSymm
    (.eqRefl _) (.eqRefl _) (radius_bounded two one (le_refl one))
  exact distance_congr (coefficient_readback p).eqSymm (coefficient_readback q).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance _ _ _ _ _ _
      (positive_product _ _ (GaussianCoefficientNameBounds.unit_positive p) (GaussianCoefficientNameBounds.unit_positive q))
      h (sample_distance p q))

theorem scale_factor (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ap2 scaleF p (scaleData false A B) ≐ qmul (fraction A B) (coefficient (piClock p A)) := by
  let k := piClock p A
  have hb := denominator_positive (Γ := Γ) k
  have prod := (qmul_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB) (.eqRefl (coefficient k))).eqTrans
    (radius_multiply A B (two*piNumerator k) (piDenominator k) hB hb)
  exact (scale_readback p A B hB).eqTrans
    ((radius_congr (by ipra_ring) (.eqRefl (B*piDenominator k))).eqTrans prod.eqSymm)

theorem unit_scale (p : PTm n) :
    Γ ⊢[PRAAx] ap2 scaleF p (scaleData false one one) ≐ coefficient (piClock p one) := by
  let k := piClock p (one : PTm n)
  exact (scale_factor p one one (le_refl one)).eqTrans
    ((qmul_congr GaussianGammaFactorialValues.natural_one (.eqRefl (coefficient k))).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone (coefficient k)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right (coefficient k)
          (GaussianRationalHorner.ofGaussian_canonical _ _ (denominator_positive k)))))

theorem query_factor (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] query p A B ≐ qmul (fraction A B) (coefficient (coefficientClock p A)) :=
  scale_factor (queryClock p A) A B hB

theorem query_lower (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (query p A B) A B := by
  have ht := lower_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB).eqSymm
    (.eqRefl _) (.eqRefl _) (fraction_lower A B A B hB hB (le_congr (.eqRefl _) (mul_comm _ _) (le_refl (A*B))))
  have h := GaussianRationalLowerBounds.product_lower _ _ _ _ _ _ hB (le_refl one) ht
    (coefficient_lower (coefficientClock p A))
  exact lower_congr (query_factor p A B hB).eqSymm (by ipra_ring) (by ipra_ring) h

theorem denominator_error (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (small : Γ ⊢[PRAAx] le (num 10*A) B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B)) (query p A B) (num 100*(A*A)) (B*B) := by
  let Q := query p A B
  let R := expRadius A
  let r := sampleClock p
  let L := GaussianRadiusExponentialName.index R r
  let E := GaussianRationalPolynomialExponential.scalarSum Q L
  have t := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB).eqSymm
    (.eqRefl _) (.eqRefl _) (radius_bounded A B hB)
  have qB : Γ ⊢[PRAAx] bounded Q (num 10*A) B :=
    bound_congr (query_factor p A B hB).eqSymm (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ hB (le_refl one) t (coefficient_bound (coefficientClock p A)))
  have can := (scale_positive (queryClock p A) A B hB).andE₂
  have cutoff := GaussianPositiveExponentialSeparation.original_cutoff_positive (Γ := Γ) R r
  have error := GaussianExponentialLinearRemainder.original_finite_linear_remainder Q (num 10*A) B L hB small qB can cutoff
  have shift := GaussianNameRingLaws.sum_left_error E (GaussianRationalHorner.qadd qone Q) (qnegative qone)
    ((num 10*A)*(num 10*A)) (B*B) (positive_product _ _ hB hB) error
  have read := (GaussianBinetBoseDenominator.sample_at (Γ := Γ) p A B).eqTrans
    (qsub_congr (GaussianRadiusExponentialName.sample_at scaleF R r (scaleData false A B)) (.eqRefl _))
  exact distance_congr read.eqSymm (qadd_sub_cancel qone Q can) (by ipra_ring) (.eqRefl _) shift

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLinearApproximation
