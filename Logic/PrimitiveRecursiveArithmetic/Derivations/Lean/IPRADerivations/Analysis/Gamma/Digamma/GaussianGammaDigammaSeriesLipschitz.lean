import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaReciprocalLipschitz
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaSeries
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanelReadback

/-!
# The exact finite digamma series inherits the reciprocal slope

The harmonic term and the Euler-constant observation are common to both
endpoints. Their exact cancellation leaves the literal finite reciprocal
difference. Normalized finite-name observations add only dyadic error.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaSeriesLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaSeries (nameF data partialValue)
open GaussianGammaDigammaReciprocalLipschitz (difference cap finite_upper)
open GaussianGammaDigammaFiniteSum (reciprocalSum)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingTailComparison (point_order_refl point_add_order)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRationalMetric (qsub qsub_canonical distanceBounded)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianStirlingAllOrderFirstPanelReadback (upper_of_add_order)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open RationalValueBounds (upper upper_mono upper_triangle)
open RationalArgmin (rationalLE_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (a c b : PTm n) : PTm n := (a+b)*monus c a
def denominator (a : PTm n) : PTm n := a*a
def rawValue (g a b N : PTm n) : PTm n := qadd g (partialValue a b N)

theorem partial_rejoin (a c b N : PTm n) :
    Γ ⊢[PRAAx] qadd (partialValue a b N) (difference a c b N) ≐ partialValue c b N := by
  let A := reciprocalSum a b N
  let C := reciprocalSum c b N
  let D := difference a c b N
  let H := harmonicPoint N
  have e : Γ ⊢[PRAAx] qadd C D ≐ A :=
    GaussianRationalLinearProduct.add_sub_right _ _ (GaussianRationalFiniteSum.sum_canonical _ _ _)
  have s : Γ ⊢[PRAAx] qsub (partialValue c b N) D ≐ partialValue a b N :=
    (GaussianRationalInverseQuadraticAlgebra.subtract_sum H C D).eqTrans (qsub_congr (.eqRefl _) e)
  exact (qadd_congr s.eqSymm (.eqRefl _)).eqTrans
    ((qadd_commutative _ _).eqTrans (GaussianRationalLinearProduct.add_sub_right _ _ (qsub_canonical _ _)))

theorem raw_rejoin (g a c b N : PTm n) :
    Γ ⊢[PRAAx] qadd (rawValue g a b N) (difference a c b N) ≐ rawValue g c b N :=
  (qadd_associative _ _ _).eqTrans (qadd_congr (.eqRefl _) (partial_rejoin a c b N))

theorem raw_upper (g a c b N : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    upper (fstT (rawValue g c b (succ N))) (fstT (rawValue g a b (succ N)))
      (numerator a c b) (denominator a) := by
  let u := rawValue g a b (succ N)
  let v := rawValue g c b (succ N)
  let R := numerator a c b
  let D := denominator a
  let P := cap a c b
  have hp := positive_product _ _ ha ha
  have h := point_add_order u u _ P (point_order_refl _) (finite_upper a c b N ha hac)
  have e : Γ ⊢[PRAAx] fstT (qadd u P) ≐ RationalArithmetic.add (fstT u) (GaussianEuclideanDistanceName.fraction R D) :=
    (RationalGaussianRealPart.real_add u P).eqTrans
      (RationalAlgebra.add_congr (.eqRefl _) (fraction_real_part R D hp))
  exact upper_of_add_order _ _ _ _ hp (rationalLE_congr (congrFst (raw_rejoin g a c b (succ N))) e h)

theorem raw_sample_error (p a b N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data a b N)) (rawValue (ap2 negativeGammaF p negativeGammaData) a b N)
      GaussianNameRingLaws.three (unit p) :=
  GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.add_sample_error negativeGammaF constantF negativeGammaData (partialValue a b N) p
      negativeGamma_regular (constant_regular _))

theorem finite_name_upper (p a c b N : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    upper (fstT (ap2 nameF p (data c b (succ N)))) (fstT (ap2 nameF p (data a b (succ N))))
      (numerator a c b*unit p+num 6*denominator a) (denominator a*unit p) := by
  let u := unit p
  let D := denominator a
  let g := ap2 negativeGammaF p (negativeGammaData : PTm n)
  have hu := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ ha ha
  have l := scalar_upper _ _ _ _ hu (raw_sample_error p c b (succ N))
  have h := raw_upper g a c b N ha hac
  have r := scalar_upper _ _ _ _ hu (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hu (raw_sample_error p a b (succ N)))
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l h) r
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hu hd) hu) joined
    (by unfold GaussianNameRingLaws.three; ipra_le 0)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaSeriesLipschitz
