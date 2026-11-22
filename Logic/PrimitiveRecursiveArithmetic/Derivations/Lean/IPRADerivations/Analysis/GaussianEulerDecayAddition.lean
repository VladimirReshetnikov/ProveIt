import IPRADerivations.Analysis.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.GaussianExponentialLinearRemainder

/-!
# The original Euler decay under rational increments

The decay factors at two independently encoded rational times multiply
to the original decay name at their sum. At a time step at most one,
the actual decay approximations also admit a linear estimate with
quadratic remainder and explicit observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayAddition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_at add_fast multiplyF multiplyData recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical canonical_unique ofGaussian_represents positive_product qadd qadd_canonical
  represents represents_congr represents_rescale)
open GaussianRationalSyntheticDivision (qadd_congr qone)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qnegative_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRootAlgebra (equal_of_values re_add im_add re_neg im_neg re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem decay_point_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (decayPoint a b) (ComplexLogarithmRemainder.neg (scale a oneCode)) b :=
  qnegative_represents _ _ _ (ofGaussian_represents _ _ hb)

theorem decay_point_add (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] qadd (decayPoint a b) (decayPoint c d) ≐ decayPoint (a*d+c*b) (b*d) := by
  let x := decayPoint a b
  let y := decayPoint c d
  let A := ComplexLogarithmRemainder.neg (scale a oneCode)
  let C := ComplexLogarithmRemainder.neg (scale c oneCode)
  let Z := ComplexLogarithmRemainder.neg (scale (a*d+c*b) oneCode)
  have hbd := positive_product b d hb hd
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add (scale d A) (scale b C)) Z := by
    apply equal_of_values
    all_goals
      simp only [A, C, Z, re_add, im_add, re_neg, im_neg, re_scale, im_scale, re_one, im_one]
      ipra_simps
      ring
  have hy : Γ ⊢[PRAAx] represents y (scale b C) (b*d) :=
    represents_congr (.eqRefl _) (equal_of_values rfl rfl) (mul_comm d b)
      (represents_rescale y C d b (decay_point_represents c d hd))
  apply canonical_unique _ _ Z (b*d) (qadd_canonical x y) (qnegative_canonical _) hbd
    (hrv := decay_point_represents _ _ hbd)
  exact represents_congr (.eqRefl _) e (.eqRefl _)
    (GaussianRationalHorner.qadd_represents x y (scale d A) (scale b C) (b*d) hbd
      (represents_rescale x A b d (decay_point_represents a b hb)) hy)

private theorem constant_add_at (x y z p : PTm n) (e : Γ ⊢[PRAAx] qadd x y ≐ z)
    (hz : Γ ⊢[PRAAx] canonical z) : Γ ⊢[PRAAx] ap2 (addF constantF constantF) p (addData x y) ≐ ap2 constantF p z :=
  (add_at constantF constantF x y p).eqTrans
    ((recode_congr ((qadd_congr (constant_at _ _) (constant_at _ _)).eqTrans e)).eqTrans
      ((GaussianExponentialReference.recode_fixed z hz).eqTrans (constant_at _ _).eqSymm))

theorem original_decay_add (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF decayF decayF) decayF
      (multiplyData decayF decayF (decayData a b) (decayData c d)) (decayData (a*d+c*b) (b*d)) := by
  let x := decayPoint a b
  let y := decayPoint c d
  let z := decayPoint (a*d+c*b) (b*d)
  apply GaussianGammaFoldedApproximantBalance.exponential_product_equivalent constantF constantF constantF
      _ _ _ x y z (exponential_input _ _ (constant_regular x)) (exponential_input _ _ (constant_regular y))
      (exponential_input _ _ (constant_regular z))
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
      (add_fast constantF constantF x y (constant_regular x) (constant_regular y)) (constant_regular z)
  refine .allI ?_
  have hb' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hb.shift
  have hd' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift d) := by simpa [Fm.shift, Syn.shift] using hd.shift
  simpa only [x, y, z, GaussianNameConjugation.pointwiseEqual, Syn.shift, GaussianNameArithmetic.subst_addData,
    GaussianEulerIntegrandName.subst_decayPoint, PTm.subst_mul, PTm.subst_add] using
      constant_add_at _ _ _ (var 0) (decay_point_add (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) hb' hd')
        (qnegative_canonical _)

theorem decay_point_bounded (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (decayPoint a b) a b :=
  GaussianRationalReciprocal.bounded_negative (fraction a b) a b hb
    (GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded a b hb))

theorem original_decay_linear_remainder (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 decayF p (decayData a b)) (qadd qone (decayPoint a b))
      (a*a*unit p+two*(b*b)) (b*b*unit p) := by
  let x := decayPoint a b
  let R := GaussianNameBounds.U constantF x
  let u := ap2 decayF p (decayData a b)
  let v := GaussianRadiusExponentialName.sample constantF one p x
  let w := qadd qone x
  let B := b*b
  have hx := decay_point_bounded a b hb
  have hB := positive_product b b hb hb
  have hBound : Γ ⊢[PRAAx] bounded x one one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hb (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) hab) hx
  have hI : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF one x := by
    refine .andI (constant_regular x) (.allI ?_)
    have hrs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) one one := by
      simpa only [Fm.shift, Syn.shift, GaussianRationalMetric.subst_bounded, PTm.subst_succ, PTm.subst_zero] using hBound.shift
    simpa only [GaussianRadiusExponentialName.boundedSamples, Syn.shift, PTm.subst_succ, PTm.subst_zero] using
      GaussianRationalReciprocal.bound_congr (constant_at (var 0) (Syn.shift x)).eqSymm (.eqRefl one) (.eqRefl one) hrs
  have cr := GaussianExponentialRadiusIndependence.same_input_cross constantF R one x
    (exponential_input constantF x (constant_regular x)) hI
  have d : Γ ⊢[PRAAx] distanceBounded u v two (unit p) := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ cr)
  have tail := GaussianExponentialLinearRemainder.original_constant_exponential_linear_remainder
    x a b p hb hab hx (qnegative_canonical _)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [B]; ipra_ring) (by dsimp only [B]; ipra_ring)
    (GaussianReconstructionRoots.distance_triangle u v w two (unit p) (a*a) B (unit_positive p) hB d tail)

theorem original_Euler_decay_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 3) ⟶ crossEquivalent (multiplyF decayF decayF) decayF
      (multiplyData decayF decayF (decayData (var 0) (var 1)) (decayData (var 2) (var 3)))
      (decayData (var 0*var 3+var 2*var 1) (var 1*var 3))) :=
  closeUniv 4 (.impI (.impI (original_decay_add _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_Euler_decay_linear_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶
      distanceBounded (ap2 decayF (var 2) (decayData (var 0) (var 1))) (qadd qone (decayPoint (var 0) (var 1)))
        (var 0*var 0*unit (var 2)+two*(var 1*var 1)) (var 1*var 1*unit (var 2))) :=
  closeUniv 3 (.impI (.impI (original_decay_linear_remainder _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayAddition
