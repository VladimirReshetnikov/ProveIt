import IPRADerivations.Analysis.Euler.HarmonicLogarithms.QuadraticBounds.GaussianHarmonicIntervalLinearRemainder
import IPRADerivations.Analysis.Euler.CompactExhaustion.ParameterBounds.GaussianEulerExponentCompactBounds

/-!
# First-order increments of the original positive rational logarithm

At positive time `a/b` and a nonnegative step `c/b`, the original
logarithm increment differs from `c/a` by at most `c^2/a^2` and
the two independent requested observation errors. On a single auxiliary
mesh the common denominator logarithm cancels exactly. The rectangle
remainder and one finite integer-gap query remove the auxiliary errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmIncrement

open_ipra
open GaussianPositiveRationalLogarithm (sample source fraction logF data name_regular)
open GaussianPositiveRationalLogarithmProperness (original_finite_difference sample_interval_error)
open RationalGaussianEmbedding (embed)
open RationalHarmonicInterval (interval)
open GammaEulerConstantName (mesh mesh_positive)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr qadd_sub_cancel)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def increment (p q a b c : PTm n) : PTm n := qsub (sample p (a+c) b) (sample q a b)
def errorNumerator (p q a c : PTm n) : PTm n := (c*c)*(unit p*unit q)+(unit p+unit q)*(a*a)
def errorDenominator (p q a : PTm n) : PTm n := (a*a)*(unit p*unit q)

theorem finite_difference (a b c Q : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub (embed (interval (a+c) b Q)) (embed (interval a b Q)) ≐
      embed (interval (a+c) a Q) := by
  let X := embed (GammaMeshRobinLogBridge.harmonicLog (a+c) Q)
  let Y := embed (GammaMeshRobinLogBridge.harmonicLog a Q)
  let Z := embed (GammaMeshRobinLogBridge.harmonicLog b Q)
  have hac : Γ ⊢[PRAAx] le one (a+c) := le_trans ha (le_add_right a c)
  have hx : Γ ⊢[PRAAx] qsub X Z ≐ embed (interval (a+c) b Q) :=
    original_finite_difference (a+c) b Q hac hb
  have hy : Γ ⊢[PRAAx] qsub Y Z ≐ embed (interval a b Q) :=
    original_finite_difference a b Q ha hb
  have diff : Γ ⊢[PRAAx] qsub X Y ≐ embed (interval (a+c) a Q) :=
    original_finite_difference (a+c) a Q hac ha
  have cancel : Γ ⊢[PRAAx] qsub (qsub X Z) (qsub Y Z) ≐ qsub X Y :=
    (qsub_congr (GaussianReconstructionRoots.difference_chain X Y Z).eqSymm (.eqRefl _)).eqTrans
      ((qsub_congr (GaussianRationalLinearProduct.qadd_commutative _ _) (.eqRefl _)).eqTrans
        (qadd_sub_cancel _ _ (GaussianRationalMetric.qsub_canonical X Y)))
  exact (qsub_congr hx.eqSymm hy.eqSymm).eqTrans (cancel.eqTrans diff)

private theorem interval_observation (p t a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (sample p a b) (embed (interval a b (mesh t)))
      (unit t+num 9*unit p) (unit p*unit t) := by
  let P := unit p
  let U := unit t
  let D := P*U
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hu : Γ ⊢[PRAAx] le one U := unit_positive t
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ hp hu
  have approximate := distance_radius_mono _ _ _ _ (num 8*P) D hu hd
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) (sample_interval_error t a b h)
  have regular : Γ ⊢[PRAAx] distanceBounded (sample p a b) (sample t a b) (P+U) D :=
    GaussianNameEquivalence.point_at logF (data a b) p t (name_regular a b h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd regular approximate)

theorem increment_interval_error (p q t a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (increment p q a b c) (embed (interval (a+c) a (mesh t)))
      ((unit p+unit q)*unit t+num 18*(unit p*unit q)) ((unit p*unit q)*unit t) := by
  let P := unit p
  let Q := unit q
  let U := unit t
  let D := (P*Q)*U
  let X := sample p (a+c) b
  let Y := sample q a b
  let L := embed (interval (a+c) b (mesh t))
  let M := embed (interval a b (mesh t))
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hu : Γ ⊢[PRAAx] le one U := unit_positive t
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hp hq) hu
  have plus : Γ ⊢[PRAAx] distanceBounded X L ((U+num 9*P)*Q) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hu) hd
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (interval_observation p t (a+c) b (.andI (le_trans ha (le_add_right a c)) hb))
  have minus : Γ ⊢[PRAAx] distanceBounded (qnegative Y) (qnegative M) ((U+num 9*Q)*P) D := by
    apply GaussianEulerExponentCompactBounds.negative_distance _ _ _ _ hd
    exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hq hu) hd
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) (interval_observation q t a b (.andI ha hb))
  have both := GaussianNameArithmetic.sum_distance X L (qnegative Y) (qnegative M) _ _ D hd plus minus
  exact distance_congr (.eqRefl _) (finite_difference a b c (mesh t) ha hb) (by ipra_ring) (.eqRefl _) both

theorem increment_slack (p q t a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack (qsub (increment p q a b c) (fraction c a))
      (errorNumerator p q a c) (errorDenominator p q a) (num 18) t := by
  let D := (unit p*unit q)*unit t
  have hd : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)
  have haa := positive_product a a ha ha
  have rem := distance_symmetric _ _ _ _ haa
    (GaussianHarmonicIntervalLinearRemainder.interval_remainder a c (mesh t) ha (mesh_positive t))
  have near := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hd haa
    (increment_interval_error p q t a b c ha hb) rem
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [D,errorNumerator,errorDenominator,unit]; ipra_ring)
    (by dsimp only [D,errorDenominator,unit]; ipra_ring) near

theorem original_increment (p q a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (increment p q a b c) (fraction c a)
      (errorNumerator p q a c) (errorDenominator p q a) := by
  let t := GaussianRationalSlackRemoval.precision (qsub (increment p q a b c) (fraction c a))
    (errorNumerator p q a c) (errorDenominator p q a) (num 18)
  exact GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 18)
    (positive_product _ _ (positive_product _ _ ha ha) (positive_product _ _ (unit_positive p) (unit_positive q)))
    (increment_slack p q t a b c ha hb)

theorem original_positive_rational_logarithm_first_order_remainder_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 2) ⋏ le one (var 3)) ⟶
        distanceBounded (increment (var 0) (var 1) (var 2) (var 3) (var 4)) (fraction (var 4) (var 2))
          (errorNumerator (var 0) (var 1) (var 2) (var 4)) (errorDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (original_increment _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmIncrement
