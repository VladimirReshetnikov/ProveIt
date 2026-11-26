import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumChord
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScaleOrder
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingGlobalBounds

/-!
# Difference readback of the strong Gamma chord

The weighted inequality is evaluated at the actual independent-clock
log-Gamma name. At a common output query its normalization errors are
bounded explicitly. Subtracting the full base weight gives the scaled
center difference plus the squared-separation margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaMinimumChord (centerData center_source lowerData margin scaledF strong_chord weightedData)
open GaussianNameRingLaws (add_sample_error sum_left_error sum_right_error three)
open GaussianNamedNaturalScaleOrder (common_upper cost sample_error)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNaturalScaleProductName (productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical qadd)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalNaturalScale (natScale natScale_add natScale_as_product natScale_congr natScale_one_canonical)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qsub_add_cancel)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGlobalBounds (small_join)
open GaussianStirlingTailComparison (point_add_upper_same point_order_refl)
open RationalValueBounds (upper upper_congr upper_of_order upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => logGammaF
local notation "lg" => logGammaData

def budget (a c b W : PTm n) : PTm n :=
  cost G W (centerData a c b W)+cost G (pred W) (lg a b)+num 8

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a c b W : PTm n) :
    Syn.subst σ (budget a c b W) = budget (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ W) := by
  simp [budget]

theorem log_sample_canonical (p a b : PTm n) : Γ ⊢[PRAAx] canonical (ap2 G p (lg a b)) := by
  unfold logGammaF logGammaData
  apply GaussianRationalHorner.canonical_congr (GaussianNamedPositiveLogarithm.sample_at _ _ _ _)
  exact GaussianPositiveRationalLogarithm.sample_canonical _ _ _

private theorem scale_subtract (W x y : PTm n) :
    Γ ⊢[PRAAx] qsub (natScale W x) (natScale W y) ≐ natScale W (qsub x y) :=
  (qsub_congr (natScale_as_product W x) (natScale_as_product W y)).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqTrans (natScale_as_product W _).eqSymm)

private theorem cancel_scaled_base (W x y : PTm n) (hx : Γ ⊢[PRAAx] canonical x)
    (hy : Γ ⊢[PRAAx] canonical y) (hW : Γ ⊢[PRAAx] le two W) : Γ ⊢[PRAAx]
    qsub (qadd (natScale (pred W) x) y) (natScale W x) ≐ qsub y x := by
  let X := natScale (pred W) x
  have ep := natEq (AnalyticNumberTheory.BinomialThree.pos_of_one_le (le_trans RationalAlgebra.two_positive hW))
  have ew : Γ ⊢[PRAAx] W ≐ pred W+one := by
    apply deriveNat
    ipra_simps
    linear_combination ep
  have split := (natScale_congr ew (.eqRefl x)).eqTrans
    ((natScale_add (pred W) one x).eqTrans (qadd_congr (.eqRefl X) (natScale_one_canonical x hx)))
  exact (qsub_congr (qadd_commutative X y) split).eqTrans
    ((subtract_sum (qadd y X) X x).eqSymm.eqTrans (qsub_congr (qsub_add_cancel y X hy) (.eqRefl x)))

private theorem translate_chord (a c b M W X Y Z A P : PTm n)
    (hW : Γ ⊢[PRAAx] le two W) (hP : Γ ⊢[PRAAx] le one P)
    (hx : Γ ⊢[PRAAx] canonical X) (hy : Γ ⊢[PRAAx] canonical Y)
    (h : Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b M) (natScale W Z)))
      (fstT (qadd (natScale (pred W) X) Y)) A P) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b M) (natScale W (qsub Z X)))) (fstT (qsub Y X)) A P := by
  let g := margin a c b M
  let v := natScale W X
  have sub : Γ ⊢[PRAAx] upper (fstT (qnegative v)) (fstT (qnegative v)) zero P :=
    upper_of_order _ _ _ _ (point_order_refl _)
  have together := point_add_upper_same _ _ _ _ _ _ _ hP h sub
  have left : Γ ⊢[PRAAx] qsub (qadd g (natScale W Z)) v ≐ qadd g (natScale W (qsub Z X)) :=
    (qadd_associative g (natScale W Z) (qnegative v)).eqTrans (qadd_congr (.eqRefl _) (scale_subtract W Z X))
  exact upper_congr (congrFst left) (congrFst (cancel_scaled_base W X Y hx hy hW))
    (LeanProofs.IPRA.add_zero A) (.eqRefl _) together

/-- The actual finite observation of the chord compares the signed
difference to the base at the same query. Its cost is fixed before
choosing that query. -/
theorem difference_at (p a c b M W : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b)) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] upper
      (fstT (qadd (margin a c b M) (natScale W (qsub (ap2 G p (centerData a c b W)) (ap2 G p (lg a b))))))
      (fstT (qsub (ap2 G p (lg c b)) (ap2 G p (lg a b)))) (budget a c b W) (unit p) := by
  let m := margin a c b M
  let x := lg a b
  let y := lg c b
  let z := centerData a c b W
  let P := unit p
  let leftRaw := qadd m (natScale W (ap2 G p z))
  let rightRaw := qadd (natScale (pred W) (ap2 G p x)) (ap2 G p y)
  let left := ap2 (GaussianNameArithmetic.addF C scaledF) p (lowerData a c b M W)
  let right := ap2 (GaussianNameArithmetic.addF scaledF G) p (weightedData a c b W)
  have hP := unit_positive (Γ := Γ) p
  have hx := log_gamma_regular a b (.andI ha hb)
  have hy := log_gamma_regular c b (.andI hc hb)
  have hz := log_gamma_regular _ _ (center_source a c b W hc hb hW)
  have leftAdd : Γ ⊢[PRAAx] distanceBounded left (qadd m (ap2 scaledF p (productData G W z))) three P :=
    distance_congr (.eqRefl _) (qadd_congr (constant_at p m) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
      (add_sample_error C scaledF m (productData G W z) p (constant_regular m) (GaussianNamedNaturalScaleOrder.regular G W z hz))
  have rightAdd : Γ ⊢[PRAAx] distanceBounded right (qadd (ap2 scaledF p (productData G (pred W) x)) (ap2 G p y)) three P :=
    add_sample_error scaledF G (productData G (pred W) x) y p (GaussianNamedNaturalScaleOrder.regular G (pred W) x hx) hy
  have leftErr : Γ ⊢[PRAAx] distanceBounded left leftRaw (three+cost G W z) P :=
    distance_triangle_same _ _ _ _ _ _ hP leftAdd (sum_right_error m _ _ _ _ hP (sample_error G W z p hz))
  have rightErr : Γ ⊢[PRAAx] distanceBounded right rightRaw (three+cost G (pred W) x) P :=
    distance_triangle_same _ _ _ _ _ _ hP rightAdd (sum_left_error _ _ _ _ _ hP (sample_error G (pred W) x p hx))
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP (distance_symmetric _ _ _ _ hP leftErr))
  have after := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP rightErr)
  have middle := common_upper _ _ _ _ p (strong_chord a c b M W ha hc hb haM hcM hW)
  have together : Γ ⊢[PRAAx] upper (fstT leftRaw) (fstT rightRaw) (budget a c b W) P :=
    upper_congr (.eqRefl _) (.eqRefl _) (by unfold budget three; ipra_ring) (.eqRefl _)
      (small_join _ _ _ _ _ p (small_join _ _ _ _ _ p before middle) after)
  exact translate_chord _ _ _ _ _ _ _ _ _ _ hW hP (log_sample_canonical p a b) (log_sample_canonical p c b) together

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordReadback
