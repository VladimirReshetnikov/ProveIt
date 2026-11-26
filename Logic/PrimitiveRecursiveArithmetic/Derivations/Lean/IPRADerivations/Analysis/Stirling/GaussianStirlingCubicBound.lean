import IPRADerivations.Analysis.Stirling.GaussianStirlingCubicFinite
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrement
import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNativeStrictLogConvexity
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# The signed cubic log-Stirling bound on the original rational name

The first-cell margin survives the finite sum and the cofinal limit.
The strict lower comparison is written additively:
1/(12x) < R(x) + 1/(360x³).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingCubicBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianRationalHorner (qadd qzero qadd_canonical ofGaussian_canonical positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open GaussianStirlingCubicCell (cubicValue cubic_den_positive margin marginNumerator marginDenominator
  margin_den_positive margin_num_positive)
open GaussianStirlingCubicFinite (cubicDifference cubic_telescope cubic_diff_den_positive raw_lower)
open GaussianStirlingGammaFractionalIncrement (increment_rate)
open GaussianStirlingGlobalBounds (steps translatedRate rate_at endpoint_close small_join limitRemainderF limitRemainderData
  limit_remainder_regular remainderF remainderData remainder_regular remainder_cross)
open GaussianStirlingNames (source)
open GaussianStirlingMultiplicativeBoundsLog (constant_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingRationalTelescopers (upperValue upperDifference upper_den_positive upper_telescope)
open GaussianStirlingTailComparison (point_add_upper_same point_add_order point_order_refl)
open GaussianStirlingTelescope (shifted shifted_source rawSum)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_of_order upper_of_radius upper_order_right upper_mono)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "A" => GaussianStirlingNames.nameF
local notation "G" => GaussianNamedDifference.nameF A A
local notation "L" => GaussianStirlingTelescopeName.nameF
local notation "LD" => GaussianStirlingTelescopeName.data

def cap (a b : PTm n) : PTm n := qadd (margin a b) (upperValue a b)
def correctedF : PR 2 := addF remainderF constantF
def correctedData (a b x : PTm n) : PTm n := addData (remainderData a b x) (cubicValue a b)
def limitF : PR 2 := addF limitRemainderF constantF
def limitData (a b x : PTm n) : PTm n := addData (limitRemainderData a b x) (cubicValue a b)

theorem cubic_diff_le (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] rationalLE (fstT (cubicDifference N a b)) (fstT (cubicValue a b)) := by
  let c := shifted a b N
  let q := cubicDifference N a b
  have e := (GaussianRationalNonnegativeFractions.fraction_nonnegative (GaussianStirlingCubicCell.cube b) _
    (cubic_den_positive c (shifted_source a b N hs).andE₁)).andE₁
  have z := rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _) e
  exact rationalLE_congr (congrFst (qzero_add q (ofGaussian_canonical _ _ (cubic_diff_den_positive N a b hs))))
    (congrFst (cubic_telescope N a b hs)) (point_add_order qzero (cubicValue c b) q q z (point_order_refl q))

private theorem upper_tail (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (upperValue (shifted a b (steps p)) b)) (fstT qzero) one (unit p) := by
  let c := shifted a b (steps p)
  let B := num 12*c
  let P := unit p
  have hB := upper_den_positive c (shifted_source a b (steps p) hs).andE₁
  have hP := unit_positive (Γ := Γ) p
  have idx := GaussianStirlingIntegerLimit.index_dominates_unit (Γ := Γ) p
  have hstep : Γ ⊢[PRAAx] le P (steps p) := le_trans idx (le_succ_self _)
  have cmp : Γ ⊢[PRAAx] le (b*P) (one*B) := by
    dsimp only [B,c,shifted]
    ipra_le 𝔞 b*sl hstep+12*𝔞 a+11*𝔞 b*𝔞 (steps p)
  have raw := GaussianDominantPairAlgebra.radius_bounded b B hB
  have bound := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point b B hB).eqSymm (.eqRefl _) (.eqRefl _) raw
  have near := bounded_radius_mono (upperValue c b) b B one P hB hP cmp bound
  have z := GaussianRationalReconstruction.qsub_zero_right (upperValue c b) (ofGaussian_canonical _ _ hB)
  exact upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP
    (GaussianRationalReciprocal.bound_congr z.eqSymm (.eqRefl _) (.eqRefl _) near))

private theorem endpoint_observation (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (cap a b))
      (fstT (qadd (ap2 G p (GaussianStirlingTelescopeName.endpointData (steps p) a b)) (cubicValue a b)))
      two (unit p) := by
  let N := GaussianStirlingIntegerLimit.index p
  let K := steps p
  let P := unit p
  let U := upperDifference a b K
  let V := cubicDifference K a b
  let M := margin a b
  let T := upperValue (shifted a b K) b
  let X := GaussianStirlingTelescopeName.endpointData K a b
  let C := cubicValue a b
  let Z := ap2 G p X
  have hP := unit_positive (Γ := Γ) p
  have readback := GaussianStirlingTelescopeName.telescope_cross K a b hs
  have lhs : Γ ⊢[PRAAx] qadd (qadd U M) T ≐ cap a b :=
    (GaussianStirlingGlobalBoundsFinite.swap_suffix U M T).eqTrans
      ((qadd_congr ((qadd_commutative U T).eqTrans (upper_telescope a b K hs.andE₁)) (.eqRefl M)).eqTrans
        (qadd_commutative _ _))
  -- The raw summation rate K/2^p is removed before the cofinal step.
  let I := GaussianNamedRealOrderTransport.precision (fstT (qadd U M)) (fstT (qadd Z C)) P (K+one)
  let R := unit I
  let Y' := ap2 L I (LD K a b)
  let W' := qadd Y' C
  have rP := unit_positive (Γ := Γ) I
  have precise := raw_lower (GaussianFastValueCut.exponent K I) N a b hs
  have mono := mul_le_mul_right K
    (GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right I (GaussianFastValueCut.normalizer K)))
  have flat' : Γ ⊢[PRAAx] upper (fstT (qadd U M)) (fstT (qadd Y' V)) K R :=
    upper_congr (.eqRefl _) (congrFst (qadd_congr (GaussianStirlingTelescopeName.name_at I K a b).eqSymm
      (.eqRefl V))) (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive (GaussianFastValueCut.exponent K I)) precise
        (le_congr (mul_comm _ _) (mul_comm _ _) mono))
  have hi := upper_order_right _ _ _ _ _ flat'
    (point_add_order Y' Y' V C (point_order_refl Y') (cubic_diff_le K a b hs))
  have tailBudget : Γ ⊢[PRAAx] upper (fstT T) (fstT qzero) one P := upper_tail a b p hs
  have hY : Γ ⊢[PRAAx] upper (fstT W') (fstT (qadd Z C)) (P+R) (R*P) := by
    have hDen := positive_product _ _ rP hP
    have r := GaussianNameEquivalence.cross_at L G (LD K a b) X I p readback
    have f := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hDen r)
    exact upper_congr (.eqRefl _) (.eqRefl _) ((add_zero _).eqTrans (add_comm R P)) (.eqRefl _)
      (point_add_upper_same Y' Z C C _ zero _ hDen f (upper_of_order _ _ _ _ (point_order_refl C)))
  have h₁ := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ hi hY
  have h₂ : Γ ⊢[PRAAx] upper (fstT (qadd U M)) (fstT (qadd Z C)) ((K+one)*P+R) (R*P) := by
    apply upper_mono _ _ _ _ _ _ (positive_product _ _ rP (positive_product _ _ rP hP)) h₁
    exact le_of_eq_add (d := zero) (by ipra_ring)
  have h₃ : Γ ⊢[PRAAx] upper (fstT (qadd U M)) (fstT (qadd Z C)) one P := by
    apply GaussianNamedRealOrderTransport.remove_upper_slack _ _ one P (K+one)
    change Γ ⊢[PRAAx] upper _ _ (one*R+(K+one)*P) (P*R)
    exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (mul_comm R P) h₂
  exact upper_congr (congrFst lhs) (congrFst (qadd_zero_right _ (qadd_canonical _ _))) (by ipra_ring) (.eqRefl _)
    (point_add_upper_same _ _ T qzero one one P hP h₃ tailBudget)

private theorem observed (a b x K p : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (GaussianStirlingGlobalBounds.translatedPoint a b p)
      (ap2 GaussianStirlingIntegerLimit.nameF p x) K (unit p)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (cap a b)))
      (fstT (ap2 limitF p (limitData a b x))) (K+num 17) (unit p) := by
  let X := GaussianStirlingTelescopeName.endpointData (steps p) a b
  let Y := limitRemainderData a b x
  let C := cubicValue a b
  let P := unit p
  let q := ap2 G p X
  let r := ap2 limitRemainderF p Y
  let lhs := qadd q C
  let rhs := qadd r C
  have hp := unit_positive (Γ := Γ) p
  have a₀ := upper_congr (congrFst (constant_at p (cap a b))).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (endpoint_observation p a b hs)
  have a₁ := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp (endpoint_close a b x K p hs h))
  have fixed : Γ ⊢[PRAAx] upper (fstT C) (fstT C) zero P := upper_of_order _ _ _ _ (point_order_refl C)
  have b₁ : Γ ⊢[PRAAx] upper (fstT lhs) (fstT rhs) (K+num 12) P :=
    upper_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
      (point_add_upper_same q r C C (K+num 12) zero P hp a₁ fixed)
  have reg := limit_remainder_regular a b x hs
  have c₁ := GaussianNameRingLaws.add_sample_error limitRemainderF constantF Y C p reg (constant_regular _)
  have c₂ := distance_congr (.eqRefl _) (qadd_congr (.eqRefl r) (constant_at p C)) (.eqRefl _) (.eqRefl _) c₁
  have c₃ := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp (distance_symmetric _ _ _ _ hp c₂))
  exact upper_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (small_join _ _ _ _ _ p (small_join _ _ _ _ _ p a₀ b₁) c₃)

theorem original_margin (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    realOrder constantF correctedF (cap a b) (correctedData a b x) := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have rate := GaussianStirlingGlobalBoundsTranslatedRate.translated_rate a b x hs increment_rate
  have hs' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
  have ht : Δ ⊢[PRAAx] translatedRate (sh a) (sh b) (sh x) (num 30) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using rate.shift
  have env : Γ ⊢[PRAAx] envelope constantF limitF (cap a b) (limitData a b x) (num 30+num 17) := by
    refine .allI ?_
    simpa [envelope,cap,limitData,Syn.shift,sh,Δ] using
      observed (sh a) (sh b) (sh x) (num 30) (var 0) hs' (rate_at _ _ _ _ (var 0) ht)
  have hl := limit_remainder_regular a b x hs
  have hr := remainder_regular a b x hs
  have hc := constant_regular (Γ := Γ) (cubicValue a b)
  have lim := order_from_envelope constantF limitF (cap a b) (limitData a b x) _
    (constant_regular _) (add_fast _ _ _ _ hl hc) env
  have e := remainder_cross a b x hs (GaussianStirlingConstantIdentification.identification x x)
  have ec := add_cross limitRemainderF remainderF constantF constantF (limitRemainderData a b x)
    (remainderData a b x) (cubicValue a b) (cubicValue a b) hl hr hc hc e (cross_refl _ _ hc)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (constant_regular _)) ec lim

set_option maxHeartbeats 800000 in
theorem original_cubic_bound (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] strictOrder constantF correctedF
      (upperValue a b) (correctedData a b x) := by
  let U := upperValue a b
  let M := margin a b
  let X := correctedData a b x
  let u := marginNumerator a b
  let v := marginDenominator a b
  have hU := constant_regular (Γ := Γ) U
  have hB := margin_den_positive a b hs
  have hA := margin_num_positive a b hs
  have hsum := constant_sum (Γ := Γ) M U (cap a b) (.eqRefl _)
  have withMargin := original_margin a b x hs
  have hc := constant_regular (Γ := Γ) (cubicValue a b)
  have reg : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN correctedF X :=
    add_fast remainderF constantF (remainderData a b x) (cubicValue a b) (remainder_regular a b x hs) hc
  have namedMargin : Γ ⊢[PRAAx] realOrder (addF constantF constantF) correctedF (addData M U) X :=
    GaussianNamedRealOrderTransport.transport (addF constantF constantF) constantF correctedF correctedF
      (addData M U) (cap a b) X X hsum (cross_refl correctedF X reg) withMargin
  have strict : Γ ⊢[PRAAx] neg (realOrder constantF constantF M (GaussianPositiveRationalLogarithm.fraction zero one)) :=
    GaussianStirlingMultiplicativeBoundsCaps.strict_fractions zero one u v (le_refl one) hB
      (lt_congr (by ipra_ring) (by ipra_ring) hA)
  have mNonneg := (GaussianRationalNonnegativeFractions.fraction_nonnegative u v hB).andE₁
  have le := point_add_order qzero M U U
    (rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _) mNonneg) (point_order_refl U)
  have hUC : Γ ⊢[PRAAx] GaussianRationalHorner.canonical U := ofGaussian_canonical _ _ (upper_den_positive a hs.andE₁)
  have ule := constant_order U (cap a b) (rationalLE_congr (congrFst (qzero_add U hUC)) (.eqRefl _) le)
  exact .andI (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ ule withMargin)
    (GaussianGammaNativeStrictLogConvexity.strictly_ordered_of_margin _ _ _ _ _ hU strict namedMargin)

theorem actual_positive_rational_signed_cubic_Stirling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶
      strictOrder constantF correctedF (upperValue (var 0) (var 1))
        (correctedData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_cubic_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingCubicBound
