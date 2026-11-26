import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaSlopeLowerRational
import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaMonotone
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaRecurrence
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartTimeOrder
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogOrder
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeStrictLogConvexity
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelUniform
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# Lower digamma slope on a general positive rational interval

The recurrence isolates the exact reciprocal difference from the
monotone digamma difference at the translated arguments. A common
upper cap M then gives a lower slope of 1/M². The final observations
use the original separate encodings and independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaCompactSlopeLower

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaNative (data nameF name_regular)
open GaussianGammaDigammaSlopeLower (lowerF)
open GaussianGammaDigammaRecurrence (digamma_shift)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaDigammaRescale (datum_congr)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative additive_inverse_value add_sample_error three zeroF zero_fast)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (transport)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingRationalTelescopers (fraction_same)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_of_radius upper_triangle upper_mono positive_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "recData" => GaussianGammaDigammaRecurrence.data

def margin (a b c d M : PTm n) : PTm n := fraction (monus (b*c) (d*a)) (M*M*b*d)

def lowerData (a b c d M : PTm n) : PTm n := addData (data a b) (margin a b c d M)

ipra_subst margin

ipra_subst lowerData

theorem monotone_rational (a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hac : Γ ⊢[PRAAx] le (d*a) (b*c)) : Γ ⊢[PRAAx] realOrder nameF nameF (data a b) (data c d) := by
  let A := d*a
  let C := b*c
  let B := d*b
  have hb := positive_product d b hc.andE₂ ha.andE₂
  have left : Γ ⊢[PRAAx] source A B := .andI (positive_product _ _ hc.andE₂ ha.andE₁) hb
  have right : Γ ⊢[PRAAx] source C B := .andI (positive_product _ _ ha.andE₂ hc.andE₁) hb
  have e₀ := GaussianGammaDigammaRescaling.original_rescaling a b d ha hc.andE₂
  have e₁ := GaussianGammaDigammaRescaling.original_rescaling c d b hc ha.andE₂
  have reindex : Γ ⊢[PRAAx] data C (b*d) ≐ data C B := datum_congr (.eqRefl _) (mul_comm b d)
  exact transport nameF nameF nameF nameF (data a b) (data A B) (data C B) (data c d)
    (cross_symm _ _ _ _ e₀) (GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ reindex (.eqRefl _) e₁)
    (GaussianGammaDigammaMonotone.monotone A C B left right hac)

private theorem combine_constants (x a b c : PTm n) (hx : Γ ⊢[PRAAx] pointCN nameF x) (e : Γ ⊢[PRAAx] qadd a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (addF lowerF constantF) lowerF (addData (addData x a) b) (addData x c) :=
  cross_trans _ _ _ _ _ _ (add_associative nameF constantF constantF x a b hx (constant_regular _) (constant_regular _))
    (add_cross nameF nameF (addF constantF constantF) constantF x x (addData a b) c hx hx
      (add_fast _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
      (cross_refl _ _ hx) (constant_sum a b c e))

private theorem remove_zero (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN nameF x) :
    Γ ⊢[PRAAx] crossEquivalent lowerF nameF (addData x qzero) x :=
  cross_trans _ _ _ _ _ _ (add_cross nameF nameF constantF zeroF x x qzero x hx hx (constant_regular _) (zero_fast _)
    (cross_refl _ _ hx) (cross_symm _ _ _ _ (GaussianGammaRationalWendelUniform.zero_constant x)))
    (GaussianNameRingLaws.add_zero nameF x hx)

theorem reciprocal_lower (a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hac : Γ ⊢[PRAAx] le (d*a) (b*c)) : Γ ⊢[PRAAx]
    realOrder lowerF nameF (addData (data a b) (qsub (fraction b a) (fraction d c))) (data c d) := by
  let x := data a b
  let y := data c d
  let u := fraction b a
  let v := fraction d c
  let w := qsub qzero v
  have hA : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans ha.andE₁ (le_add_right a b)) ha.andE₂
  have hC : Γ ⊢[PRAAx] source (c+d) d := .andI (le_trans hc.andE₁ (le_add_right c d)) hc.andE₂
  have shifted := monotone_rational (a+b) b (c+d) d hA hC (by ipra_le sl hac)
  have step : Γ ⊢[PRAAx] realOrder lowerF lowerF (recData a b) (recData c d) :=
    transport lowerF nameF nameF lowerF _ _ _ _ (cross_symm _ _ _ _ (digamma_shift a b ha)) (digamma_shift c d hc) shifted
  have order := add_order lowerF lowerF constantF constantF (recData a b) (recData c d) w w step
    (order_refl constantF w (constant_regular _))
  have left := combine_constants x u w (qsub u v) (name_regular a b ha)
    (qadd_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)))
  have right := cross_trans _ _ _ _ _ _
    (combine_constants y v w qzero (name_regular c d hc) (additive_inverse_value v)) (remove_zero y (name_regular c d hc))
  exact transport lowerF (addF lowerF constantF) (addF lowerF constantF) nameF _ _ _ _
    (cross_symm _ _ _ _ left) right order

private theorem margin_le_gap (a b c d M : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hM : Γ ⊢[PRAAx] le one M) (hac : Γ ⊢[PRAAx] le (d*a) (b*c)) (hcap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] rationalLE (fstT (margin a b c d M)) (fstT (qsub (fraction b a) (fraction d c))) := by
  let D := a*c
  let A := monus (b*c) (d*a)
  have hD := positive_product a c ha.andE₁ hc.andE₁
  have hm := positive_product (M*M*b) d (positive_product _ _ (positive_product _ _ hM hM) ha.andE₂) hc.andE₂
  have h₀ : Γ ⊢[PRAAx] le a (M*b) := positive_cancel hc.andE₂
    (le_trans hac (le_congr (mul_comm c b) (by ipra_ring) (mul_le_mul_right b hcap)))
  have cap := le_mul_mono h₀ hcap
  have u := fraction_same b a (b*c) D ha.andE₁ hD (by unfold D; ipra_ring)
  have v := fraction_same d c (d*a) D hc.andE₁ hD (by unfold D; ipra_ring)
  have gap := (qsub_congr u v).eqTrans (GaussianEulerPositivePowerChartImageWeights.fraction_difference (d*a) (b*c) D hD hac)
  exact rationalLE_congr (.eqRefl _) (congrFst gap).eqSymm
    (fractions_order A (M*M*b*d) A D hm hD (by dsimp only [A,D]; ipra_le 𝔞(monus (b*c) (d*a))*sl cap))

theorem lower_slope (a b c d M : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hM : Γ ⊢[PRAAx] le one M) (hac : Γ ⊢[PRAAx] le (d*a) (b*c)) (hcap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] realOrder lowerF nameF (lowerData a b c d M) (data c d) := by
  let gap := qsub (fraction b a) (fraction d c)
  have order := add_order nameF nameF constantF constantF (data a b) (data a b) (margin a b c d M) gap
    (order_refl nameF (data a b) (name_regular a b ha)) (constant_order _ _ (margin_le_gap a b c d M ha hc hM hac hcap))
  exact GaussianEulerPowerChartTimeOrder.order_trans lowerF lowerF nameF _ _ _ order (reciprocal_lower a b c d ha hc hac)

theorem lower_slope_at (a b c d M p q : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hM : Γ ⊢[PRAAx] le one M) (hac : Γ ⊢[PRAAx] le (d*a) (b*c)) (hcap : Γ ⊢[PRAAx] le c (M*d)) : Γ ⊢[PRAAx]
    upper (RationalArithmetic.add (fstT (ap2 nameF p (data a b))) (fstT (margin a b c d M)))
      (fstT (ap2 nameF q (data c d))) (num 4*unit q+unit p) (unit p*unit q) := by
  let g := margin a b c d M
  let X := ap2 nameF p (data a b)
  let P := unit p
  let Q := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have err : Γ ⊢[PRAAx] distanceBounded (ap2 lowerF p (lowerData a b c d M)) (qadd X g) three P :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p g)) (.eqRefl _) (.eqRefl _)
      (add_sample_error nameF constantF (data a b) g p (name_regular a b ha) (constant_regular g))
  have raw := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp (distance_symmetric _ _ _ _ hp err))
  have obs := real_order_at lowerF nameF (lowerData a b c d M) (data c d) p q (lower_slope a b c d M ha hc hM hac hcap)
  have joined := upper_triangle _ _ _ _ _ _ _ raw obs
  exact upper_congr (RationalGaussianRealPart.real_add X g) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_mono _ _ _ _ (num 4*Q+P) (P*Q) (positive_product _ _ hp (positive_product _ _ hp hq)) joined
      (le_of_eq_add (d := zero) (by unfold three; ipra_ring)))

theorem strict_rational (a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hac : Γ ⊢[PRAAx] lt (d*a) (b*c)) : Γ ⊢[PRAAx] strictOrder nameF nameF (data a b) (data c d) := by
  let m := margin a b c d c
  let x := data a b
  let y := data c d
  let D := c*c*b*d
  have hD := positive_product (c*c*b) d
    (positive_product _ _ (positive_product _ _ hc.andE₁ hc.andE₁) ha.andE₂) hc.andE₂
  have hp := GaussianEulerUnitLogarithmicMargin.gap_positive (d*a) (b*c) hac
  have pos : Γ ⊢[PRAAx] neg (realOrder constantF constantF m (fraction zero one)) :=
    GaussianStirlingMultiplicativeBoundsCaps.strict_fractions zero one (monus (b*c) (d*a)) D (le_refl one) hD
      (lt_congr (by unfold D; ipra_ring) (by ipra_ring) hp)
  have hcap : Γ ⊢[PRAAx] le c (c*d) := by ipra_le 𝔞(c)*sl hc.andE₂
  have hx := name_regular a b ha
  have hy := name_regular c d hc
  have left := add_commutative constantF nameF m x (constant_regular m) hx
  have shifted : Γ ⊢[PRAAx] realOrder (addF constantF nameF) nameF (addData m x) y :=
    transport _ _ _ _ _ _ _ _ left (cross_refl nameF y hy) (lower_slope a b c d c ha hc hc.andE₁ (le_of_lt hac) hcap)
  exact .andI (monotone_rational a b c d ha hc (le_of_lt hac))
    (GaussianGammaNativeStrictLogConvexity.strictly_ordered_of_margin nameF nameF m x y hx pos shifted)

theorem actual_original_positive_digamma_compact_lower_slope_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source (var 0) (var 1) ⋏ (source (var 2) (var 3) ⋏ (le one (var 4) ⋏
        (le (var 3*var 0) (var 1*var 2) ⋏ le (var 2) (var 4*var 3))))) ⟶
        realOrder lowerF nameF (lowerData (var 0) (var 1) (var 2) (var 3) (var 4)) (data (var 2) (var 3))) :=
  closeUniv 5 (.impI (lower_slope _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

theorem actual_original_positive_digamma_strict_rational_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source (var 0) (var 1) ⋏ (source (var 2) (var 3) ⋏ lt (var 3*var 0) (var 1*var 2))) ⟶
        strictOrder nameF nameF (data (var 0) (var 1)) (data (var 2) (var 3))) :=
  closeUniv 4 (.impI (strict_rational _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaCompactSlopeLower
