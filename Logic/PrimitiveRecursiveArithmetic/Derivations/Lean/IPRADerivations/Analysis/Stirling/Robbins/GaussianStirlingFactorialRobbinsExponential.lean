import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingFactorialRobbins
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# The strict exponential forms of the Robbins and Stirling bounds

The original logarithmic margins are positive rational numbers. Strict
monotonicity of the original exponential preserves both margins, and
the exact quotient identity identifies the exponential of the remainder.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (precision upperSlack remove_upper_slack)
open GaussianPositiveRationalLogarithm (fraction logF data)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (qnegative)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingFactorialRobbinsQuotient (factorialRatioF factorialRatioData exp_remainder_is_factorial_ratio)
open GaussianStirlingMultiplicative (quotientF quotientData multiplicative_formula)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData remainder_regular)
open GaussianStirlingMultiplicativeBounds (weak_upper_log weak_lower_log remainder_real)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order logarithm_rectangles)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_exponential_order strict_transport)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (firstTerm upperValue lowerValue denominatorSquare
  square_positive small_numeral_positive upper_den_positive lower_den_positive lower_margin_numerator_positive)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper_mono upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "finalU" => GaussianStirlingGlobalBounds.finalUpper
local notation "finalL" => GaussianStirlingRobbins.finalLower

abbrev capF : PR 2 := E constantF
def capData (c : PTm n) : PTm n := ed constantF c

private theorem exact_constant_order (a b : PTm n) (h : Γ ⊢[PRAAx] realOrder constantF constantF a b) :
    Γ ⊢[PRAAx] rationalLE (fstT a) (fstT b) := by
  let t := precision (fstT a) (fstT b) one two
  have hp := unit_positive (Γ := Γ) t
  have orig := upper_congr (congrFst (constant_at t a)) (congrFst (constant_at t b))
    (.eqRefl _) (.eqRefl _) (real_order_at constantF constantF a b t t h)
  have slack : Γ ⊢[PRAAx] upperSlack (fstT a) (fstT b) zero one two t := by
    unfold upperSlack
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) orig
      (le_of_eq_add (d := zero) (by ipra_ring))
  have h' := remove_upper_slack (fstT a) (fstT b) zero one two slack
  exact le_congr (by unfold RationalValueBounds.crossLeft RationalArgmin.left; ipra_ring)
    (by unfold RationalValueBounds.crossLeft RationalArgmin.left; ipra_ring) h'

private theorem frac_can (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (fraction a b) := GaussianRationalHorner.ofGaussian_canonical _ _ hb

private theorem frac_real (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples constantF (fraction a b) :=
  GaussianStirlingNames.constant_real _ (frac_can a b hb) (GaussianStirlingNames.fraction_axis a b hb)

private theorem positive_contradiction (m d : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] rationalLE (fstT (fraction m d)) (fstT qzero)) : Γ ⊢[PRAAx] Fm.bot := by
  have r := rationalLE_congr (fraction_real_part m d hd) RationalGaussianRealPart.real_zero h
  have c := GaussianRationalMetric.comparison_to_cleared _ _ _ _ d one
    (GaussianEuclideanDistanceName.fraction_represents m d hd)
    (RationalGaussianEmbedding.scalar_zero_represents (Γ := Γ) one) r
  have z : Γ ⊢[PRAAx] le m zero := le_congr (one_mul m) (zero_mul d) c
  exact lt_irrefl zero _ (le_trans hm z)

private theorem strict_add_margin (q m d : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] neg (realOrder constantF constantF (qadd q (fraction m d)) q) := by
  refine .impI ?_
  let v := fraction m d
  let Δ := realOrder constantF constantF (qadd q v) q :: Γ
  have h := exact_constant_order (Γ := Δ) (qadd q v) q Prf.hyp0
  have r := point_add_order (qadd q v) q (qnegative q) (qnegative q) h (point_order_refl _)
  have lo := GaussianRationalSyntheticDivision.qadd_sub_cancel (Γ := Δ) q v (frac_can m d hd.wk)
  have hi := GaussianCoefficientNormOrder.qsub_self (Γ := Δ) q
  exact positive_contradiction m d hm.wk hd.wk (rationalLE_congr (congrFst lo) (congrFst hi) r)

private theorem strict_sub_margin (q m d : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] neg (realOrder constantF constantF q (qadd q (qnegative (fraction m d)))) := by
  refine .impI ?_
  let v := fraction m d
  let Δ := realOrder constantF constantF q (qadd q (qnegative v)) :: Γ
  have h := exact_constant_order (Γ := Δ) q (qadd q (qnegative v)) Prf.hyp0
  have r := point_add_order q (qadd q (qnegative v)) (qnegative q) (qnegative q) h (point_order_refl _)
  have lo := GaussianCoefficientNormOrder.qsub_self (Γ := Δ) q
  have hi := GaussianRationalSyntheticDivision.qadd_sub_cancel (Γ := Δ) q (qnegative v)
    (GaussianRationalMetric.qnegative_canonical _)
  have centered := rationalLE_congr (congrFst lo) (congrFst hi) r
  have r' := point_add_order qzero (qnegative v) v v centered (point_order_refl _)
  have cancel := (GaussianReciprocalHorner.qadd_commutative (Γ := Δ) (qnegative v) v).eqTrans
    (GaussianCoefficientNormOrder.qsub_self v)
  have first := GaussianRationalSyntheticDivision.qzero_add (Γ := Δ) v (frac_can m d hd.wk)
  exact positive_contradiction m d hm.wk hd.wk (rationalLE_congr (congrFst first) (congrFst cancel) r')

theorem upper_log_strict (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hi : Γ ⊢[PRAAx] realOrder remainderF constantF (remainderData a b x) (finalU a b)) :
    Γ ⊢[PRAAx] strictOrder remainderF constantF (remainderData a b x) (upperValue a b) := by
  let D := denominatorSquare a b
  let m := two*(b*b)*(b*b)
  let d := num 15*D*D
  have hD := square_positive a b hs.andE₂
  have db := positive_product _ _ (positive_product _ _ (small_numeral_positive 14) hD) hD
  have hb := positive_product _ _ hs.andE₂ hs.andE₂
  have mb := positive_product _ _ (positive_product _ _ RationalAlgebra.two_positive hb) hb
  have impossible := strict_sub_margin (upperValue a b) m d mb db
  refine .andI (order_trans _ _ _ _ _ _ hi (weak_upper_log a b hs)) (.impI ?_)
  exact impossible.wk.impE (order_trans _ _ _ _ _ _ Prf.hyp0 hi.wk)

theorem lower_log_strict (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (lo : Γ ⊢[PRAAx] realOrder constantF remainderF (finalL a b) (remainderData a b x)) :
    Γ ⊢[PRAAx] strictOrder constantF remainderF (lowerValue a b) (remainderData a b x) := by
  let D := denominatorSquare a b
  let m := b*b*b*monus (num 24*a) (num 23*b)
  let d := num 3*D*(num 12*a+b)*(num 12*a+num 13*b)
  have hd := square_positive a b hs.andE₂
  have db : Γ ⊢[PRAAx] le one d :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (small_numeral_positive 2) hd)
      (lower_den_positive a b hs.andE₁)) (le_trans (upper_den_positive a hs.andE₁) (le_add_right _ _))
  have n := lower_margin_numerator_positive a b hs.andE₁ hba
  have mb : Γ ⊢[PRAAx] le one m := positive_product _ _
    (positive_product _ _ (positive_product _ _ hs.andE₂ hs.andE₂) hs.andE₂) n
  have impossible := strict_add_margin (lowerValue a b) m d mb db
  refine .andI (order_trans _ _ _ _ _ _ (weak_lower_log a b hs) lo) (.impI ?_)
  exact impossible.wk.impE (order_trans _ _ _ _ _ _ lo.wk Prf.hyp0)

private theorem positive_log_real (a b : PTm n) : Γ ⊢[PRAAx] realSamples logF (data a b) := by
  refine .allI ?_
  let s := Syn.shift a
  let t := Syn.shift b
  have hc : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 logF (var 0) (data s t)) :=
    GaussianNameArithmetic.add_canonical _ _ _ _ _
  have h := GaussianRealNameExponentialInjectivity.axis_sample_at logF (data s t) (var 0)
    (GaussianNamedPositiveLogarithmScale.exact_rational_axis (Γ := Γ.map Fm.shift) s t)
  simpa [realSamples,Syn.shift,s,t] using Prf.andI hc h

private theorem exponential_log_value (a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent (E logF) constantF (ed logF (data a b)) (fraction a b) := by
  have first := GaussianExponentialRadiusIndependence.same_input_cross logF (U logF (data a b))
    (GaussianPositiveRationalLogarithm.radius a b) (data a b)
    (exponential_input _ _ (GaussianPositiveRationalLogarithm.name_regular _ _ hs))
    (GaussianPositiveRationalLogarithm.exponential_input _ _ hs)
  exact cross_trans _ _ _ _ _ _ first (GaussianPositiveRationalLogarithm.exponential_fraction a b hs)

theorem rational_exponential_bounds (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (bounds : Γ ⊢[PRAAx] GaussianStirlingGlobalBounds.firstOrderBounds remainderF a b (remainderData a b x)) :
    Γ ⊢[PRAAx] strictOrder constantF quotientF (fraction one one) (quotientData a b x) ⋏
      strictOrder quotientF capF (quotientData a b x) (capData (upperValue a b)) := by
  let X : PTm n := data (one+zero) one
  let z : PTm n := fraction zero one
  let t := firstTerm a b
  let m := b*b
  let d := num 3*denominatorSquare a b
  let y := remainderData a b x
  have db := positive_product _ _ (small_numeral_positive 2) (square_positive a b hs.andE₂)
  have mb : Γ ⊢[PRAAx] le one m := positive_product _ _ hs.andE₂ hs.andE₂
  have xsource : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (one+zero) one :=
    .andI (le_add_right one zero) (le_refl one)
  have zl := (logarithm_rectangles (Γ := Γ) (one : PTm n) zero (le_refl one)).andE₂
  have positive := strict_fractions zero one m d (le_refl one) db (by
    change Γ ⊢[PRAAx] le (ConciseIPRA.PTm.succ (d*zero)) (m*one)
    ipra_le sl mb)
  have zlt := constant_order z t (fractions_order zero one m d (le_refl one) db (by ipra_le 𝔞 m))
  have left : Γ ⊢[PRAAx] strictOrder logF remainderF X y := by
    refine .andI (order_trans _ _ _ _ _ _ zl (order_trans _ _ _ _ _ _ zlt bounds.andE₁)) (.impI ?_)
    exact positive.wk.impE (order_trans _ _ _ _ _ _ bounds.andE₁.wk
      (order_trans _ _ _ _ _ _ Prf.hyp0 zl.wk))
  have gamma := multiplicative_formula a b x hs
  have yg := remainder_regular a b x hs
  have yr := remainder_real a b x hs
  have lp := strict_exponential_order _ _ _ _ (GaussianPositiveRationalLogarithm.name_regular _ _ xsource)
    yg (positive_log_real _ _) yr left
  have up := strict_exponential_order _ _ _ _ yg (constant_regular _) yr
    (frac_real b _ (upper_den_positive a hs.andE₁)) (upper_log_strict a b x hs bounds.andE₂)
  have oneEq := GaussianStirlingRationalTelescopers.fraction_same (Γ := Γ) (one+zero) one one one
    (le_refl one) (le_refl one) (by ipra_ring)
  have low := cross_trans _ _ _ _ _ _ (exponential_log_value _ _ xsource)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ oneEq)
  exact .andI
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ low) gamma lp)
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ gamma) (cross_refl _ _ (GaussianStirlingLogDuplication.exponential_regular _ _ (constant_regular _))) up)

theorem factorial_exponential_bounds (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] strictOrder capF factorialRatioF (capData (lowerValue i one)) (factorialRatioData i x) ⋏
      strictOrder factorialRatioF capF (factorialRatioData i x) (capData (upperValue i one)) := by
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have b := GaussianStirlingRobbins.integer_bounds i x hi
  have gr := remainder_regular i one x hs
  have ax := remainder_real i one x hs
  have gamma := exp_remainder_is_factorial_ratio i x hi
  have l := strict_exponential_order _ _ _ _ (constant_regular _) gr
    (frac_real _ _ (lower_den_positive i one hi)) ax (lower_log_strict i one x hs hi b.andE₁)
  have u := strict_exponential_order _ _ _ _ gr (constant_regular _) ax
    (frac_real _ _ (upper_den_positive i hi)) (upper_log_strict i one x hs b.andE₂)
  have hrL := GaussianStirlingLogDuplication.exponential_regular constantF (lowerValue i one) (constant_regular (Γ := Γ) _)
  have hrU := GaussianStirlingLogDuplication.exponential_regular constantF (upperValue i one) (constant_regular (Γ := Γ) _)
  exact .andI (strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ hrL) gamma l)
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ gamma) (cross_refl _ _ hrU) u)

theorem actual_factorial_Robbins_exponential_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶
      (strictOrder capF factorialRatioF (capData (lowerValue (var 0) one)) (factorialRatioData (var 0) (var 1)) ⋏
        strictOrder factorialRatioF capF (factorialRatioData (var 0) (var 1)) (capData (upperValue (var 0) one)))) :=
  closeUniv 2 (.impI (factorial_exponential_bounds _ _ Prf.hyp0))

theorem actual_positive_rational_Stirling_exponential_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 0) (var 1) ⋏ GaussianStirlingGlobalBounds.firstOrderBounds remainderF (var 0) (var 1)
      (remainderData (var 0) (var 1) (var 2))) ⟶
      (strictOrder constantF quotientF (fraction one one) (quotientData (var 0) (var 1) (var 2)) ⋏
        strictOrder quotientF capF (quotientData (var 0) (var 1) (var 2)) (capData (upperValue (var 0) (var 1))))) :=
  closeUniv 3 (.impI (rational_exponential_bounds _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingFactorialRobbinsExponential
