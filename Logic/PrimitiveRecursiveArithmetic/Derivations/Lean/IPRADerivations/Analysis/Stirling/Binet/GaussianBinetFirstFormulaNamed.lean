import IPRADerivations.Analysis.Stirling.Binet.Laplace.Exhaustion.GaussianBinetLaplaceNamed
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder

/-!
# Binet's first formula on actual regular right half-plane names

The named remainder is the literal combination of the existing
named log-Gamma, logarithm, input and Stirling constant. A common
late observation freezes these operations and the actual improper
integral at the same signed rational point. The rational first
formula removes the middle expression with a dyadic error allowance.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFirstFormulaNamed

open_ipra
open GaussianBinetLaplaceNamed (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator subst_independentRate)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator point realNumerator sign)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithmNamed.nameF
local notation "G" => GaussianLogGammaEulerNamed.nameF
local notation "J" => GaussianBinetLaplaceNamed.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithmNamed.pointData
local notation "gd" => GaussianLogGammaEulerNamed.pointData
local notation "dataAt" => GaussianNamedRightHalfPlaneLift.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "S" => GaussianBinetStirlingRemainder.nameF
local notation "sd" => GaussianBinetStirlingRemainderRate.pointData
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData

private def negativeHalf : PTm n := qnegative (fraction one two)
def offsetF (f : PR 2) : PR 2 := addF f constantF
def offsetData (x : PTm n) : PTm n := addData x negativeHalf
def weightedF (f : PR 2) : PR 2 := multiplyF (offsetF f) (L f)
def weightedData (f : PR 2) (x M R : PTm n) : PTm n :=
  multiplyData (offsetF f) (L f) (offsetData x) (dataAt x M R)
def coreF (f : PR 2) : PR 2 := addF (Diff (G f) (weightedF f)) f
def coreData (f : PR 2) (x M R : PTm n) : PTm n :=
  addData (dd (dataAt x M R) (weightedData f x M R)) x
def remainderF (f : PR 2) : PR 2 := Diff (coreF f) C
def remainderData (f : PR 2) (x M R w : PTm n) : PTm n := dd (coreData f x M R) (cd w)
def productCost (f : PR 2) (x M R : PTm n) : PTm n := GaussianNameBounds.U (L f) (dataAt x M R)+(R+one)
def cost (f : PR 2) (x M R : PTm n) : PTm n := productCost f x M R+num 5

ipra_subst remainderData [coreData, weightedData, offsetData, negativeHalf, one, two]

ipra_subst cost [productCost, one]

private theorem offset_regular (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (offsetF f) (offsetData x) :=
  add_fast f constantF x negativeHalf hx (constant_regular _)

private theorem weighted_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (weightedF f) (weightedData f x M R) :=
  multiply_fast _ _ _ _ (offset_regular f x h.andE₁.andE₁)
    (GaussianRightHalfPlaneLogarithmNamed.name_regular f x M R h)

private theorem core_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (coreF f) (coreData f x M R) :=
  add_fast _ _ _ _ (GaussianNamedDifference.name_regular _ _ _ _
    (GaussianLogGammaEulerNamed.name_regular f x M R h) (weighted_regular f x M R h)) h.andE₁.andE₁

theorem remainder_regular (f : PR 2) (x M R w : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (remainderF f) (remainderData f x M R w) :=
  GaussianNamedDifference.name_regular _ _ _ _ (core_regular f x M R h) (GaussianStirlingConstant.name_regular w)

private theorem frozen_argument (f : PR 2) (x s k R K : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hsk : Γ ⊢[PRAAx] le s k) (hq : Γ ⊢[PRAAx] certificate (ap2 f k x) R K) :
    Γ ⊢[PRAAx] independentRate f constantF x (point (ap2 f k x)) one (unit s) := by
  let q := ap2 f k x
  let u := unit s
  have hu := unit_positive (Γ := Γ) s
  have raw := GaussianSignedNameExponentialOrder.own_sample_rate f x k hx
  have earlier : Γ ⊢[PRAAx] independentRate f constantF x q one u :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive k) hu
      (le_congr (one_mul u).eqSymm (one_mul (unit k)).eqSymm (GaussianExponentialReference.unit_monotone hsk)) raw
  have hd := distance_symmetric _ _ _ _ (le_refl one)
    (GaussianNamedRightHalfPlaneSigned.point_distance_raw q hq.andE₁.andE₁.andE₁.andE₁)
  have hd' := distance_radius_mono _ _ zero one zero u (le_refl one) hu (by ipra_le 0) hd
  have next := GaussianNamedAddRate.constant_rate q (point q) zero u hu hd'
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (add_zero one) (.eqRefl u)
    (GaussianNamedRateComposition.same_denominator f constantF constantF x q (point q) one u zero hu earlier next)

private theorem offset_bound (q R K : PTm n) (hq : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] bounded (GaussianBinetStirlingRemainderRate.pointOffset q) (R+one) one := by
  have b : Γ ⊢[PRAAx] bounded (fraction one two) one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one (le_succ_self one)
      (le_congr (.eqRefl _) (one_mul _).eqSymm (le_succ_self one))
  exact GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
    (GaussianNamedRightHalfPlaneSigned.point_bound q R K hq)
    (GaussianRationalReciprocal.bounded_negative _ _ one (le_refl one) b)

private theorem rational_offset_rate (f : PR 2) (x q D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] pointCN f x) (h : Γ ⊢[PRAAx] independentRate f constantF x (point q) one D) :
    Γ ⊢[PRAAx] independentRate (offsetF f) constantF (offsetData x) (GaussianBinetStirlingRemainderRate.pointOffset q) one D := by
  let c : PTm n := negativeHalf
  let sum := addF constantF constantF
  let d := addData (point q) c
  have raw := GaussianNamedAddRate.independent_rate f constantF constantF constantF x c (point q) c one D zero one
    hD (le_refl one) h (GaussianNamedDifferenceRate.self_rate _ _ (constant_regular c))
  have r : Γ ⊢[PRAAx] independentRate (offsetF f) sum (offsetData x) d one D :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) raw
  have right := GaussianNamedGammaHalfShift.constant_sum (Γ := Γ) (point q) c (GaussianBinetStirlingRemainderRate.pointOffset q) (.eqRefl _)
  exact GaussianNamedRateTransport.transport _ sum _ constantF _ d _ _ _ D hD r
    (cross_refl _ _ (offset_regular f x hf)) (GaussianNameEquivalence.cross_symm _ _ _ _ right)

theorem frozen_remainder_rate (f : PR 2) (x M R w s k : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R)
    (hsk : Γ ⊢[PRAAx] le s k)
    (hlk : Γ ⊢[PRAAx] le (GaussianRightHalfPlaneLogarithmNamed.clock s M R) k)
    (hgk : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlaneLift.clock GaussianLogGammaEulerNamed.rationalMap s M R) k) :
    Γ ⊢[PRAAx] independentRate (remainderF f) S (remainderData f x M R w) (sd (ap2 f k x) w)
      (one+productCost f x M R+one) (unit s) := by
  let q := ap2 f k x
  let D := unit s
  let x' := dataAt x M R
  let Cw := productCost f x M R
  let a := realNumerator q
  let b := imagNumerator q
  let d := denominator q
  let signBit := sign q
  let O := GaussianBinetStirlingRemainderRate.pointOffset q
  let W := GaussianBinetStirlingRemainder.weightedF
  let wd := GaussianBinetStirlingRemainder.weightedData a b d signBit
  let c' := GaussianBinetStirlingRemainder.coreData a b d signBit
  let p' := weightedData f x M R
  have hD := unit_positive (Γ := Γ) s
  have qcert := GaussianNamedRightHalfPlaneLift.late_certificate f x k M R h
    (le_trans (GaussianNamedRightHalfPlaneLift.clock_margin GaussianRightHalfPlaneLogarithmNamed.rationalMap s M R) hlk)
  have hh := h.andE₁.andE₁
  have fa := frozen_argument f x s k R (two*M) hh hsk qcert
  have fo := rational_offset_rate f x q D hD hh fa
  have lx := GaussianRightHalfPlaneLogarithmNamed.name_regular f x M R h
  have gx := GaussianLogGammaEulerNamed.name_regular f x M R h
  have lq := GaussianRightHalfPlaneLogarithm.regular a b d signBit qcert.andE₁.andE₁
  have gq := GaussianLogGammaEulerCofinal.canonical_regular a b d signBit qcert.andE₁.andE₁
  have lr := GaussianRightHalfPlaneLogarithmNamed.late_rational_rate f s k x M R h hlk
  have gr : Γ ⊢[PRAAx] independentRate (G f) GaussianLogGammaEulerCofinal.nameF x' (gd q) one D := by
    let φ := independentRate (G f) GaussianLogGammaEulerCofinal.nameF (Syn.shift x') (var 0) (Syn.shift one) (Syn.shift D)
    have raw := GaussianLogGammaEulerNamed.late_rational_rate f s k x M R h hgk
    simpa only [φ,subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqSubst1 φ (GaussianLogGammaEulerNamed.rational_data_at q)
        (by simpa only [φ,subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,q,x',D] using raw)
  have bound := GaussianNameBounds.all_samples_bounded _ _ lx
  have qBound := GaussianEulerNamedPowerScalingPowerFrozen.constant_bound O (R+one) (offset_bound q R (two*M) qcert)
  have wRate : Γ ⊢[PRAAx] independentRate (weightedF f) W p' wd Cw D := by
    have raw := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator (offsetF f) (L f)
      constantF GaussianRightHalfPlaneLogarithm.nameF (offsetData x) x' O (ld q) one one D
      (GaussianNameBounds.U (L f) x') (R+one) hD (offset_regular _ _ hh) lx (constant_regular O) lq bound qBound fo lr
    exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by dsimp only [Cw,productCost]; ipra_ring) (.eqRefl _) raw
  have wx := weighted_regular f x M R h
  have wq := GaussianBinetStirlingRemainder.weighted_regular a b d signBit qcert.andE₁.andE₁
  have D2 := positive_product _ _ hD hD
  have main : Γ ⊢[PRAAx] independentRate (Diff (G f) (weightedF f)) (Diff GaussianLogGammaEulerCofinal.nameF W)
      (dd x' p') (dd (gd q) wd) (one+Cw) D := by
    have raw := GaussianNamedDifferenceRate.original_rate (G f) (weightedF f) GaussianLogGammaEulerCofinal.nameF W
      x' p' (gd q) wd one D Cw D (.andI (.andI hD hD) (.andI (.andI gx wx) (.andI (.andI gq wq) (.andI gr wRate))))
    exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ D2 hD
      (le_of_eq_add (d := zero) (by dsimp only [D,GaussianNamedDifferenceRate.leadingNumerator,GaussianNamedDifferenceRate.leadingDenominator]; ipra_ring)) raw
  have core : Γ ⊢[PRAAx] independentRate (coreF f) GaussianBinetStirlingRemainder.coreF (coreData f x M R) c' (one+Cw+one) D := by
    have raw := GaussianNamedAddRate.independent_rate _ _ _ _ _ _ _ _ (one+Cw) D one D hD hD main fa
    exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ D2 hD
      (le_of_eq_add (d := zero) (by dsimp only [D,GaussianNamedRateComposition.leadingNumerator,GaussianNamedRateComposition.leadingDenominator]; ipra_ring)) raw
  exact GaussianNamedDifferenceRate.same_right_rate (coreF f) GaussianBinetStirlingRemainder.coreF C
    (coreData f x M R) c' (cd w) (one+Cw+one) D hD (core_regular f x M R h)
    (GaussianBinetStirlingRemainder.core_regular a b d signBit qcert.andE₁.andE₁) (GaussianStirlingConstant.name_regular w) core

theorem original_observation (f : PR 2) (p x M R w : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (remainderF f) p (remainderData f x M R w))
      (ap2 (J f) p (dataAt x M R)) (cost f x M R) (unit p) := by
  let j := GaussianBinetLaplaceNamed.clock p M R
  let g := GaussianNamedRightHalfPlaneLift.clock GaussianLogGammaEulerNamed.rationalMap p M R
  let l := GaussianRightHalfPlaneLogarithmNamed.clock p M R
  let k := (j+(g+l))+p
  let q := ap2 f k x
  let v := dataAt x M R
  let r := remainderData f x M R w
  let D := unit p
  let A := one+productCost f x M R+one
  let Jq := GaussianBinetLaplaceNamed.pointData q
  let JR := GaussianBinetLaplaceImproperName.nameF
  have hD := unit_positive (Γ := Γ) p
  have hj : Γ ⊢[PRAAx] le j k := le_trans (le_add_right j (g+l)) (le_add_right _ _)
  have hg : Γ ⊢[PRAAx] le g k := le_trans (le_add_right g l) (le_trans (le_add_left (g+l) j) (le_add_right _ _))
  have hl : Γ ⊢[PRAAx] le l k := le_trans (le_add_left l g) (le_trans (le_add_left (g+l) j) (le_add_right _ _))
  have cq := GaussianNamedRightHalfPlaneLift.late_certificate f x k M R h
    (le_trans (GaussianNamedRightHalfPlaneLift.clock_margin GaussianRightHalfPlaneLogarithmNamed.rationalMap p M R) hl)
  have rem := frozen_remainder_rate f x M R w p k h (le_add_left _ _) hl hg
  have jr := GaussianBinetLaplaceNamed.late_rational_rate f p k x M R h hj
  have rational := GaussianBinetFirstFormula.equivalent (realNumerator q) (imagNumerator q) (denominator q) (sign q) w cq.andE₁.andE₁
  have toIntegral : Γ ⊢[PRAAx] independentRate (remainderF f) JR r Jq A D :=
    GaussianNamedRateTransport.transport _ S _ JR r (sd q w) r Jq A D hD rem
      (cross_refl _ _ (remainder_regular f x M R w h)) (GaussianNameEquivalence.cross_symm _ _ _ _ rational)
  have fromIntegral := GaussianNamedRateComposition.symmetric (J f) JR v Jq one D hD jr
  have together := GaussianNamedRateComposition.same_denominator (remainderF f) JR (J f) r Jq v A D one hD toIntegral fromIntegral
  have raw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p p together
  exact distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive D p p hD) hD
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,cost,A,D]; ipra_ring)) raw

theorem equivalent (f : PR 2) (x M R w : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (remainderF f) (J f) (remainderData f x M R w) (dataAt x M R) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost f x M R)
    (remainder_regular f x M R w h) (GaussianBinetLaplaceNamed.name_regular f x M R h) (.allI ?_)
  let s (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (s x) (s M) (s R) := by
    simpa [s,Fm.shift,Syn.shift,GaussianNamedRightHalfPlaneLift.source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,subst_remainderData,subst_cost,
    GaussianNamedRightHalfPlaneLift.subst_data] using
    original_observation f (var 0) (s x) (s M) (s R) (s w) hs

theorem actual_first_Binet_formula_named_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 1) (var 2) ⟶ crossEquivalent (remainderF f) (J f)
      (remainderData f (var 0) (var 1) (var 2) (var 3)) (dataAt (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (equivalent f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetFirstFormulaNamed
