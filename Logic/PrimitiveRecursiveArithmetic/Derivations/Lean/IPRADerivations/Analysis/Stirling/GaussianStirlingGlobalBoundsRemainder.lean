import IPRADerivations.Analysis.Stirling.GaussianStirlingGlobalBounds
import IPRADerivations.Analysis.Stirling.GaussianStirlingConstantIdentification

/-!
# Finite d-sums and the named Stirling remainder

The original Stirling remainder is exactly the finite d-sum plus the
remainder at the translated argument. The latter is bounded by
(1/(12(x+N))) once the fractional logarithmic gamma rate is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_associative add_commutative add_negative zeroF zero_fast zero_at add_zero_left)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianRationalHorner (positive_product qzero qadd)
open GaussianStirlingGlobalBounds (remainderF remainderData remainder_regular first_order_bounds finalUpper translatedRate)
open GaussianStirlingNames (source nameData name_regular)
open GaussianStirlingRationalTelescopers (firstTerm upperValue upperMargin upper_den_positive square_positive small_numeral_positive)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open GaussianStirlingTelescope (shifted shifted_source)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_order_left upper_order_right upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "A" => GaussianStirlingNames.nameF
local notation "C" => GaussianStirlingConstant.nameF
local notation "CD" => GaussianStirlingConstant.nameData
local notation "P" => GaussianStirlingTelescopeName.nameF
local notation "PD" => GaussianStirlingTelescopeName.data

def sumF : PR 2 := addF P remainderF
def sumData (N a b x : PTm n) : PTm n := addData (PD N a b) (remainderData (shifted a b N) b x)
@[simp] theorem subst_sumData {l : ℕ} (σ : Fin n → PTm l) (N a b x : PTm n) :
    Syn.subst σ (sumData N a b x) = sumData (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by
  simp [sumData]

private theorem zeros_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y :=
  GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast x) (zero_fast y)
    (.allI ((zero_at (var 0) (Syn.shift x)).eqTrans (zero_at (var 0) (Syn.shift y)).eqSymm))

private theorem cancel_differences (f g h : PR 2) (x y z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (addF (GaussianNamedDifference.nameF f g) (GaussianNamedDifference.nameF g h))
      (GaussianNamedDifference.nameF f h) (addData (GaussianNamedDifference.data x y) (GaussianNamedDifference.data y z))
      (GaussianNamedDifference.data x z) := by
  let u := negativeData y
  let v := negativeData z
  let G := negativeF g
  let H := negativeF h
  have hu := negative_fast g y hg
  have hv := negative_fast h z hh
  have reorder := add_associative f G (addF g H) x u (addData y v) hf hu (add_fast _ _ _ _ hg hv)
  have swap := cross_symm _ _ _ _ (add_associative G g H u y v hu hg hv)
  have cancel := cross_trans _ _ _ _ _ _ (add_commutative G g u y hu hg) (add_negative g y hg)
  have drop := add_cross (addF G g) zeroF H H (addData u y) v v v
    (add_fast _ _ _ _ hu hg) (zero_fast v) hv hv
    (cross_trans _ _ _ _ _ _ cancel (zeros_cross y v)) (cross_refl _ _ hv)
  have inner := cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ drop (add_zero_left H v hv))
  have lift := add_cross f f (addF G (addF g H)) H x x (addData u (addData y v)) v
    hf hf (add_fast _ _ _ _ hu (add_fast _ _ _ _ hg hv)) hv (cross_refl _ _ hf) inner
  exact cross_trans _ _ _ _ _ _ reorder lift

theorem exact_decomposition (N a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent sumF remainderF (sumData N a b x) (remainderData a b x) := by
  let j := shifted a b N
  let g := GaussianNamedDifference.nameF A A
  let G := GaussianStirlingTelescopeName.endpointData N a b
  let R := remainderData j b x
  have ha := name_regular a b hs
  have hj := name_regular j b (shifted_source a b N hs)
  have hc := GaussianStirlingConstant.name_regular (Γ := Γ) x
  have hr := remainder_regular j b x (shifted_source a b N hs)
  have cut := add_cross P g remainderF remainderF (PD N a b) G R R
    (GaussianStirlingTelescopeName.name_regular N a b hs)
    (GaussianNamedDifference.name_regular A A _ _ ha hj) hr hr
    (GaussianStirlingTelescopeName.telescope_cross N a b hs) (cross_refl _ _ hr)
  exact cross_trans _ _ _ _ _ _ cut (cancel_differences A A C (nameData a b) (nameData j b) (CD x) ha hj hc)

private theorem lower_positive_order (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT (firstTerm a b)) :=
  rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _)
    (GaussianRationalNonnegativeFractions.fraction_nonnegative (b*b) _
      (positive_product _ _ (small_numeral_positive 2) (square_positive a b hs.andE₂))).andE₁

private theorem upper_discard_margin (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] rationalLE (fstT (finalUpper a b)) (fstT (upperValue a b)) := by
  let W := GaussianStirlingRationalTelescopers.denominatorSquare a b
  let M := upperMargin a b
  let V := upperValue a b
  let U := finalUpper a b
  have hW := square_positive a b hs.andE₂
  have hD := positive_product _ _ (positive_product _ _ (small_numeral_positive 14) hW) hW
  have nz := rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _)
    (GaussianRationalNonnegativeFractions.fraction_nonnegative (two*(b*b)*(b*b)) (num 15*W*W) hD).andE₁
  have cV : Γ ⊢[PRAAx] GaussianRationalHorner.canonical V :=
    GaussianRationalHorner.ofGaussian_canonical _ _ (upper_den_positive a hs.andE₁)
  have cU : Γ ⊢[PRAAx] GaussianRationalHorner.canonical U := GaussianRationalMetric.qsub_canonical _ _
  have e := (GaussianRationalLinearProduct.qadd_commutative U M).eqTrans
    (GaussianRationalLinearProduct.add_sub_right M V cV)
  exact rationalLE_congr (congrFst (GaussianReciprocalHorner.qadd_zero_right U cU)) (congrFst e)
    (point_add_order U U qzero M (point_order_refl U) nz)

private theorem tail_envelopes (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] GaussianStirlingGlobalBounds.firstOrderBounds remainderF a b (remainderData a b x)) :
    Γ ⊢[PRAAx] envelope constantF remainderF qzero (remainderData a b x) two ⋏
      envelope remainderF constantF (remainderData a b x) (upperValue a b) two := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let a' := sh a
  let b' := sh b
  let x' := sh x
  let p : PTm (n+1) := var 0
  let X := remainderData a' b' x'
  let L := firstTerm a' b'
  let U := finalUpper a' b'
  have hs' : Δ ⊢[PRAAx] source a' b' := by simpa [Δ,a',b',sh,Fm.shift,Syn.shift] using hs.shift
  have hp := unit_positive (Γ := Δ) p
  have den := positive_product _ _ hp hp
  have h' : Δ ⊢[PRAAx] GaussianStirlingGlobalBounds.firstOrderBounds remainderF a' b' X := by
    simpa [GaussianStirlingGlobalBounds.firstOrderBounds,Δ,a',b',x',X,sh,Fm.shift,Syn.shift] using h.shift
  refine .andI (.allI ?_) (.allI ?_)
  · have d := real_order_at constantF remainderF L X p p h'.andE₁
    have e := upper_congr (congrFst (constant_at p L)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ two (unit p) den d (le_of_eq_add (d := zero) (by ipra_ring)))
    have out := upper_congr (congrFst (constant_at p qzero)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (upper_order_left _ _ _ _ _ (lower_positive_order a' b' hs') e)
    simpa [envelope,a',b',x',X,sh,Δ,p,Syn.shift,GaussianRationalHorner.qzero,ComplexLogarithmRemainder.zeroCode,
      ComplexLogarithmRemainder.code,ZT.ofNat] using out
  · have d := real_order_at remainderF constantF X U p p h'.andE₂
    have e := upper_congr (.eqRefl _) (congrFst (constant_at p U)) (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ two (unit p) den d (le_of_eq_add (d := zero) (by ipra_ring)))
    have out := upper_congr (.eqRefl _) (congrFst (constant_at p (upperValue a' b'))).eqSymm (.eqRefl _) (.eqRefl _)
      (upper_order_right _ _ _ _ _ e (upper_discard_margin a' b' hs'))
    simpa [envelope,a',b',x',X,sh,Δ,p,Syn.shift] using out

theorem original_tail_from_bounds (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] GaussianStirlingGlobalBounds.firstOrderBounds remainderF a b (remainderData a b x)) :
    Γ ⊢[PRAAx] realOrder constantF remainderF qzero (remainderData a b x) ⋏
      realOrder remainderF constantF (remainderData a b x) (upperValue a b) := by
  have e := tail_envelopes a b x hs h
  have hr := remainder_regular a b x hs
  exact .andI (order_from_envelope _ _ _ _ _ (constant_regular _) hr e.andE₁)
    (order_from_envelope _ _ _ _ _ hr (constant_regular _) e.andE₂)

theorem positive_series_remainder_from_rate (N a b x K : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (rate : Γ ⊢[PRAAx] translatedRate (shifted a b N) b x K) :
    Γ ⊢[PRAAx] crossEquivalent sumF remainderF (sumData N a b x) (remainderData a b x) ⋏
      (realOrder constantF remainderF qzero (remainderData (shifted a b N) b x) ⋏
        realOrder remainderF constantF (remainderData (shifted a b N) b x) (upperValue (shifted a b N) b)) := by
  let c := shifted a b N
  have h := shifted_source a b N hs
  have bound := first_order_bounds c b x K h rate (GaussianStirlingConstantIdentification.identification x x)
  exact .andI (exact_decomposition N a b x hs) (original_tail_from_bounds c b x h bound)

theorem actual_Stirling_remainder_finite_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) ⟶ crossEquivalent sumF remainderF
      (sumData (var 0) (var 1) (var 2) (var 3)) (remainderData (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exact_decomposition _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsRemainder
