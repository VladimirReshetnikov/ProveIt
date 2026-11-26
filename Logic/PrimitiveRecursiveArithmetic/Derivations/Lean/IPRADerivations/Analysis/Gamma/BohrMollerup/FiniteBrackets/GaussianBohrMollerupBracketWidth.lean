import IPRADerivations.Analysis.Gamma.BohrMollerup.FiniteBrackets.GaussianBohrMollerupBracketEndpoints
import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupLogWindow
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSqrtBrackets

/-!
# The exact general-B Bohr–Mollerup width bound

The literal upper-minus-lower name is nonnegative and at most
B^2/j, with j=n-1. In particular j=B^2*2^(p+2) supplies the dyadic
width used for the squeeze.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketWidth

open_ipra
open GaussianBohrMollerupBlockChord (source)
open GaussianBohrMollerupBracketEndpoints (widthF widthData ratioData width_identity ratio_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalLogOrder (order_refl)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder constant_order)
open GaussianNamedRealOrderLinear (fractionData fractional_order)
open GaussianNamedRealOrderTransport (transport)
open GaussianNaturalScaleProductName (productF)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (positive_product qzero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "logData" => GaussianHarmonicLogarithmName.data
local notation "R" => productF H

private theorem fraction_order (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (a*d) (c*b)) :
    Γ ⊢[PRAAx] realOrder constantF constantF (fraction a b) (fraction c d) := by
  have cleared : Γ ⊢[PRAAx] zle (ZT.ofNat (a*d)) (ZT.ofNat (c*b)) := by
    change Γ ⊢[PRAAx] le (a*d+zero) (c*b+zero)
    exact le_congr (add_zero _).eqSymm (add_zero _).eqSymm h
  have ord : Γ ⊢[PRAAx] zle (ZT.ofNat a*ZT.ofNat d) (ZT.ofNat c*ZT.ofNat b) :=
    PolynomialBisection.zle_congr (by ipra_simps) (by ipra_simps) cleared
  have cmp := RationalArithmetic.order_of_representations _ _ (ZT.ofNat a) (ZT.ofNat c) b d
    (GaussianGammaHalfSqrtBrackets.fraction_first_represents a b hb)
    (GaussianGammaHalfSqrtBrackets.fraction_first_represents c d hd) hb hd ord
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let x := fraction (sh a) (sh b)
  let y := fraction (sh c) (sh d)
  have hs : Δ ⊢[PRAAx] RationalArgmin.rationalLE (fstT x) (fstT y) :=
    by simpa [Δ,x,y,Fm.shift,sh,Syn.shift] using cmp.shift.shift
  simpa only [realOrder,Δ,sh,x,y,Syn.shift,GaussianPositiveRationalLogarithm.subst_fraction] using
    RationalValueBounds.upper_congr
      (congrFst (GaussianGammaCanonicalExponent.constant_at (var 1) x)).eqSymm
      (congrFst (GaussianGammaCanonicalExponent.constant_at (var 0) y)).eqSymm (.eqRefl _) (.eqRefl _)
      (RationalValueBounds.upper_of_order _ _ (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0)) hs)

private theorem scaled_constant (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] crossEquivalent (productF constantF) constantF
      (fractionData constantF a b (fraction c d)) (fraction (a*c) (b*d)) :=
  cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross (fraction a b) (fraction c d))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianEulerDampedTimeRate.fraction_product a b c d hb hd))

theorem ratio_bounds (a b B j : PTm n) (hs : Γ ⊢[PRAAx] source a b B) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] realOrder constantF R qzero (ratioData a b B j) ⋏
      realOrder R constantF (ratioData a b B j) (fraction (B*B) j) := by
  let x := logData (j+B) j
  let y := fraction B (j+B)
  let v := fraction B j
  let s := ratioData a b B j
  let l := fraction (a*B) (b*(j+B))
  let u := fraction (a*B) (b*j)
  let w := fraction (B*B) j
  let C := constantF
  let F := productF constantF
  have hb := hs.andE₁.andE₂
  have hd := le_trans hj (le_add_right j B)
  have old := GaussianHarmonicLogarithmName.cross_original (j+B) j (.andI hd hj)
  have hx := GaussianHarmonicLogarithmName.name_regular (j+B) j (.andI hd hj)
  have hy := constant_regular (Γ := Γ) y
  have hv := constant_regular (Γ := Γ) v
  have rect := GaussianStirlingMultiplicativeBoundsLog.logarithm_rectangles j B hj
  have raw : Γ ⊢[PRAAx] realOrder C H y x :=
    transport _ _ _ _ _ _ _ _ (cross_refl _ _ hy) old rect.andE₁
  have hL : Γ ⊢[PRAAx] realOrder C R l s :=
    transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (scaled_constant a b B (j+B) hb hd))
      (cross_refl _ _ (ratio_regular a b B j hj)) (fractional_order C H a b y x hb hy hx raw)
  have hU : Γ ⊢[PRAAx] realOrder R C s u :=
    transport _ _ _ _ _ _ _ _ (cross_refl _ _ (ratio_regular a b B j hj)) (scaled_constant a b B j hb hj)
      (fractional_order H C a b x v hb hx hv (GaussianBohrMollerupLogWindow.unscaled_window_order j B hj))
  have low : Γ ⊢[PRAAx] realOrder C C qzero l := by
    have zer := GaussianGammaRationalWendelBoundary.fraction_zero (Γ := Γ) one (le_refl one)
    have p : Γ ⊢[PRAAx] le (zero*(b*(j+B))) ((a*B)*one) :=
      le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _)
    exact transport _ _ _ _ _ _ _ _
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ zer.eqSymm) (cross_refl _ _ (constant_regular _))
      (fraction_order zero one (a*B) (b*(j+B)) (le_refl one) (positive_product _ _ hb hd) p)
  have high : Γ ⊢[PRAAx] realOrder C C u w := by
    have bound : Γ ⊢[PRAAx] le ((a*B)*j) ((B*B)*(b*j)) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (B*j) hs.andE₂.andE₂)
    exact fraction_order (a*B) (b*j) (B*B) j (positive_product _ _ hb hj) hj bound
  exact .andI (GaussianEulerPowerChartTimeOrder.order_trans C C R qzero l s low hL)
    (GaussianEulerPowerChartTimeOrder.order_trans R C C s u w hU high)

theorem width_bounds (a b B j : PTm n) (hs : Γ ⊢[PRAAx] source a b B) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] realOrder constantF widthF qzero (widthData a b B j) ⋏
      realOrder widthF constantF (widthData a b B j) (fraction (B*B) j) := by
  have e := width_identity a b B j hs.andE₁ hj
  have bds := ratio_bounds a b B j hs hj
  exact .andI (transport _ _ _ _ _ _ _ _ (cross_refl _ _ (constant_regular qzero)) (cross_symm _ _ _ _ e) bds.andE₁)
    (transport _ _ _ _ _ _ _ _ e (cross_refl _ _ (constant_regular _)) bds.andE₂)

def cutoff (B p : PTm n) : PTm n := (B*B)*unit (p+two)

ipra_subst cutoff [two, one]

theorem cutoff_positive (B p : PTm n) (h : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] le one (cutoff B p) :=
  positive_product _ _ (positive_product _ _ h h) (unit_positive (p+two))

theorem width_at_cutoff (a b B j p : PTm n) (hs : Γ ⊢[PRAAx] source a b B) (hj : Γ ⊢[PRAAx] le (cutoff B p) j) :
    Γ ⊢[PRAAx] realOrder widthF constantF (widthData a b B j) (fraction one (unit (p+two))) := by
  let C := constantF
  let u := fraction (B*B) j
  let v := fraction one (unit (p+two))
  have jpos := le_trans (cutoff_positive B p hs.andE₂.andE₁) hj
  have e : Γ ⊢[PRAAx] le ((B*B)*unit (p+two)) (one*j) := le_congr (.eqRefl _) (one_mul j).eqSymm hj
  exact GaussianEulerPowerChartTimeOrder.order_trans widthF C C (widthData a b B j) u v
    (width_bounds a b B j hs jpos).andE₂ (fraction_order (B*B) j one (unit (p+two)) jpos (unit_positive _) e)

theorem actual_literal_Bohr_Mollerup_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ le one (var 3) ⟶
      realOrder constantF widthF qzero (widthData (var 0) (var 1) (var 2) (var 3)) ⋏
      realOrder widthF constantF (widthData (var 0) (var 1) (var 2) (var 3)) (fraction (var 2*var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (width_bounds _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_literal_Bohr_Mollerup_dyadic_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) ⟶ le (cutoff (var 2) (var 4)) (var 3) ⟶
      realOrder widthF constantF (widthData (var 0) (var 1) (var 2) (var 3)) (fraction one (unit (var 4+two)))) :=
  closeUniv 5 (.impI (.impI (width_at_cutoff _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketWidth
