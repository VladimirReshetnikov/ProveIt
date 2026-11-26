import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartRationalPowers
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.CommonLemmas

/-!
# Explicit cofinal endpoints for the original rational power chart

At cutoff V, use the physical panel from 1/(S*V)^f to (h*V)^f.
Its exact image is contained in the positive half-line and contains
the canonical cutoff panel from 1/V to V.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartCofinalEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (parameters)
open GaussianEulerPowerChartRationalPowers (original_chart_value chart_proper)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (e f d h Q S V : PTm n) : Fm PTm n :=
  parameters e f d h Q S ⋏ le two V

def lowerDenominator (S V m : PTm n) : PTm n := pw (S*V) m
def upperNumerator (h V m : PTm n) : PTm n := pw (h*V) m
def width (f h S V : PTm n) : PTm n :=
  monus (upperNumerator h V f*lowerDenominator S V f) one

def physicalPanel (f h S V : PTm n) : Fm PTm n :=
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  le one E ⋏ (le one T ⋏ (le one (width f h S V) ⋏ (one+width f h S V ≐ T*E)))

def imageGuards (e d h S V : PTm n) : Fm PTm n :=
  let E := lowerDenominator S V e
  let T := upperNumerator h V e
  le one (h*E) ⋏ (le (d*V) (h*E) ⋏ le (h*V) (d*T))

def identifiesEndpoints (e f d h S V : PTm n) : Fm PTm n :=
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let F := GaussianEulerPositivePowerChart.nameF
  let x := GaussianEulerPositivePowerChart.data e f d h S one E
  let y := GaussianEulerPositivePowerChart.data e f d h S T one
  crossEquivalent F constantF x (fraction d (h*lowerDenominator S V e)) ⋏
    crossEquivalent F constantF y (fraction (d*upperNumerator h V e) h)

private theorem bounded_below_by_base (b m : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le b (pw b m) :=
  le_congr (pw_one b) (.eqRefl _) (GaussianFactorBudget.power_monotone_length b one m hb hm)

private theorem one_le_two : Γ ⊢[PRAAx] le one two :=
  le_of_eq_add (d := one) (by ipra_ring)

private alias right_one := Common.mul_one_right

private theorem powered_bounds (a V m : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hV : Γ ⊢[PRAAx] le two V) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le two (pw (a*V) m) := by
  have base : Γ ⊢[PRAAx] le V (a*V) :=
    le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V ha)
  have start := le_trans hV base
  exact le_trans start (bounded_below_by_base (a*V) m (le_trans one_le_two start) hm)

theorem physical_panel (e f d h Q S V : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S V) : Γ ⊢[PRAAx] physicalPanel f h S V := by
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  have hf := hs.andE₁.andE₁.andE₂
  have low : Γ ⊢[PRAAx] le two E := powered_bounds S V f hs.andE₁.andE₂.andE₂.andE₁.andE₂ hs.andE₂ hf
  have high : Γ ⊢[PRAAx] le one T :=
    le_trans one_le_two (powered_bounds h V f hs.andE₁.andE₂.andE₁.andE₂ hs.andE₂ hf)
  have product : Γ ⊢[PRAAx] le two (T*E) :=
    le_congr (one_mul two) (.eqRefl _) (le_mul_mono high low)
  have widthPos : Γ ⊢[PRAAx] le one (width f h S V) := by
    have eq := eq_add_of_le product
    have normalized : Γ ⊢[PRAAx] T*E ≐ (one+monus (T*E) two)+one :=
      eq.eqTrans (by ipra_ring)
    have subtract : Γ ⊢[PRAAx] monus (T*E) one ≐ monus ((one+monus (T*E) two)+one) (zero+one) :=
      congrMonus normalized (zero_add one).eqSymm
    have reduced := subtract.eqTrans ((monus_add_add (one+monus (T*E) two) zero one).eqTrans
      (monus_zero (one+monus (T*E) two)))
    exact le_congr (.eqRefl _) reduced.eqSymm (le_add_right one (monus (T*E) two))
  exact .andI (le_trans one_le_two low) (.andI high
    (.andI widthPos (eq_add_of_le (le_trans one_le_two product)).eqSymm))

theorem image_guards (e f d h Q S V : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S V) : Γ ⊢[PRAAx] imageGuards e d h S V := by
  let E := lowerDenominator S V e
  let T := upperNumerator h V e
  have hp := hs.andE₁
  have he := hp.andE₁.andE₁
  have hd := hp.andE₂.andE₁.andE₁
  have hh := hp.andE₂.andE₁.andE₂
  have hS := hp.andE₂.andE₂.andE₁.andE₂
  have hV := le_trans one_le_two hs.andE₂
  have hlBase := positive_product S V hS hV
  have hrBase := positive_product h V hh hV
  have hl : Γ ⊢[PRAAx] le (S*V) E := bounded_below_by_base _ _ hlBase he
  have hr : Γ ⊢[PRAAx] le (h*V) T := bounded_below_by_base _ _ hrBase he
  have lhs : Γ ⊢[PRAAx] le (d*V) (h*(S*V)) :=
    le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] S*h*V ≐ h*(S*V))
      (mul_le_mul_right V hp.andE₂.andE₂.andE₂.andE₂)
  have rhs : Γ ⊢[PRAAx] le (h*(S*V)) (h*E) :=
    le_mul_mono (le_refl h) hl
  have left : Γ ⊢[PRAAx] le (d*V) (h*E) :=
    le_trans lhs rhs
  have right : Γ ⊢[PRAAx] le (h*V) (d*T) :=
    le_trans hr (le_congr (one_mul T) (.eqRefl _) (mul_le_mul_right T hd))
  exact .andI (positive_product h E hh (le_trans hlBase hl)) (.andI left right)

private theorem above_one_from_two {a : PTm n} (h : Γ ⊢[PRAAx] le two a) :
    Γ ⊢[PRAAx] le one a := le_trans one_le_two h

theorem exact_endpoints (e f d h Q S V : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S V) : Γ ⊢[PRAAx] identifiesEndpoints e f d h S V := by
  let E := lowerDenominator S V f
  let T := upperNumerator h V f
  let F := GaussianEulerPositivePowerChart.nameF
  let chart := GaussianEulerPositivePowerChart.data e f d h S
  let L := pw one f
  let L₁ := pw one e
  have hE : Γ ⊢[PRAAx] le one E := (physical_panel e f d h Q S V hs).andE₁
  have hT : Γ ⊢[PRAAx] le one T := (physical_panel e f d h Q S V hs).andE₂.andE₁
  have hV := above_one_from_two hs.andE₂
  have hS := hs.andE₁.andE₂.andE₂.andE₁.andE₂
  have hh := hs.andE₁.andE₂.andE₁.andE₂
  have EL : Γ ⊢[PRAAx] L ≐ one := pw_one_base f
  have EL₁ : Γ ⊢[PRAAx] L₁ ≐ one := pw_one_base e
  have hL : Γ ⊢[PRAAx] le one L := le_congr (.eqRefl _) EL.eqSymm (le_refl one)
  have hTl : Γ ⊢[PRAAx] le L (T*E) :=
    le_congr EL.eqSymm (.eqRefl _) (positive_product T E hT hE)
  have left : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T L E :=
    .andI hs.andE₁ (.andI hE (.andI (.andI hL hE)
      (.andI (le_congr (right_one E) (.eqRefl _) (le_mul_mono (le_refl E) hL)) hTl)))
  have right : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T T L :=
    .andI hs.andE₁ (.andI hE (.andI (.andI hT hL)
      (.andI (le_congr EL.eqSymm (.eqRefl _) (positive_product E T hE hT))
        (le_congr (right_one T) (.eqRefl _) (le_mul_mono (le_refl T) hL)))))
  have rawLeft := original_chart_value e f d h Q S E T one (S*V)
    (.andI (le_refl one) (positive_product S V hS hV)) left
  have rawRight := original_chart_value e f d h Q S E T (h*V) one
    (.andI (positive_product h V hh hV) (le_refl one)) right
  have pLeft := chart_proper e f d h Q S one E L E hs.andE₁ (.andI (le_refl _) hE) (.andI hL hE)
    ((mul_comm one E).eqTrans (congrMul (.eqRefl E) EL.eqSymm))
  have pRight := chart_proper e f d h Q S T one T L hs.andE₁ (.andI hT (le_refl _)) (.andI hT hL)
    ((congrMul (.eqRefl T) EL).eqTrans (mul_comm T one))
  have rLeft := GaussianEulerPositivePowerChartJacobian.fraction_congr
    ((congrMul (.eqRefl d) EL₁).eqTrans (right_one d)) (.eqRefl (h*lowerDenominator S V e))
  have rRight := GaussianEulerPositivePowerChartJacobian.fraction_congr
    (.eqRefl (d*upperNumerator h V e)) ((congrMul (.eqRefl h) EL₁).eqTrans (right_one h))
  have leftValue := cross_trans F F constantF (chart one E) (chart L E) _ pLeft rawLeft
  have rightValue := cross_trans F F constantF (chart T one) (chart T L) _ pRight rawRight
  exact .andI
    (GaussianGammaCompactCutoffAlignment.cross_data_congr F constantF _ _ _ _ (.eqRefl _) rLeft leftValue)
    (GaussianGammaCompactCutoffAlignment.cross_data_congr F constantF _ _ _ _ (.eqRefl _) rRight rightValue)

theorem actual_power_chart_cofinal_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      (physicalPanel (var 1) (var 3) (var 5) (var 6) ⋏
        (imageGuards (var 0) (var 2) (var 3) (var 5) (var 6) ⋏
          identifiesEndpoints (var 0) (var 1) (var 2) (var 3) (var 5) (var 6)))) :=
  closeUniv 7 (.impI (.andI (physical_panel _ _ _ _ _ _ _ Prf.hyp0)
    (.andI (image_guards _ _ _ _ _ _ _ Prf.hyp0) (exact_endpoints _ _ _ _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartCofinalEndpoints
