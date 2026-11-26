import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftExactCofinalRate
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftRationalWindow
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftRelativeRate

/-!
# Exact original Gamma-ratio bounds for rational shift windows

For the positive base a/b, the rational shift window is A=L/b and
both endpoints c/b and d/b stay in it. The normalized Gamma quotient
has logarithmic radius 4A(A+1)/(a/b), with no enlargement of A.
When this radius is at most one, the relative error is at most
twice the logarithmic radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRationalRate

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftBinding (quotientLogF quotientLogData quotientF quotientData quotient_log_regular)
open GaussianGammaDigammaTwoShiftCofinalRate
  (rawSample raw_positive_coefficient raw_data_congr raw_bounds_from_ordered)
open GaussianGammaDigammaTwoShiftExactCofinalRate (finiteRate logRate cofinal_rate)
open GaussianGammaDigammaTwoShiftExponentialCaps (lower upperPoint constant_caps)
open GaussianGammaDigammaTwoShiftWindow (low width)
open GaussianGammaDigammaTwoShiftRationalWindow
  (input coefficient cost low_split high_split forward_raw positive_endpoint)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero positive_product ofGaussian_canonical)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingNames (constant_real fraction_axis)
open RationalGaussianEmbedding (axis_negative)
open RationalValueBounds (upper upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def budget (b c d : PTm n) : PTm n := cost b c d+cost b d c

ipra_subst budget

private theorem forward (p a b c d L : PTm n) (hs : Γ ⊢[PRAAx] input a b c d L)
    (h : Γ ⊢[PRAAx] lt d c) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (rawSample p a b c d)) (coefficient b L*unit p+cost b c d*(a*b)) ((a*b)*unit p) ⋏
       upper (fstT (rawSample p a b c d)) (fstT qzero) (coefficient b L*unit p+cost b c d*(a*b)) ((a*b)*unit p)) := by
  have hb := hs.andE₁.andE₂
  have hbase := hs.andE₂.andE₂.andE₁
  have hd := hs.andE₂.andE₂.andE₂.andE₂
  have ec := high_split a b L c d hbase hd (le_of_lt h)
  have ed := low_split a b L d hbase hd
  have e := (raw_positive_coefficient p a (low b d) b (width c d) hb).eqSymm.eqTrans (raw_data_congr p a b _ _ c d ec ed)
  have rate := forward_raw p a b c d L hs h
  exact .andI (upper_congr (.eqRefl _) (congrFst e) (.eqRefl _) (.eqRefl _) rate.andE₁)
    (upper_congr (congrFst e) (.eqRefl _) (.eqRefl _) (.eqRefl _) rate.andE₂)

private theorem row (p a b c d L : PTm n) (hs : Γ ⊢[PRAAx] input a b c d L) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (rawSample p a b c d)) (coefficient b L*unit p+budget b c d*(a*b)) ((a*b)*unit p) ⋏
       upper (fstT (rawSample p a b c d)) (fstT qzero) (coefficient b L*unit p+budget b c d*(a*b)) ((a*b)*unit p)) := by
  have swapped : Γ ⊢[PRAAx] input a b d c L := .andI hs.andE₁
    (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₁
      (.andI hs.andE₂.andE₂.andE₂.andE₂ hs.andE₂.andE₂.andE₂.andE₁)))
  exact raw_bounds_from_ordered p a b c d (coefficient b L*unit p) (a*b)
    (cost b c d) (cost b d c) (positive_product _ _ hs.andE₁.andE₁ hs.andE₁.andE₂)
    (.impI (forward p a b c d L hs.wk Prf.hyp0))
    (.impI (forward p a b d c L swapped.wk Prf.hyp0))

theorem two_shift_log_rate (a b c d L : PTm n) (hs : Γ ⊢[PRAAx] input a b c d L) :
    Γ ⊢[PRAAx] logRate a b c d (coefficient b L) (a*b) := by
  have sb := hs.andE₁.andE₂
  have ha := hs.andE₁
  have H := hs.andE₂.andE₂.andE₁
  have hc := positive_endpoint a b L c sb H hs.andE₂.andE₂.andE₂.andE₁
  have hd := positive_endpoint a b L d sb H hs.andE₂.andE₂.andE₂.andE₂
  apply cofinal_rate a b c d (coefficient b L) (a*b) (budget b c d) ha hc hd
    (positive_product _ _ ha.andE₁ ha.andE₂)
  have hx : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift L) :=
    by simpa only [Fm.shift,GaussianGammaDigammaTwoShiftRationalWindow.subst_input,Syn.shift] using hs.shift
  refine .allI ?_
  simpa only [finiteRate,GaussianGammaDigammaTwoShiftCofinalRate.finiteRateWithDenominator,Syn.shift,GaussianGammaDigammaTwoShiftRationalWindow.subst_coefficient,PTm.subst_mul,subst_budget] using
    row (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift L) hx

theorem actual_original_Gamma_rational_window_logarithmic_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        logRate (var 0) (var 1) (var 2) (var 3) (coefficient (var 1) (var 4)) (var 0*var 1)) :=
  closeUniv 5 (.impI (two_shift_log_rate _ _ _ _ _ Prf.hyp0))

def relativeRate (a b c d L : PTm n) : Fm PTm n :=
  realOrder constantF quotientF (lower (coefficient b L) (a*b)) (quotientData a b c d) ⋏
  realOrder quotientF constantF (quotientData a b c d) (upperPoint (coefficient b L) (a*b))

theorem two_shift_relative_rate (a b c d L : PTm n) (hs : Γ ⊢[PRAAx] input a b c d L)
    (hSize : Γ ⊢[PRAAx] le (coefficient b L) (a*b)) : Γ ⊢[PRAAx] relativeRate a b c d L := by
  let K := coefficient b L
  let q := fraction K (a*b)
  let v := qnegative q
  let x := quotientLogData a b c d
  have ha := hs.andE₁
  have hB := hs.andE₁.andE₂
  have hDden := positive_product _ _ hs.andE₁.andE₁ hB
  have base := hs.andE₂.andE₂.andE₁
  have hc := positive_endpoint a b L c hB base hs.andE₂.andE₂.andE₂.andE₁
  have hD := positive_endpoint a b L d hB base hs.andE₂.andE₂.andE₂.andE₂
  have hq := constant_real q (ofGaussian_canonical _ _ hDden) (fraction_axis K (a*b) hDden)
  have hv := constant_real v (qnegative_canonical _) (axis_negative _ (fraction_axis K (a*b) hDden))
  have hx := quotient_log_regular a b c d ha hc hD
  have hr := GaussianGammaDigammaTwoShiftRelativeRate.quotient_log_real a b c d hB
  have localLog := two_shift_log_rate a b c d L hs
  have lo := GaussianStirlingMultiplicativeBoundsOrder.exponential_order constantF quotientLogF v x
    (constant_regular _) hx hv hr localLog.andE₁
  have hi := GaussianStirlingMultiplicativeBoundsOrder.exponential_order quotientLogF constantF x q
    hx (constant_regular _) hr hq localLog.andE₂
  have caps := constant_caps K (a*b) hDden hSize
  exact .andI
    (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ caps.andE₁ lo)
    (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ hi caps.andE₂)

theorem actual_original_Gamma_rational_window_relative_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        le (coefficient (var 1) (var 4)) (var 0*var 1) ⟶
        relativeRate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (two_shift_relative_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRationalRate
