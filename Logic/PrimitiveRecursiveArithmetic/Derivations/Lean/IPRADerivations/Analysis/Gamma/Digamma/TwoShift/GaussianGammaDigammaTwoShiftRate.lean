import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftWindow
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.Rates.GaussianGammaDigammaTwoShiftCofinalRate

/-!
# The logarithmic rate of the original two-shift Gamma quotient

For encoded positive x and rational shifts α, β with absolute values
at most A, derive the named real interval
−4A(A+1)/x ≤ log(Γ(x+α)/(Γ(x+β)x^(α−β))) ≤ 4A(A+1)/x.
The rate and the quotient refer to the same original Gamma instances.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRate

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaDigammaTwoShiftCofinalRate
  (rawSample finiteRate logRate cofinal_rate raw_positive_coefficient raw_data_congr raw_bounds_from_ordered)
open GaussianGammaDigammaTwoShiftWindow (input coefficient low width cost low_split high_split forward_raw positive_endpoint)
open GaussianRationalHorner (qzero)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def budget (b c d A : PTm n) : PTm n := cost b c d A+cost b d c A

ipra_subst budget [cost, low, width, GaussianGammaDigammaTwoShiftFiniteRate.leftError, GaussianGammaDigammaTwoShiftFiniteRate.rightError, GaussianGammaDigammaTwoShiftSecants.leftCost, GaussianGammaDigammaTwoShiftSecants.rightCost, GaussianStirlingGammaFractionalIncrementObservations.weightedCost, GaussianStirlingGammaFractionalIncrementObservations.scaleCost, GaussianNameRingLaws.three, two]

private theorem forward (p a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A)
    (h : Γ ⊢[PRAAx] lt d c) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (rawSample p a b c d)) (coefficient b A*unit p+cost b c d A*a) (a*unit p) ⋏
       upper (fstT (rawSample p a b c d)) (fstT qzero) (coefficient b A*unit p+cost b c d A*a) (a*unit p)) := by
  have hb := hs.andE₁.andE₂
  have hbase := hs.andE₂.andE₂.andE₁
  have hd := hs.andE₂.andE₂.andE₂.andE₂
  have ec := high_split a b A c d hbase hd (le_of_lt h)
  have ed := low_split a b A d hbase hd
  have e := (raw_positive_coefficient p a (low b d) b (width c d) hb).eqSymm.eqTrans (raw_data_congr p a b _ _ c d ec ed)
  have rate := forward_raw p a b c d A hs h
  exact .andI (upper_congr (.eqRefl _) (congrFst e) (.eqRefl _) (.eqRefl _) rate.andE₁)
    (upper_congr (congrFst e) (.eqRefl _) (.eqRefl _) (.eqRefl _) rate.andE₂)

private theorem row (p a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (rawSample p a b c d)) (coefficient b A*unit p+budget b c d A*a) (a*unit p) ⋏
       upper (fstT (rawSample p a b c d)) (fstT qzero) (coefficient b A*unit p+budget b c d A*a) (a*unit p)) := by
  have swapped : Γ ⊢[PRAAx] input a b d c A := .andI hs.andE₁
    (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₁
      (.andI hs.andE₂.andE₂.andE₂.andE₂ hs.andE₂.andE₂.andE₂.andE₁)))
  exact raw_bounds_from_ordered p a b c d (coefficient b A*unit p) a
    (cost b c d A) (cost b d c A) hs.andE₁.andE₁
    (.impI (forward p a b c d A hs.wk Prf.hyp0))
    (.impI (forward p a b d c A swapped.wk Prf.hyp0))

theorem two_shift_log_rate (a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A) :
    Γ ⊢[PRAAx] logRate a b c d (coefficient b A) := by
  have sb := hs.andE₁.andE₂
  have ha := hs.andE₁
  have H := hs.andE₂.andE₂.andE₁
  have hc := positive_endpoint a b A c sb H hs.andE₂.andE₂.andE₂.andE₁
  have hd := positive_endpoint a b A d sb H hs.andE₂.andE₂.andE₂.andE₂
  apply cofinal_rate a b c d (coefficient b A) (budget b c d A) ha hc hd
  have hx : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) :=
    by simpa only [Fm.shift,GaussianGammaDigammaTwoShiftWindow.subst_input,Syn.shift] using hs.shift
  refine .allI ?_
  simpa only [finiteRate,GaussianGammaDigammaTwoShiftCofinalRate.finiteRateWithDenominator,Syn.shift,GaussianGammaDigammaTwoShiftWindow.subst_coefficient,subst_budget] using
    row (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) hx

theorem actual_original_Gamma_two_shift_logarithmic_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        logRate (var 0) (var 1) (var 2) (var 3) (coefficient (var 1) (var 4))) :=
  closeUniv 5 (.impI (two_shift_log_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRate
