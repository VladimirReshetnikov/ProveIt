import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicFixedCutoff
import IPRADerivations.Analysis.Euler.GaussianEulerDerivativeParameterPath
import IPRADerivations.Analysis.Euler.GaussianEulerDerivativeSubdivisionBudget

/-!
# One original compact interval for two orders along a parameter path

The requested truncation precisions r and s are independent. A numerical
index shift makes the original order-j and order-(j+1) full cutoffs have
literally equal height, eta denominator, upper endpoint and width. The
same physical interval works at every certified point of the actual
native parameter path, with its proved radius R+1 and margin 1/(2A).
The original improper-to-compact estimates retain their independent
observation queries. The last helper pays two endpoint tails relative
to the actual nonzero whole parameter h/D.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeCommonInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen top tailCoefficient)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerLogarithmicCommonCutoff (cutoff lowerIndex)
open GaussianEulerDerivativeParameterPath (numerator denominator)
open GaussianEulerLogarithmicIntervalName (data)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "C" => GaussianEulerLogarithmicIntervalName.nameF

abbrev source (z R B A h D : PTm n) : Fm PTm n := GaussianEulerDerivativeParameterPath.source z R B A h D
def nextIndex (r s j A : PTm n) : PTm n := cutoff r j (two*A)+cutoff s (succ j) (two*A)
def baseIndex (r s j R A : PTm n) : PTm n := lowerIndex (nextIndex r s j A) (R+one+j) one
def intervalDen (r s j R A : PTm n) : PTm n := etaDen (nextIndex r s j A) (two*(two*A)) (R+one+succ j)
def intervalTop (r s j R A : PTm n) : PTm n := top (nextIndex r s j A) (two*(two*A)) (R+one+succ j)
def intervalWidth (r s j R A : PTm n) : PTm n := width (nextIndex r s j A) (two*(two*A)) (R+one+succ j)
def compactData (r s j m z R B A h D N i : PTm n) : PTm n :=
  data m (numerator z B h D N i) (R+one) (denominator B D N) one
    (intervalWidth r s j R A) (intervalDen r s j R A) (intervalTop r s j R A)
def improperData (m z R B A h D N i : PTm n) : PTm n :=
  GaussianEulerLogarithmicImproperName.data m (numerator z B h D N i) (R+one) (denominator B D N) (two*A)
def endpointQuery (p D : PTm n) : PTm n := GaussianFastValueCut.exponent (num 4*D) (p+num 6)

@[simp] theorem subst_nextIndex {m : ℕ} (σ : Fin n → PTm m) (r s j A : PTm n) :
    Syn.subst σ (nextIndex r s j A) = nextIndex (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ A) := by simp [nextIndex]
@[simp] theorem subst_baseIndex {m : ℕ} (σ : Fin n → PTm m) (r s j R A : PTm n) :
    Syn.subst σ (baseIndex r s j R A) = baseIndex (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) := by simp [baseIndex]
@[simp] theorem subst_intervalDen {m : ℕ} (σ : Fin n → PTm m) (r s j R A : PTm n) :
    Syn.subst σ (intervalDen r s j R A) = intervalDen (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) := by
  simp [intervalDen,etaDen,height,tailCoefficient]
@[simp] theorem subst_intervalTop {m : ℕ} (σ : Fin n → PTm m) (r s j R A : PTm n) :
    Syn.subst σ (intervalTop r s j R A) = intervalTop (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) := by
  simp [intervalTop,top,height,tailCoefficient]
@[simp] theorem subst_intervalWidth {m : ℕ} (σ : Fin n → PTm m) (r s j R A : PTm n) :
    Syn.subst σ (intervalWidth r s j R A) = intervalWidth (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ A) := by simp [intervalWidth]
@[simp] theorem subst_compactData {m : ℕ} (σ : Fin n → PTm m) (r s j k z R B A h D N i : PTm n) :
    Syn.subst σ (compactData r s j k z R B A h D N i) = compactData (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ j)
      (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) := by simp [compactData]
@[simp] theorem subst_improperData {m : ℕ} (σ : Fin n → PTm m) (k z R B A h D N i : PTm n) :
    Syn.subst σ (improperData k z R B A h D N i) = improperData (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) := by simp [improperData]
@[simp] theorem subst_endpointQuery {m : ℕ} (σ : Fin n → PTm m) (p D : PTm n) :
    Syn.subst σ (endpointQuery p D) = endpointQuery (Syn.subst σ p) (Syn.subst σ D) := by simp [endpointQuery]

theorem base_late (r s j R A : PTm n) : Γ ⊢[PRAAx] le (cutoff r j (two*A)) (baseIndex r s j R A) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

theorem next_late (r s j A : PTm n) : Γ ⊢[PRAAx] le (cutoff s (succ j) (two*A)) (nextIndex r s j A) := le_add_left _ _

theorem same_height (r s j R A : PTm n) : Γ ⊢[PRAAx]
    height (baseIndex r s j R A) (two*(two*A)) (R+one+j) ≐
      height (nextIndex r s j A) (two*(two*A)) (R+one+succ j) := by
  have degree : Γ ⊢[PRAAx] (R+one+j)+one ≐ R+one+succ j := by ipra_ring
  have moved : Γ ⊢[PRAAx]
      height (nextIndex r s j A) (two*(two*A)) ((R+one+j)+one) ≐
        height (nextIndex r s j A) (two*(two*A)) (R+one+succ j) := by
    simpa [height,tailCoefficient] using Prf.eqCongr1
      (height (Syn.shift (nextIndex r s j A)) (Syn.shift (two*(two*A))) (var 0)) degree
  exact (GaussianEulerLogarithmicCommonCutoff.height_shift (nextIndex r s j A) (two*A) (R+one+j) one).eqTrans moved

theorem same_denominator (r s j R A : PTm n) : Γ ⊢[PRAAx]
    etaDen (baseIndex r s j R A) (two*(two*A)) (R+one+j) ≐ intervalDen r s j R A :=
  congrAp2 powF (congrMul (.eqRefl _) (same_height r s j R A)) (.eqRefl two)

theorem same_top (r s j R A : PTm n) : Γ ⊢[PRAAx]
    top (baseIndex r s j R A) (two*(two*A)) (R+one+j) ≐ intervalTop r s j R A :=
  congrMul (.eqRefl two) (same_height r s j R A)

theorem same_width (r s j R A : PTm n) : Γ ⊢[PRAAx]
    width (baseIndex r s j R A) (two*(two*A)) (R+one+j) ≐ intervalWidth r s j R A :=
  congrMonus (congrMul (same_denominator r s j R A) (same_top r s j R A)) (.eqRefl one)

theorem base_data (r s j z R B A h D N i : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicCutoffSplit.fullData j (numerator z B h D N i) (R+one) (denominator B D N) (two*A) (baseIndex r s j R A) ≐
      compactData r s j j z R B A h D N i :=
  GaussianEulerLogarithmicCutoffSplit.interval_data_congr _ _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _)
    (same_width r s j R A) (same_denominator r s j R A) (same_top r s j R A)

theorem next_data (r s j z R B A h D N i : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicCutoffSplit.fullData (succ j) (numerator z B h D N i) (R+one) (denominator B D N) (two*A) (nextIndex r s j A) ≐
      compactData r s j (succ j) z R B A h D N i := .eqRefl _

theorem path_source (z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source (numerator z B h D N i) (R+one) (denominator B D N) (two*A) :=
  GaussianEulerDerivativeParameterPath.path_source z R B A h D N i hs hN hi

theorem interval_source (r s j z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource (numerator z B h D N i) (R+one) (denominator B D N) one
      (intervalWidth r s j R A) (intervalDen r s j R A) (intervalTop r s j R A) :=
  GaussianEulerLogarithmicCutoffSplit.full_source (succ j) _ _ _ _ (nextIndex r s j A)
    (path_source z R B A h D N i hs hN hi).andE₂.andE₁

private theorem rate_data_congr (F G : PR 2) (x y y' K V : PTm n) (he : Γ ⊢[PRAAx] y ≐ y')
    (hr : Γ ⊢[PRAAx] independentRate F G x y K V) : Γ ⊢[PRAAx] independentRate F G x y' K V := by
  simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 (independentRate F G (Syn.shift x) (var 0) (Syn.shift K) (Syn.shift V)) he
      (by simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hr)

theorem base_rate (r s j z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    independentRate I C (improperData j z R B A h D N i) (compactData r s j j z R B A h D N i) two (unit (r+num 6)) :=
  rate_data_congr I C _ _ _ _ _ (base_data r s j z R B A h D N i)
    (GaussianEulerLogarithmicFixedCutoff.original_fixed_cutoff_rate r j _ _ _ _ (baseIndex r s j R A)
      (path_source z R B A h D N i hs hN hi) (base_late r s j R A))

theorem next_rate (r s j z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    independentRate I C (improperData (succ j) z R B A h D N i) (compactData r s j (succ j) z R B A h D N i) two (unit (s+num 6)) :=
  GaussianEulerLogarithmicFixedCutoff.original_fixed_cutoff_rate s (succ j) _ _ _ _ (nextIndex r s j A)
    (path_source z R B A h D N i hs hN hi) (next_late r s j A)

theorem base_observations (p q r s j z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I p (improperData j z R B A h D N i)) (ap2 C q (compactData r s j j z R B A h D N i))
      (rateNumerator two (unit (r+num 6)) p q) (rateDenominator (unit (r+num 6)) p q) :=
  GaussianNamedInverseRate.rate_at I C _ _ _ _ p q (base_rate r s j z R B A h D N i hs hN hi)

theorem next_observations (p q r s j z R B A h D N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I p (improperData (succ j) z R B A h D N i)) (ap2 C q (compactData r s j (succ j) z R B A h D N i))
      (rateNumerator two (unit (s+num 6)) p q) (rateDenominator (unit (s+num 6)) p q) :=
  GaussianNamedInverseRate.rate_at I C _ _ _ _ p q (next_rate r s j z R B A h D N i hs hN hi)

theorem whole_inverse_bound (z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hz : Γ ⊢[PRAAx] le one (ComplexLogarithmRemainder.normSq h)) : Γ ⊢[PRAAx]
    bounded (GaussianRationalReciprocal.reciprocal (ofGaussian h D)) D one :=
  GaussianEulerDerivativeSubdivisionBudget.parameter_inverse_bound h D (.andI hs.andE₂.andE₁ hz)

theorem endpoint_query_budget (p D r : PTm n) (hr : Γ ⊢[PRAAx] le (endpointQuery p D) r) : Γ ⊢[PRAAx]
    le ((num 4*D)*unit (p+num 6)) (unit (r+num 6)) :=
  le_trans (GaussianFastValueCut.query_budget (num 4*D) (p+num 6))
    (GaussianExponentialReference.unit_monotone (le_trans hr (le_add_right _ _)))

theorem normalized_endpoint_tails (q p r z R B A h D : PTm n) (hs : Γ ⊢[PRAAx] source z R B A h D)
    (hz : Γ ⊢[PRAAx] le one (ComplexLogarithmRemainder.normSq h))
    (hr : Γ ⊢[PRAAx] le (endpointQuery p D) r) (hq : Γ ⊢[PRAAx] bounded q (num 4) (unit (r+num 6))) : Γ ⊢[PRAAx]
    bounded (GaussianRationalHorner.qmul q (GaussianRationalReciprocal.reciprocal (ofGaussian h D))) one (unit (p+num 6)) := by
  have budget : Γ ⊢[PRAAx] le (num 4*(D*unit (p+num 6))) (one*unit (r+num 6)) :=
    le_congr (by ipra_ring) (by ipra_ring) (endpoint_query_budget p D r hr)
  exact GaussianEulerDerivativeSubdivisionBudget.normalize_error q h p D (.andI hs.andE₂.andE₁ hz)
    (GaussianCoefficientNameBounds.bounded_radius_mono q (num 4) (unit (r+num 6)) one (D*unit (p+num 6)) (unit_positive _)
      (positive_product _ _ hs.andE₂.andE₁ (unit_positive _))
      budget hq)

theorem actual_original_derivative_common_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((etaDen (baseIndex (var 0) (var 1) (var 2) (var 3) (var 4)) (two*(two*var 4)) (var 3+one+var 2) ≐
        intervalDen (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (top (baseIndex (var 0) (var 1) (var 2) (var 3) (var 4)) (two*(two*var 4)) (var 3+one+var 2) ≐
        intervalTop (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.andI (same_denominator _ _ _ _ _) (same_top _ _ _ _ _))

theorem actual_original_derivative_common_interval_rates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ (le one (var 9) ⋏ le (var 10) (var 9))) ⟶
      (independentRate I C (improperData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
        (compactData (var 0) (var 1) (var 2) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) two (unit (var 0+num 6)) ⋏
       independentRate I C (improperData (succ (var 2)) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
        (compactData (var 0) (var 1) (var 2) (succ (var 2)) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) two (unit (var 1+num 6)))) :=
  closeUniv 11 (.impI (.andI (base_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (next_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

theorem actual_nonzero_whole_parameter_endpoint_tail_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
      (le one (ComplexLogarithmRemainder.normSq (var 7)) ⋏
       (le (endpointQuery (var 1) (var 8)) (var 2) ⋏ bounded (var 0) (num 4) (unit (var 2+num 6))))) ⟶
      bounded (GaussianRationalHorner.qmul (var 0) (GaussianRationalReciprocal.reciprocal (ofGaussian (var 7) (var 8))))
        one (unit (var 1+num 6))) :=
  closeUniv 9 (.impI (normalized_endpoint_tails _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeCommonInterval
