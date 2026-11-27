import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.EndpointControl.GaussianGammaNegativeCriticalEndpoints
import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaMonotone
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescale
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderLinear

/-!
# Original positive digamma on the shifted unit interval

The original Euler-constant observations lie in [0,1]. The digamma
value at one equals its negative, and recurrence gives the value
at two. The verified native digamma order propagates the resulting
bounds −1 and 1 to every rational argument in [1,2].
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalPositiveWindow

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular gamma_regular gamma_sample_at)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaDigammaRescale (integer_rescale datum_congr)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (negative_order negative_constant)
open GaussianNamedRealOrderTransport (transport)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero ofGaussian_canonical)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open RationalArgmin (rationalLE rationalLE_congr transitive eq_le)
open RationalValueBounds (upper_of_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "GF" => GaussianGammaCanonicalExponent.gammaF
local notation "NG" => GaussianGammaDerivativeAtOne.negativeGammaF
local notation "ng" => GaussianGammaDerivativeAtOne.negativeGammaData
local notation "CF" => constantF

def positiveOne : PTm n := fraction one one
def negativeOne : PTm n := qsub qzero positiveOne

@[simp] theorem subst_positiveOne {k : ℕ} (σ : Fin n → PTm k) :
    Syn.subst σ (positiveOne : PTm n) = (positiveOne : PTm k) :=
  by simp [positiveOne]
@[simp] theorem subst_negativeOne {k : ℕ} (σ : Fin n → PTm k) :
    Syn.subst σ (negativeOne : PTm n) = (negativeOne : PTm k) :=
  by simp [negativeOne]

theorem gamma_sample_range (p : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT qzero) (fstT (ap2 GF p zero)) ⋏
      rationalLE (fstT (ap2 GF p zero)) (fstT positiveOne) := by
  let g := GammaEulerConstantName.gammaSample p zero
  have h := GammaEulerConstantName.gamma_sample_range (Γ := Γ) p zero
  have e : Γ ⊢[PRAAx] fstT (ap2 GF p zero) ≐ RationalArithmetic.recode g :=
    (congrFst (gamma_sample_at p)).eqTrans (fst_pair _ _)
  have eq := RationalArithmetic.recode_equal (Γ := Γ) g
  have z : Γ ⊢[PRAAx] fstT (qzero : PTm n) ≐ GaussianRationalSyntheticBounds.natCode zero :=
    (congrFst (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one))).eqSymm.eqTrans
      (fraction_real_part zero one (le_refl one))
  have o : Γ ⊢[PRAAx] fstT (positiveOne : PTm n) ≐ GaussianRationalSyntheticBounds.natCode one :=
    fraction_real_part one one (le_refl one)
  exact .andI (rationalLE_congr z.eqSymm e.eqSymm (transitive h.andE₁ (eq_le eq.eqSymm)))
    (rationalLE_congr e.eqSymm o.eqSymm (transitive (eq_le eq) h.andE₂))

theorem gamma_bounds : Γ ⊢[PRAAx] realOrder CF GF qzero zero ⋏ realOrder GF CF zero positiveOne := by
  refine .andI (.allI (.allI ?_)) (.allI (.allI ?_))
  · simp only [Syn.shift,GaussianRationalHorner.subst_qzero,ConciseIPRA.PTm.subst_zero]
    exact upper_of_order _ _ _ _ (rationalLE_congr (congrFst (constant_at (var 1) qzero)).eqSymm
      (.eqRefl _) (gamma_sample_range (var 0)).andE₁)
  · simp only [Syn.shift,subst_positiveOne,ConciseIPRA.PTm.subst_zero]
    exact upper_of_order _ _ _ _ (rationalLE_congr (.eqRefl _)
      (congrFst (constant_at (var 0) positiveOne)).eqSymm (gamma_sample_range (var 1)).andE₂)

theorem one_lower : Γ ⊢[PRAAx] realOrder CF DF negativeOne (dd one one) := by
  let c : PTm n := positiveOne
  have h := negative_order (Γ := Γ) GF CF zero c gamma_regular (constant_regular c) gamma_bounds.andE₂
  exact transport CF (GaussianNameRingLaws.negativeF CF) NG DF negativeOne
    (GaussianNameRingLaws.negativeData c) ng (dd one one) (cross_symm _ _ _ _ (negative_constant c))
    (cross_symm _ _ _ _ (GaussianGammaDigammaNative.digamma_one (Γ := Γ))) h

theorem one_upper : Γ ⊢[PRAAx] realOrder DF CF (dd one one) qzero := by
  have h := negative_order (Γ := Γ) CF GF qzero zero (constant_regular qzero) gamma_regular gamma_bounds.andE₁
  have eq : Γ ⊢[PRAAx] qsub (qzero : PTm n) qzero ≐ qzero :=
    GaussianCoefficientNormOrder.qsub_self _
  have right := cross_trans (Γ := Γ) _ _ _ _ _ _ (negative_constant qzero)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ eq)
  exact transport DF NG (GaussianNameRingLaws.negativeF CF) CF (dd one one) ng
    (GaussianNameRingLaws.negativeData qzero) qzero GaussianGammaDigammaNative.digamma_one right h

theorem two_upper : Γ ⊢[PRAAx] realOrder DF CF (dd two one) positiveOne := by
  let c : PTm n := positiveOne
  let d : PTm n := dd one one
  let R := GaussianGammaDigammaRecurrence.nameF
  let r : PTm n := GaussianGammaDigammaRecurrence.data one one
  have h := add_order (Γ := Γ) DF CF CF CF d qzero c c one_upper (order_refl _ _ (constant_regular c))
  have eq : Γ ⊢[PRAAx] dd (one+one) one ≐ dd two one := datum_congr (by ipra_ring) (.eqRefl _)
  have shift : Γ ⊢[PRAAx] crossEquivalent DF R (dd two one) r :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr DF R _ _ _ _ eq (.eqRefl _)
      (GaussianGammaDigammaRecurrence.digamma_shift one one (.andI (le_refl _) (le_refl _)))
  have sum := cross_trans (Γ := Γ) _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross qzero c)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ (qzero_add c (ofGaussian_canonical _ _ (le_refl one))))
  exact transport DF R (addF CF CF) CF (dd two one) r (addData qzero c) c shift sum h

theorem window (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ha : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] realOrder CF DF negativeOne (dd (b+a) b) ⋏ realOrder DF CF (dd (b+a) b) positiveOne := by
  have s : Γ ⊢[PRAAx] source (b+a) b := .andI (le_trans hb (le_add_right _ _)) hb
  have h₁ : Γ ⊢[PRAAx] crossEquivalent DF DF (dd b b) (dd one one) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr DF DF _ _ _ _
      (datum_congr (by ipra_ring) (.eqRefl _)) (.eqRefl _) (integer_rescale one b (le_refl _) hb)
  have h₂ : Γ ⊢[PRAAx] crossEquivalent DF DF (dd (b+b) b) (dd two one) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr DF DF _ _ _ _
      (datum_congr (by ipra_ring) (.eqRefl _)) (.eqRefl _) (integer_rescale two b (by ipra_le 1) hb)
  have lo := transport CF CF DF DF negativeOne negativeOne (dd one one) (dd b b)
    (cross_refl _ _ (constant_regular _)) (cross_symm _ _ _ _ h₁) one_lower
  have hi := transport DF DF CF CF (dd (b+b) b) (dd two one) positiveOne positiveOne
    h₂ (cross_refl _ _ (constant_regular _)) two_upper
  have l := GaussianGammaDigammaMonotone.monotone b (b+a) b (.andI hb hb) s (le_add_right _ _)
  have r := GaussianGammaDigammaMonotone.monotone (b+a) (b+b) b s (.andI (le_trans hb (le_add_right _ _)) hb)
    (add_le_add_left b ha)
  exact .andI (order_trans _ _ _ _ _ _ lo l) (order_trans _ _ _ _ _ _ r hi)

theorem original_shifted_positive_digamma_window_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 1) ⋏ le (var 0) (var 1)) ⟶
      realOrder CF DF negativeOne (dd (var 1+var 0) (var 1)) ⋏
      realOrder DF CF (dd (var 1+var 0) (var 1)) positiveOne) :=
  closeUniv 2 (.impI (window _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalPositiveWindow
