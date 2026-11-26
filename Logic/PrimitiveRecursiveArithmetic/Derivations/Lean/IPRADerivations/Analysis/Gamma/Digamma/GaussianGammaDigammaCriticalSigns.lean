import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLogThree
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaElementaryOriginalLog
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaRecurrence
import IPRADerivations.Analysis.Names.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsCaps

/-!
# Strict digamma margins at the integers one and two

The elementary inequalities at three, the explicit brackets for log 3,
and the exact original digamma recurrence separate the two endpoint
values from zero by a quarter.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaCriticalSigns

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaLogThree (logData lower_order upper_order)
open GaussianGammaEulerShift (constant_sum_cross)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedStrictOrderDifference (difference_lt lt_difference sum_sub_right trans_weak weak_trans)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (qadd qzero positive_product ofGaussian_canonical)
open GaussianRationalMetric (qsub qnegative qnegative_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianStirlingRationalTelescopers (fraction_same)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "CF" => constantF

def quarter : PTm n := fraction one (num 4)
def negativeQuarter : PTm n := qsub qzero quarter

@[simp] theorem subst_quarter {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (quarter : PTm n) = (quarter : PTm m) := by simp [quarter]

@[simp] theorem subst_negativeQuarter {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (negativeQuarter : PTm n) = (negativeQuarter : PTm m) := by simp [negativeQuarter]

private theorem native_source (a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] source a one := .andI ha (le_refl one)

private theorem log_source : Γ ⊢[PRAAx] source (one+two : PTm n) one :=
  native_source _ (le_add_right _ _)

private theorem const_id (a : PTm n) : Γ ⊢[PRAAx] crossEquivalent CF CF a a :=
  cross_refl _ _ (constant_regular _)

private theorem fraction_lt (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] lt (d*a) (c*b)) :
    Γ ⊢[PRAAx] strictOrder CF CF (fraction a b) (fraction c d) :=
  .andI (constant_order _ _ (fractions_order a b c d hb hd (le_of_lt h))) (strict_fractions a b c d hb hd h)

private theorem fraction_sum_value (a b c d u v : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hv : Γ ⊢[PRAAx] le one v)
    (e : Γ ⊢[PRAAx] (a*d+c*b)*v ≐ u*(b*d)) :
    Γ ⊢[PRAAx] qadd (fraction a b) (fraction c d) ≐ fraction u v :=
  (GaussianEulerPositivePowerChartCorrectedImage.fraction_sum a b c d hb hd).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ hb hd) hv e)

private theorem sum_as_constant (a b : PTm n) {c : PTm n} (e : Γ ⊢[PRAAx] qadd a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (addF CF CF) CF (addData a b) c :=
  cross_trans _ _ _ _ _ _ (constant_sum_cross a b) (constant_equal_cross _ _ e)

private theorem native_data_congr (a c : PTm n) (e : Γ ⊢[PRAAx] a ≐ c) :
    Γ ⊢[PRAAx] dd a one ≐ dd c one := by
  simpa [GaussianGammaDigammaNative.subst_data] using
    Prf.eqCongr (dd (var 0) one : PTm 1) (σ := ![a]) (σ' := ![c]) (fun j => by fin_cases j; exact e)

private theorem previous (a c : PTm n) (hs : Γ ⊢[PRAAx] source a one)
    (hc : Γ ⊢[PRAAx] source c one) (e : Γ ⊢[PRAAx] a+one ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF DF CF) DF
      (GaussianNamedDifference.data (dd c one) (fraction one a)) (dd a one) := by
  let b := fraction one a
  have ha := GaussianGammaDigammaNative.name_regular a one hs
  have eq := GaussianGammaCompactCutoffAlignment.cross_data_congr DF DF (dd c one) (dd c one)
    (dd c one) (dd (a+one) one) (.eqRefl _) (native_data_congr _ _ e.eqSymm)
    (cross_refl _ _ (GaussianGammaDigammaNative.name_regular c one hc))
  have move := cross_trans _ _ _ _ _ _ eq (GaussianGammaDigammaRecurrence.digamma_shift a one hs)
  have both := GaussianNamedDifferenceQuotientProperness.difference_proper DF (addF DF CF) CF CF
    (dd c one) (addData (dd a one) b) b b (GaussianGammaDigammaNative.name_regular c one hc)
    (GaussianGammaDigammaRecurrence.name_regular a one hs) (constant_regular _) (constant_regular _)
    move (const_id b)
  exact cross_trans _ _ _ _ _ _ both (sum_sub_right DF CF (dd a one) b ha (constant_regular b))

private theorem three_lower :
    Γ ⊢[PRAAx] strictOrder CF DF (fraction (num 3) (num 4) : PTm n) (dd (one+two) one) := by
  let a : PTm n := fraction (num 3) (num 4)
  let b : PTm n := fraction one (one+two)
  have e : Γ ⊢[PRAAx] qadd a b ≐ fraction (num 13) (num 12) :=
    fraction_sum_value _ _ _ _ _ _ (by ipra_le 3) (by ipra_le 2) (by ipra_le 11) (by ipra_ring)
  have sep := fraction_lt (Γ := Γ) (num 13) (num 12) (num 12) (num 11)
    (by ipra_le 11) (by ipra_le 10) (by change Γ ⊢[PRAAx] le _ _; ipra_le 0)
  have hb := trans_weak _ _ _ _ _ _ sep lower_order
  have step := strict_transport _ _ _ _ _ _ _ _ (sum_as_constant a b e)
    (cross_refl _ _ (GaussianPositiveRationalLogarithm.name_regular _ _ log_source)) hb
  have shift := lt_difference CF logF CF a logData b (constant_regular a)
    (GaussianPositiveRationalLogarithm.name_regular _ _ log_source) (constant_regular b) step
  have h := (GaussianGammaDigammaElementaryOriginalLog.elementary_bounds (Γ := Γ) (one+two) one log_source).andE₁
  exact trans_weak _ _ _ _ _ _ shift h

private theorem three_upper :
    Γ ⊢[PRAAx] strictOrder DF CF (dd (one+two) one) (fraction (num 5) (num 4) : PTm n) := by
  let a : PTm n := fraction (num 5) (num 4)
  let b : PTm n := fraction one (two*(one+two))
  have e : Γ ⊢[PRAAx] qadd a b ≐ fraction (num 17) (num 12) :=
    fraction_sum_value _ _ _ _ _ _ (by ipra_le 3) (by ipra_le 5) (by ipra_le 11) (by ipra_ring)
  have sep := fraction_lt (Γ := Γ) (num 4) (num 3) (num 17) (num 12)
    (by ipra_le 2) (by ipra_le 11) (by change Γ ⊢[PRAAx] le _ _; ipra_le 2)
  have hb := weak_trans _ _ _ _ _ _ upper_order sep
  have step := strict_transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianPositiveRationalLogarithm.name_regular _ _ log_source))
    (cross_symm _ _ _ _ (sum_as_constant a b e)) hb
  have shift := difference_lt logF CF CF logData a b
    (GaussianPositiveRationalLogarithm.name_regular _ _ log_source) (constant_regular a) (constant_regular b) step
  have h := (GaussianGammaDigammaElementaryOriginalLog.elementary_bounds (Γ := Γ) (one+two) one log_source).andE₂
  exact weak_trans _ _ _ _ _ _ h shift

theorem two_lower : Γ ⊢[PRAAx] strictOrder CF DF (quarter : PTm n) (dd two one) := by
  let a : PTm n := quarter
  let b : PTm n := fraction one two
  have hs := native_source (Γ := Γ) two (by ipra_le 1)
  have e : Γ ⊢[PRAAx] qadd a b ≐ fraction (num 3) (num 4) :=
    fraction_sum_value _ _ _ _ _ _ (by ipra_le 3) (by ipra_le 1) (by ipra_le 3) (by ipra_ring)
  have h := strict_transport _ _ _ _ _ _ _ _ (sum_as_constant a b e)
    (cross_refl _ _ (GaussianGammaDigammaNative.name_regular _ _ log_source)) three_lower
  have step := lt_difference CF DF CF a (dd (one+two) one) b (constant_regular a)
    (GaussianGammaDigammaNative.name_regular _ _ log_source) (constant_regular b) h
  exact strict_transport _ _ _ _ _ _ _ _ (const_id a)
    (previous two (one+two) hs log_source (add_comm two one)) step

private theorem two_upper :
    Γ ⊢[PRAAx] strictOrder DF CF (dd two one) (fraction (num 3) (num 4) : PTm n) := by
  let a : PTm n := fraction (num 3) (num 4)
  let b : PTm n := fraction one two
  have hs := native_source (Γ := Γ) two (by ipra_le 1)
  have e : Γ ⊢[PRAAx] qadd a b ≐ fraction (num 5) (num 4) :=
    fraction_sum_value _ _ _ _ _ _ (by ipra_le 3) (by ipra_le 1) (by ipra_le 3) (by ipra_ring)
  have h := strict_transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianGammaDigammaNative.name_regular _ _ log_source))
    (cross_symm _ _ _ _ (sum_as_constant a b e)) three_upper
  have step := difference_lt DF CF CF (dd (one+two) one) a b
    (GaussianGammaDigammaNative.name_regular _ _ log_source) (constant_regular a) (constant_regular b) h
  exact strict_transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (previous two (one+two) hs log_source (add_comm two one))) (const_id a) step

private theorem negative_quarter_plus_one : Γ ⊢[PRAAx]
    qadd (negativeQuarter : PTm n) (fraction one one) ≐ fraction (num 3) (num 4) := by
  let a : PTm n := quarter
  let b : PTm n := fraction (num 3) (num 4)
  have hb : Γ ⊢[PRAAx] GaussianRationalHorner.canonical b := ofGaussian_canonical _ _ (by ipra_le 3)
  have sum : Γ ⊢[PRAAx] qadd a b ≐ fraction one one :=
    fraction_sum_value _ _ _ _ _ _ (by ipra_le 3) (by ipra_le 3) (le_refl one) (by ipra_ring)
  have cancel : Γ ⊢[PRAAx] qadd negativeQuarter a ≐ qzero :=
    (qadd_congr (qzero_add (qnegative a) (qnegative_canonical _)) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative (qnegative a) a).eqTrans (GaussianCoefficientNormOrder.qsub_self a))
  exact (qadd_congr (.eqRefl _) sum.eqSymm).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
      ((qadd_congr cancel (.eqRefl _)).eqTrans (qzero_add b hb)))

theorem one_upper : Γ ⊢[PRAAx] strictOrder DF CF (dd one one) (negativeQuarter : PTm n) := by
  let a : PTm n := negativeQuarter
  let b : PTm n := fraction one one
  have hs := native_source (Γ := Γ) two (by ipra_le 1)
  have h := strict_transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianGammaDigammaNative.name_regular _ _ hs))
    (cross_symm _ _ _ _ (sum_as_constant a b negative_quarter_plus_one)) two_upper
  have step := difference_lt DF CF CF (dd two one) a b
    (GaussianGammaDigammaNative.name_regular _ _ hs) (constant_regular a) (constant_regular b) h
  exact strict_transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (previous one two (native_source _ (le_refl one)) hs (by ipra_ring))) (const_id a) step

theorem actual_original_digamma_critical_signs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    strictOrder DF CF (dd one one) negativeQuarter ⋏ strictOrder CF DF quarter (dd two one) :=
  .andI one_upper two_lower

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaCriticalSigns
