import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerResidualHalfDisk
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerResidualIntervalMajorant
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerLinearInterval
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerFactorSum
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyRange
import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSumMajorant

/-!
# Quadratic error of an actual Euler logarithm interval

The interval uses the original right-half-plane log evaluator at the
original residual rows, with indices N+1 to N+r. The linearly
approximating rows are the actual finite Euler sum of z/k. Summing their
variable scalar budgets gives R²/N + 3r/2^p at a common row clock p.
The original named interval raises the row clock by its length, so its
observation error is at most R²/N + 3/2^p.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive subst_unit bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianFastValueCut (exponent query_budget)
open GaussianLogGammaEulerFactorSum (residualBody residual_at residual_rows)
open GaussianLogGammaEulerHead (rowData subst_rowData)
open GaussianLogGammaEulerLinearInterval (linearRows linearBody linearSum subst_linearRows)
open GaussianLogGammaEulerResidualCanonicalError (canonicalPoint)
open GaussianLogGammaEulerResidualHalfDisk (canonical_sample_error)
open GaussianLogGammaEulerResidualDomain (source linearTerm subst_source)
open GaussianLogGammaEulerResidualIntervalMajorant (budgetBody budgetData budgetSum budget_term
  subst_budgetData scalar_bound)
open GaussianNamedFiniteSumFamily (body finite nameF term_at sample_at)
open GaussianNamedFiniteSumFamilyRange (rangeBody rangeData range_row_at range_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub comparison_to_cleared)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant
  (termsMajorized majorized majorized_congr from_representation sum_majorized)
open RationalSupMetric (denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def intervalBody : PTm 2 := body G (rangeBody residualBody)
def intervalData (p N x : PTm n) : PTm n := pairT p (pairT N x)
def interval (p A B D neg N r : PTm n) : PTm n :=
  finite G (rangeBody residualBody) p r (pairT N (rowData A B D neg))

@[simp] theorem subst_intervalData {m : ℕ} (σ : Fin n → PTm m) (p N x : PTm n) :
    Syn.subst σ (intervalData p N x) =
      intervalData (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) := by simp [intervalData]

theorem interval_entry (p A B D neg N i : PTm n) :
    Γ ⊢[PRAAx] inst2 intervalBody i (intervalData p N (rowData A B D neg)) ≐
      canonicalPoint p A B D neg (succ (N + i)) := by
  let x := rowData A B D neg
  have row := (range_row_at (Γ := Γ) residualBody N i x).eqTrans (residual_at (N + i) A B D neg)
  exact (term_at G (rangeBody residualBody) i p (pairT N x)).eqTrans
    (congrAp2 G (.eqRefl _) row)

theorem interval_regular (A B D neg N r : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] pointCN (nameF G (rangeBody residualBody)) (rangeData N r (rowData A B D neg)) :=
  range_regular G residualBody N r (rowData A B D neg) (residual_rows A B D neg (N + r) h)

private theorem row_majorized (p A B D neg R N i : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hlarge : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] majorized
      (inst2 (differenceBody intervalBody linearBody) i
        (pairT (intervalData p N (rowData A B D neg)) (linearRows A B D neg N)))
      (inst2 budgetBody i (budgetData (R * R) (num 3) (unit p) N)) := by
  let k := succ (N + i)
  let u := unit p
  let L := R * R * u + num 3 * (k * k)
  let Q := k * k * u
  let x := intervalData p N (rowData A B D neg)
  let y := linearRows A B D neg N
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hU := unit_positive (Γ := Γ) p
  have hQ := positive_product _ _ (positive_product _ _ hk hk) hU
  have hd := canonical_sample_error p A B D neg R k h hk
    (le_trans hlarge (le_trans (le_add_right N i) (le_succ_self _)))
  have diff := (difference_body_at intervalBody linearBody i x y).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (interval_entry p A B D neg N i)
      (GaussianLogGammaEulerLinearInterval.entry A B D neg N i h.andE₁.andE₂))
  have rep := fraction_represents L Q hQ
  have sign := GaussianRationalL1.nonnegative_of_representation _ _ _ hQ rep
  exact majorized_congr diff.eqSymm (budget_term (R * R) (num 3) u N i hU).eqSymm
    (from_representation (qsub (canonicalPoint p A B D neg k) (linearTerm A B D neg k))
      (fraction L Q) L Q hQ sign rep hd)

def errorNumerator (p R N r : PTm n) : PTm n := R * R * unit p + num 3 * r * N
def errorDenominator (p N : PTm n) : PTm n := N * unit p

/-- The common-clock error for the two literal finite sums. -/
theorem sharp_interval_sample_error (p A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] distanceBounded (interval p A B D neg N r) (linearSum A B D neg N r)
      (errorNumerator p R N r) (errorDenominator p N) := by
  let x := intervalData p N (rowData A B D neg)
  let y := linearRows A B D neg N
  let m := budgetSum (R * R) (num 3) (unit p) N r
  let diff := differenceBody intervalBody linearBody
  let S := GaussianRationalFiniteSum.sum diff r (pairT x y)
  have rows : Γ ⊢[PRAAx] termsMajorized diff budgetBody r (pairT x y)
      (budgetData (R * R) (num 3) (unit p) N) := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s A) (s B) (s D) (s neg) (s R) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, subst_source] using h.shift.wk
    have hL : Δ ⊢[PRAAx] le (two * s R) (s N) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, subst_le, PTm.subst_mul, two, one, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero] using hlarge.shift.wk
    simpa only [Δ, diff, s, x, y, Syn.shift, subst_pairT, subst_intervalData, subst_rowData, subst_linearRows,
      subst_budgetData, PTm.subst_mul, subst_unit, PTm.subst_num] using row_majorized
      (s p) (s A) (s B) (s D) (s neg) (s R) (s N) (var 0) hs hL
  have estimate : Γ ⊢[PRAAx] majorized S m := sum_majorized _ _ r _ _ rows
  have hU := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one (errorDenominator p N) := positive_product _ _ hN hU
  have hm := RationalArgmin.denominator_positive (Γ := Γ) m
  have clear := comparison_to_cleared m (fraction (errorNumerator p R N r) (errorDenominator p N))
    (GaussianPositiveRealArithmetic.numerator m) (errorNumerator p R N r) (denominatorOf m) (errorDenominator p N)
    (GaussianPositiveRealArithmetic.natural_representation m estimate.andE₁)
    (fraction_represents _ _ hD) (scalar_bound (R * R) (num 3) (unit p) N r hN hU)
  have small := bounded_radius_mono _ _ _ _ _ hm hD
    (le_congr (mul_comm _ _) (.eqRefl _) clear) estimate.andE₂
  exact bound_congr (finite_sum_difference intervalBody linearBody r x y) (.eqRefl _) (.eqRefl _) small

/-- The interval's own named sampler already pays for its row count. -/
theorem sharp_named_interval_sample_error (p A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (nameF G (rangeBody residualBody)) p (rangeData N r (rowData A B D neg)))
      (linearSum A B D neg N r) (R * R * unit p + num 3 * N) (errorDenominator p N) := by
  let k := exponent r p
  have hi := sharp_interval_sample_error k A B D neg R N r h hN hlarge
  have hk := positive_product _ _ hN (unit_positive k)
  have hp := positive_product _ _ hN (unit_positive p)
  have cmp : Γ ⊢[PRAAx] le (errorNumerator k R N r * errorDenominator p N)
      ((R * R * unit p + num 3 * N) * errorDenominator k N) := by
    unfold errorNumerator errorDenominator
    ipra_le 3 * 𝔞 N * 𝔞 N * sl (query_budget (Γ := Γ) r p)
  exact distance_congr (sample_at G (rangeBody residualBody) p r (pairT N (rowData A B D neg))).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (distance_radius_mono _ _ _ _ _ _ hk hp cmp hi)

theorem interval_sample_error (p A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (num 8 * R) N) :
    Γ ⊢[PRAAx] distanceBounded (interval p A B D neg N r) (linearSum A B D neg N r)
      (errorNumerator p R N r) (errorDenominator p N) :=
  sharp_interval_sample_error p A B D neg R N r h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) hlarge)

theorem named_interval_sample_error (p A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (num 8 * R) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (nameF G (rangeBody residualBody)) p (rangeData N r (rowData A B D neg)))
      (linearSum A B D neg N r) (R * R * unit p + num 3 * N) (errorDenominator p N) :=
  sharp_named_interval_sample_error p A B D neg R N r h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) hlarge)

theorem actual_Euler_residual_common_clock_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        le one (var 6) ⟶ le (num 8 * var 5) (var 6) ⟶
          distanceBounded (interval (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
            (linearSum (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
            (errorNumerator (var 0) (var 5) (var 6) (var 7)) (errorDenominator (var 0) (var 6))) :=
  closeUniv 8 (.impI (.impI (.impI (interval_sample_error _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_Euler_residual_named_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        le one (var 6) ⟶ le (num 8 * var 5) (var 6) ⟶
          distanceBounded (ap2 (nameF G (rangeBody residualBody)) (var 0)
            (rangeData (var 6) (var 7) (rowData (var 1) (var 2) (var 3) (var 4))))
            (linearSum (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
            (var 5 * var 5 * unit (var 0) + num 3 * var 6) (errorDenominator (var 0) (var 6))) :=
  closeUniv 8 (.impI (.impI (.impI (named_interval_sample_error _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_Euler_residual_sharp_named_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        le one (var 6) ⟶ le (two * var 5) (var 6) ⟶
          distanceBounded (ap2 (nameF G (rangeBody residualBody)) (var 0)
            (rangeData (var 6) (var 7) (rowData (var 1) (var 2) (var 3) (var 4))))
            (linearSum (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
            (var 5 * var 5 * unit (var 0) + num 3 * var 6) (errorDenominator (var 0) (var 6))) :=
  closeUniv 8 (.impI (.impI (.impI (sharp_named_interval_sample_error _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualInterval
