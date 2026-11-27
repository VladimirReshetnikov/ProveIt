import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.ReciprocalSlopes.GaussianLogGammaEulerReciprocalSlope
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerRepresentation
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.Intervals.GaussianLogGammaEulerLinearIntervalError
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.Intervals.GaussianLogGammaEulerResidualIntervalMajorant
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.WeightedSums.GaussianRationalSumMajorant
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaSeriesTerms

/-!
# A uniform cutoff gap for the actual complex Euler slope

A later cutoff adds a reciprocal interval. Its error from the harmonic
interval is at most `R/N`, independent of the number of extra rows.
The logarithm increment differs from that same harmonic interval by
at most `1/N` plus the two observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlopeGap

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction_represents)
open GaussianGammaDigammaFiniteSum (reciprocalBody reciprocal_entry)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerLinearInterval (harmonicInterval reciprocal_harmonic_interval)
open GaussianLogGammaEulerReciprocalSlope (rowBody row_at row_tail reciprocalSum)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerResidualDomain (source subst_source)
open GaussianLogGammaEulerResidualIntervalMajorant (budgetBody budgetData budgetSum budget_term scalar_bound subst_budgetData)
open GaussianPositiveRationalLogarithm (sample sample_canonical)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical comparison_to_cleared)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant (majorized from_representation termsMajorized sum_majorized majorized_congr)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qadd_commutative)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "sum" => GaussianRationalFiniteSum.sum
local notation "rf" => GaussianEuclideanDistanceName.fraction
local notation "gf" => GaussianPositiveRationalLogarithm.fraction

def interval (A B D neg N r : PTm n) : PTm n :=
  sum (offB rowBody) r (pairT (succ N) (argument A B D neg))

def observed (p A B D neg N : PTm n) : PTm n :=
  qsub (sample p N one) (reciprocalSum A B D neg (succ N))

ipra_subst observed [reciprocalSum, sample, one]

private theorem harmonic_entry (N i : PTm n) :
    Γ ⊢[PRAAx] inst2 reciprocalBody i (pairT (succ N) one) ≐ gf one (succ (N + i)) :=
  (reciprocal_entry (succ N) one i).eqTrans
    (GaussianCompactRiemannName.fraction_congr one one _ _ (.eqRefl _) (by unfold GaussianGammaDigammaFiniteSum.index; ipra_ring))

private theorem row_majorized (A B D neg R N i : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] majorized
      (inst2 (differenceBody (offB rowBody) reciprocalBody) i
        (pairT (pairT (succ N) (argument A B D neg)) (pairT (succ N) one)))
      (inst2 budgetBody i (budgetData R zero one N)) := by
  let z := argument A B D neg
  let k := succ (N + i)
  let x := pairT (succ N) z
  let y := pairT (succ N) one
  have hk := zero_lt_succ (Γ := Γ) (N + i)
  have hd := positive_product _ _ hk hk
  have eq : Γ ⊢[PRAAx] succ N + i ≐ k := by dsimp only [k]; ipra_ring
  have congr : Γ ⊢[PRAAx] inst2 rowBody (succ N + i) z ≐ inst2 rowBody k z := by
    simpa only [subst_inst2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (inst2 rowBody (var 0) (var 1) : PTm 2)
        (σ := ![succ N + i, z]) (σ' := ![k, z]) (fun j => by fin_cases j; exact eq; exact .eqRefl z)
  have atRow := (offset_at rowBody (succ N) i z).eqTrans congr
  have diff := (difference_body_at (offB rowBody) reciprocalBody i x y).eqTrans
    (qsub_congr (atRow.eqTrans (row_at z k)) (harmonic_entry N i))
  have budget : Γ ⊢[PRAAx] inst2 budgetBody i (budgetData R zero one N) ≐ rf R (k * k) :=
    (budget_term R zero one N i (le_refl one)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by ipra_ring) (by dsimp only [k]; ipra_ring))
  have rep := fraction_represents R (k * k) hd
  have nonnegative := GaussianRationalL1.nonnegative_of_representation _ _ _ hd rep
  exact majorized_congr diff.eqSymm budget.eqSymm
    (from_representation _ _ R (k * k) hd nonnegative rep (row_tail A B D neg R k h hk))

theorem interval_error (A B D neg R N r : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (interval A B D neg N r) (harmonicInterval N r) R N := by
  let x := pairT (succ N) (argument A B D neg)
  let y := pairT (succ N) one
  let t := differenceBody (offB rowBody) reciprocalBody
  let m := budgetSum R zero one N r
  have hs : Γ ⊢[PRAAx] termsMajorized t budgetBody r (pairT x y) (budgetData R zero one N) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    have hh : Δ ⊢[PRAAx] source (s A) (s B) (s D) (s neg) (s R) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, subst_source] using h.shift.wk
    simpa only [Δ, s, Syn.shift, t, x, y, subst_pairT, subst_argument, subst_budgetData,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, one] using
      row_majorized (s A) (s B) (s D) (s neg) (s R) (s N) (var 0) hh
  have estimate : Γ ⊢[PRAAx] majorized (sum t r (pairT x y)) m := sum_majorized _ _ _ _ _ hs
  have budget := scalar_bound R zero one N r hN (le_refl one)
  have en : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualIntervalMajorant.numerator R zero one N r ≐ R := by
    unfold GaussianLogGammaEulerResidualIntervalMajorant.numerator
    ipra_ring
  have ed : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualIntervalMajorant.denominator one N ≐ N := by
    unfold GaussianLogGammaEulerResidualIntervalMajorant.denominator
    ipra_ring
  have scalar : Γ ⊢[PRAAx] RationalArgmin.rationalLE m (rf R N) :=
    RationalArgmin.rationalLE_congr (.eqRefl m) (RationalNonnegativePowers.fraction_congr en ed) budget
  have clear := comparison_to_cleared m (rf R N) (GaussianPositiveRealArithmetic.numerator m) R
    (denominatorOf m) N (GaussianPositiveRealArithmetic.natural_representation m estimate.andE₁)
    (fraction_represents _ _ hN) scalar
  have bound := bounded_radius_mono _ _ _ _ _ (RationalArgmin.denominator_positive m) hN
    (le_congr (mul_comm _ _) (.eqRefl _) clear) estimate.andE₂
  exact bound_congr ((finite_sum_difference (offB rowBody) reciprocalBody r x y).eqTrans
    (qsub_congr (.eqRefl _) (reciprocal_harmonic_interval N r))) (.eqRefl _) (.eqRefl _) bound

private theorem sum_split (A B D neg N r : PTm n) : Γ ⊢[PRAAx]
    reciprocalSum A B D neg (succ (N + r)) ≐
      qadd (reciprocalSum A B D neg (succ N)) (interval A B D neg N r) :=
  (GaussianRationalFiniteSum.sum_index_congr rowBody (m := succ (N + r)) (l := succ N + r)
    (by ipra_ring) (.eqRefl (argument A B D neg))).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split rowBody (succ N) r (argument A B D neg))

private theorem observed_difference (p q A B D neg N r : PTm n) : Γ ⊢[PRAAx]
    qsub (observed p A B D neg (N + r)) (observed q A B D neg N) ≐
      qsub (GaussianPositiveRationalLogarithmIncrement.increment p q N one r) (interval A B D neg N r) := by
  let a := sample p (N + r) one
  let b := sample q N one
  let x := reciprocalSum A B D neg (succ N)
  let y := interval A B D neg N r
  let v := qsub (qsub a b) y
  let u := qsub b x
  have recover : Γ ⊢[PRAAx] qadd (qsub a b) b ≐ a :=
    (qadd_commutative (qsub a b) b).eqTrans
      (GaussianRationalLinearProduct.add_sub_right b a (sample_canonical p (N + r) one))
  have regroup : Γ ⊢[PRAAx] qadd v u ≐ observed p A B D neg (N + r) :=
    (GaussianGammaDigammaSeriesTerms.subtract_add_exchange (qsub a b) y b x).eqTrans
      (qsub_congr recover ((qadd_commutative y x).eqTrans (sum_split A B D neg N r).eqSymm))
  exact (qsub_congr (regroup.eqSymm.eqTrans (qadd_commutative v u)) (.eqRefl _)).eqTrans
    (qadd_sub_cancel u v (qsub_canonical _ _))

def gapNumerator (p q R N : PTm n) : PTm n := (R + one) * (unit p * unit q) + N * (unit p + unit q)

def gapDenominator (p q N : PTm n) : PTm n := N * (unit p * unit q)

/-- The literal cofinal slope observations have a uniform gap with independent clocks. -/
theorem ordered_gap (p q A B D neg R N r : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (observed p A B D neg (N + r)) (observed q A B D neg N)
      (gapNumerator p q R N) (gapDenominator p q N) := by
  let x := GaussianPositiveRationalLogarithmIncrement.increment p q N one r
  let y := harmonicInterval N r
  let z := interval A B D neg N r
  let U := unit p * unit q
  let Q := N * U
  have hQ : Γ ⊢[PRAAx] le one Q := positive_product _ _ hN
    (positive_product _ _ (unit_positive p) (unit_positive q))
  have hxy := GaussianLogGammaEulerLinearIntervalError.logarithms_at p q N r hN
  have hyz : Γ ⊢[PRAAx] distanceBounded y z (R * U) Q :=
    distance_radius_mono y z R N _ _ hN hQ
      (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring))
      (distance_symmetric z y R N hN (interval_error A B D neg R N r h hN))
  have total := distance_triangle_same x y z (GaussianLogGammaEulerLinearIntervalError.errorNumerator p q N)
    (R * U) Q hQ hxy hyz
  exact bound_congr (observed_difference p q A B D neg N r).eqSymm
    (by dsimp only [U, gapNumerator, GaussianLogGammaEulerLinearIntervalError.errorNumerator]; ipra_ring)
    (.eqRefl _) total

theorem actual_complex_Euler_logarithmic_slope_ordered_gap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le one (var 7) ⟶
        distanceBounded (observed (var 0) (var 2) (var 3) (var 4) (var 5) (var 7 + var 8))
          (observed (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))
          (gapNumerator (var 0) (var 1) (var 6) (var 7)) (gapDenominator (var 0) (var 1) (var 7))) :=
  closeUniv 9 (.impI (.impI (ordered_gap _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlopeGap
