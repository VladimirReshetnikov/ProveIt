import FabiusFunction.ThueMorseGenerating
import FabiusFunction.StepApproximationLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Thue--Morse prefix approximations

This module identifies the corrected iterated Thue--Morse prefixes with the
polynomial/histogram approximants, first exactly at dyadic cell centers and
then asymptotically along moving cells.  It includes the exceptional right
endpoint and the rescaling that recovers the Fabius function on `[0,1]`.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Filter Finset Set

namespace Fabius

open Polynomial

/-- The approximation polynomial with its natural coefficients cast to
integers, for comparison with the signed Thue--Morse power series. -/
noncomputable def approximationPolynomialInt (n : ℕ) : Polynomial ℤ :=
  (approximationPolynomial n).map (Nat.castRingHom ℤ)

private theorem one_sub_X_mul_geometricPolynomialInt (r : ℕ) :
    (1 - Polynomial.X) *
        (geometricPolynomial r).map (Nat.castRingHom ℤ) =
      1 - Polynomial.X ^ r := by
  rw [geometricPolynomial]
  simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (1 - (Polynomial.X : Polynomial ℤ)) *
          ∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℤ) ^ i =
        -(((Polynomial.X : Polynomial ℤ) - 1) *
          ∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℤ) ^ i) := by
          ring
    _ = -((Polynomial.X : Polynomial ℤ) ^ r - 1) := by rw [mul_geom_sum]
    _ = 1 - (Polynomial.X : Polynomial ℤ) ^ r := by ring

/-- The finite product identity aligning the polynomial approximants with the
denominator-cleared Thue--Morse series. -/
theorem one_sub_X_pow_mul_approximationPolynomialInt (n : ℕ) :
    (1 - Polynomial.X) ^ (n + 1) * approximationPolynomialInt n =
      thueMorseBlockPolynomial (n + 1) := by
  induction n with
  | zero =>
      rw [thueMorseBlockPolynomial_eq_product]
      simp [approximationPolynomialInt]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl,
        approximationPolynomialInt, approximationPolynomial_succ_product,
        Polynomial.map_mul]
      change (1 - Polynomial.X) ^ (n + 2) *
          (approximationPolynomialInt n *
            (geometricPolynomial (2 ^ (n + 1))).map (Nat.castRingHom ℤ)) = _
      rw [pow_succ]
      calc
        (1 - Polynomial.X) ^ (n + 1) * (1 - Polynomial.X) *
            (approximationPolynomialInt n *
              (geometricPolynomial (2 ^ (n + 1))).map (Nat.castRingHom ℤ)) =
            ((1 - Polynomial.X) ^ (n + 1) * approximationPolynomialInt n) *
              ((1 - Polynomial.X) *
                (geometricPolynomial (2 ^ (n + 1))).map (Nat.castRingHom ℤ)) := by
                  ring
        _ = thueMorseBlockPolynomial (n + 1) *
              (1 - Polynomial.X ^ (2 ^ (n + 1))) := by
                rw [ih, one_sub_X_mul_geometricPolynomialInt]
        _ = thueMorseBlockPolynomial (n + 1 + 1) := by
          simpa only using (thueMorseBlockPolynomial_succ (n + 1)).symm

private theorem coeff_thueMorseSeries_mul_inv_eq_finite
    (k m : ℕ) (hm : m < 2 ^ k) :
    PowerSeries.coeff m
        (thueMorseSeries * (PowerSeries.invOneSubPow ℤ k).val) =
      PowerSeries.coeff m
        ((thueMorseBlockPolynomial k : PowerSeries ℤ) *
          (PowerSeries.invOneSubPow ℤ k).val) := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have habsum : ab.1 + ab.2 = m := Finset.mem_antidiagonal.mp hab
  have halt : ab.1 < 2 ^ k := by omega
  rw [coeff_thueMorseSeries, Polynomial.coeff_coe,
    coeff_thueMorseBlockPolynomial k ab.1 halt]

private theorem thueMorseBlock_mul_inv_eq_approximationPolynomialInt (n : ℕ) :
    (thueMorseBlockPolynomial (n + 1) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (n + 1)).val =
      (approximationPolynomialInt n : PowerSeries ℤ) := by
  have hpoly := one_sub_X_pow_mul_approximationPolynomialInt n
  have hcoe :
      (thueMorseBlockPolynomial (n + 1) : PowerSeries ℤ) =
        (1 - PowerSeries.X) ^ (n + 1) *
          (approximationPolynomialInt n : PowerSeries ℤ) := by
    rw [← hpoly]
    simp
  rw [hcoe]
  have hunit :
      (1 - PowerSeries.X) ^ (n + 1) *
          (PowerSeries.invOneSubPow ℤ (n + 1)).val = 1 := by
    simpa [PowerSeries.invOneSubPow_zero] using
      (PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
        (S := ℤ) (d := 0) (n + 1))
  calc
    ((1 - PowerSeries.X) ^ (n + 1) *
        (approximationPolynomialInt n : PowerSeries ℤ)) *
        (PowerSeries.invOneSubPow ℤ (n + 1)).val =
      (approximationPolynomialInt n : PowerSeries ℤ) *
        ((1 - PowerSeries.X) ^ (n + 1) *
          (PowerSeries.invOneSubPow ℤ (n + 1)).val) := by ring
    _ = (approximationPolynomialInt n : PowerSeries ℤ) := by rw [hunit, mul_one]

/-- Below the first omitted dyadic coefficient, the `k`-fold inclusive prefix
sum is exactly the corresponding coefficient of `p_(k-1)`. -/
theorem iteratedPrefix_eq_approximationPolynomial_coeff
    (k m : ℕ) (hk : 0 < k) (hm : m < 2 ^ k) :
    iteratedPrefix k m = ((approximationPolynomial (k - 1)).coeff m : ℤ) := by
  cases k with
  | zero => omega
  | succ n =>
      rw [show n + 1 - 1 = n by omega]
      calc
        iteratedPrefix (n + 1) m =
            PowerSeries.coeff m (iteratedPrefixSeries (n + 1)) := by simp
        _ = PowerSeries.coeff m
            (thueMorseSeries * (PowerSeries.invOneSubPow ℤ (n + 1)).val) := by
              rw [iteratedPrefixSeries_eq]
        _ = PowerSeries.coeff m
            ((thueMorseBlockPolynomial (n + 1) : PowerSeries ℤ) *
              (PowerSeries.invOneSubPow ℤ (n + 1)).val) :=
                coeff_thueMorseSeries_mul_inv_eq_finite (n + 1) m hm
        _ = PowerSeries.coeff m (approximationPolynomialInt n : PowerSeries ℤ) := by
              rw [thueMorseBlock_mul_inv_eq_approximationPolynomialInt]
        _ = ((approximationPolynomial n).coeff m : ℤ) := by
          simp [approximationPolynomialInt]

private theorem halfEndpointIntervalIndicator_polynomialAtom_eq_ite (n m l : ℕ) :
    halfEndpointIntervalIndicator (stepIntervalLeft n l) (stepIntervalRight n l)
        (polynomialAtomLocation n m) =
      if l = m then 1 else 0 := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  by_cases hlm : l = m
  · subst l
    rw [if_pos rfl]
    exact halfEndpointIntervalIndicator_atom n m
  · rw [if_neg hlm]
    rcases lt_or_gt_of_ne hlm with hlt | hgt
    · have hright : stepIntervalRight n l < polynomialAtomLocation n m := by
        unfold stepIntervalRight polynomialAtomLocation
        apply (div_lt_div_iff_of_pos_right hden).2
        have hleNat : l + 1 ≤ m := by omega
        have hle : ((l + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hleNat
        push_cast at hle ⊢
        linarith
      have hleft : stepIntervalLeft n l < polynomialAtomLocation n m :=
        (stepIntervalLeft_lt_right n l).trans hright
      rw [halfEndpointIntervalIndicator]
      split_ifs with hboundary hinterior
      · rcases hboundary with hboundary | hboundary
        · exact (ne_of_gt hleft hboundary).elim
        · exact (ne_of_gt hright hboundary).elim
      · exact (not_lt_of_ge hright.le hinterior.2).elim
      · rfl
    · have hleft : polynomialAtomLocation n m < stepIntervalLeft n l := by
        unfold stepIntervalLeft polynomialAtomLocation
        apply (div_lt_div_iff_of_pos_right hden).2
        have hleNat : m + 1 ≤ l := by omega
        have hle : ((m + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hleNat
        push_cast at hle ⊢
        linarith
      have hright : polynomialAtomLocation n m < stepIntervalRight n l :=
        hleft.trans (stepIntervalLeft_lt_right n l)
      rw [halfEndpointIntervalIndicator]
      split_ifs with hboundary hinterior
      · rcases hboundary with hboundary | hboundary
        · exact (ne_of_lt hleft hboundary).elim
        · exact (ne_of_lt hright hboundary).elim
      · exact (not_lt_of_ge hleft.le hinterior.1).elim
      · rfl

/-- At the center of the `m`-th cell, the step approximant is precisely its
normalized polynomial coefficient. This remains true outside the polynomial
support, where both sides vanish. -/
theorem stepApproximant_at_polynomialAtomLocation (n m : ℕ) :
    stepApproximant n (polynomialAtomLocation n m) =
      (2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) *
        ((approximationPolynomial n).coeff m : ℝ) := by
  rw [stepApproximant]
  simp_rw [halfEndpointIntervalIndicator_polynomialAtom_eq_ite]
  by_cases hm : m < approximationDegree n + 1
  · simp [hm]
  · have hdegree : (approximationPolynomial n).natDegree < m := by
      rw [approximationPolynomial_natDegree]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
    simp [hm]

/-- The corrected vertical normalization for prefix order `k`. -/
noncomputable def correctedPrefixCoefficient (k m : ℕ) : ℝ :=
  (iteratedPrefix k m : ℝ) / (2 : ℝ) ^ ((k - 1).choose 2)

/-- Exact identification of a corrected prefix coefficient with the value of
the step approximant at the corresponding centered cell. -/
theorem correctedPrefixCoefficient_eq_stepApproximant
    (k m : ℕ) (hk : 0 < k) (hm : m < 2 ^ k) :
    correctedPrefixCoefficient k m =
      stepApproximant (k - 1) (polynomialAtomLocation (k - 1) m) := by
  cases k with
  | zero => omega
  | succ n =>
      rw [correctedPrefixCoefficient, show n + 1 - 1 = n by omega,
        stepApproximant_at_polynomialAtomLocation,
        iteratedPrefix_eq_approximationPolynomial_coeff (n + 1) m (by omega) hm,
        choose_succ_two, pow_add]
      push_cast
      have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp

/-- The order-`n+1` corrected prefix sample at the left dyadic grid choice
`floor(2^(n+1) x)`. -/
noncomputable def correctedPrefixGridSample (n : ℕ) (x : ℝ) : ℝ :=
  correctedPrefixCoefficient (n + 1) ⌊x * (2 : ℝ) ^ (n + 1)⌋₊

/-- Center of the step-approximant cell carrying the same coefficient. -/
noncomputable def correctedPrefixCellCenter (n : ℕ) (x : ℝ) : ℝ :=
  polynomialAtomLocation n ⌊x * (2 : ℝ) ^ (n + 1)⌋₊

/-- The centered-cell translation term tends to one after dyadic
normalization. -/
theorem approximationDegree_div_pow_succ_tendsto_one :
    Tendsto (fun n : ℕ =>
      (approximationDegree n : ℝ) / (2 : ℝ) ^ (n + 1))
      atTop (nhds 1) := by
  have hnbase :
      Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2))
  have hn :
      Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ (n + 1))
        atTop (nhds 0) := by
    convert hnbase.div_const 2 using 1
    · ext n
      rw [pow_succ]
      ring
    · norm_num
  have htwo :
      Tendsto (fun n : ℕ => (2 : ℝ) / (2 : ℝ) ^ (n + 1))
        atTop (nhds 0) := by
    have hhalf := tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert hhalf using 1
    · ext n
      rw [pow_succ]
      rw [one_div, inv_pow]
      field_simp
  have hsmall :
      Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
        atTop (nhds 0) := by
    convert hn.add htwo using 1
    · ext n
      push_cast
      ring
    · norm_num
  have heq (n : ℕ) :
      (approximationDegree n : ℝ) / (2 : ℝ) ^ (n + 1) =
        1 - ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by
    have hdegree := approximationDegree_eq n
    have hcast :
        (approximationDegree n : ℝ) + (n : ℝ) + 2 =
          (2 : ℝ) ^ (n + 1) := by exact_mod_cast hdegree
    have hpow : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    linarith
  convert tendsto_const_nhds.sub hsmall using 1
  · ext n
    exact heq n
  · norm_num

/-- Centered cells corresponding to the dyadic floor samples approach the
natural `[-1,1]` coordinate `2x-1`. -/
theorem correctedPrefixCellCenter_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => correctedPrefixCellCenter n x)
      atTop (nhds (2 * x - 1)) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  have hfloor :
      Tendsto (fun n : ℕ =>
        (⌊x * (2 : ℝ) ^ (n + 1)⌋₊ : ℝ) / (2 : ℝ) ^ (n + 1))
        atTop (nhds x) :=
    (tendsto_nat_floor_mul_div_atTop hx).comp hpow
  have hdegree := approximationDegree_div_pow_succ_tendsto_one
  convert (hfloor.const_mul 2).sub hdegree using 1
  ext n
  rw [correctedPrefixCellCenter, polynomialAtomLocation]
  ring

/-- Away from the right endpoint, the corrected prefix sample is exactly a
step-approximant value at its corresponding moving cell center. -/
theorem correctedPrefixGridSample_eq_stepApproximant
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    correctedPrefixGridSample n x =
      stepApproximant n (correctedPrefixCellCenter n x) := by
  rw [correctedPrefixGridSample, correctedPrefixCellCenter]
  apply correctedPrefixCoefficient_eq_stepApproximant (n + 1)
  · omega
  · rw [Nat.floor_lt (mul_nonneg hx0 (by positivity))]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
    nlinarith

/-- Pointwise convergence of the step approximants is stable when their
arguments move toward the evaluation point. The proof uses the common
unimodal shape and continuity of the limit, not a uniform rate. -/
theorem stepApproximant_moving_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (u : ℕ → ℝ) (y : ℝ)
    (hu : Tendsto u atTop (nhds y)) :
    Tendsto (fun n : ℕ => stepApproximant n (u n))
      atTop (nhds (rvachevUp F y)) := by
  have hgcont : ContinuousAt (rvachevUp F) y :=
    (rvachev_contDiff F hF).continuous.continuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rcases (Metric.continuousAt_iff.1 hgcont) (ε / 2) (by positivity) with
      ⟨δ, hδ, hgδ⟩
    let d : ℝ := min (δ / 2) (-y / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (by linarith)
    have hdδ : d < δ := by
      exact (min_le_left _ _).trans_lt (by linarith)
    have hdy : d ≤ -y / 2 := min_le_right _ _
    have ha0 : y - d < 0 := by linarith
    have hb0 : y + d < 0 := by linarith
    have hga : dist (rvachevUp F (y - d)) (rvachevUp F y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hgb : dist (rvachevUp F (y + d)) (rvachevUp F y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hua := (Metric.tendsto_nhds.1 hu) d hd
    have hfa := (Metric.tendsto_nhds.1
      (stepApproximant_tendsto_rvachevUp F hF (y - d))) (ε / 2) (by positivity)
    have hfb := (Metric.tendsto_nhds.1
      (stepApproximant_tendsto_rvachevUp F hF (y + d))) (ε / 2) (by positivity)
    filter_upwards [hua, hfa, hfb] with n hun hfan hfbn
    rw [Real.dist_eq, abs_lt] at hun hfan hfbn hga hgb ⊢
    have hau : y - d ≤ u n := by linarith [hun.1]
    have hub : u n ≤ y + d := by linarith [hun.2]
    have hu0 : u n < 0 := lt_of_le_of_lt hub hb0
    have hlower := stepApproximant_monotoneOn_Iio n ha0 hu0 hau
    have hupper := stepApproximant_monotoneOn_Iio n hu0 hb0 hub
    constructor <;> linarith
  · rcases (Metric.continuousAt_iff.1 hgcont) (ε / 2) (by positivity) with
      ⟨δ, hδ, hgδ⟩
    let d : ℝ := δ / 2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdδ : d < δ := by dsimp [d]; linarith
    have hga : dist (rvachevUp F (-d)) (rvachevUp F 0) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hgb : dist (rvachevUp F d) (rvachevUp F 0) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hua := (Metric.tendsto_nhds.1 hu) d hd
    have hfa := (Metric.tendsto_nhds.1
      (stepApproximant_tendsto_rvachevUp F hF (-d))) (ε / 2) (by positivity)
    have hfb := (Metric.tendsto_nhds.1
      (stepApproximant_tendsto_rvachevUp F hF d)) (ε / 2) (by positivity)
    filter_upwards [hua, hfa, hfb] with n hun hfan hfbn
    rw [Real.dist_eq, abs_lt] at hun hfan hfbn hga hgb ⊢
    have hleft : -d < u n := by linarith [hun.1]
    have hright : u n < d := by linarith [hun.2]
    have hlower : rvachevUp F 0 - ε < stepApproximant n (u n) := by
      rcases lt_trichotomy (u n) 0 with huneg | huzero | hupos
      · have hmono := stepApproximant_monotoneOn_Iio n (neg_neg_of_pos hd) huneg hleft.le
        linarith
      · rw [huzero, stepApproximant_apply_zero, rvachev_zero F hF]
        linarith
      · have hanti := stepApproximant_antitoneOn_Ioi n hupos hd hright.le
        linarith
    have hupper : stepApproximant n (u n) ≤ rvachevUp F 0 := by
      rw [rvachev_zero F hF]
      exact stepApproximant_le_one n (u n)
    constructor <;> linarith
  · rcases (Metric.continuousAt_iff.1 hgcont) (ε / 2) (by positivity) with
      ⟨δ, hδ, hgδ⟩
    let d : ℝ := min (δ / 2) (y / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (by linarith)
    have hdδ : d < δ := by
      exact (min_le_left _ _).trans_lt (by linarith)
    have hdy : d ≤ y / 2 := min_le_right _ _
    have ha0 : 0 < y - d := by linarith
    have hb0 : 0 < y + d := by linarith
    have hga : dist (rvachevUp F (y - d)) (rvachevUp F y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hgb : dist (rvachevUp F (y + d)) (rvachevUp F y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hua := (Metric.tendsto_nhds.1 hu) d hd
    have hfa := (Metric.tendsto_nhds.1
      (stepApproximant_tendsto_rvachevUp F hF (y - d))) (ε / 2) (by positivity)
    have hfb := (Metric.tendsto_nhds.1
      (stepApproximant_tendsto_rvachevUp F hF (y + d))) (ε / 2) (by positivity)
    filter_upwards [hua, hfa, hfb] with n hun hfan hfbn
    rw [Real.dist_eq, abs_lt] at hun hfan hfbn hga hgb ⊢
    have hau : y - d ≤ u n := by linarith [hun.1]
    have hub : u n ≤ y + d := by linarith [hun.2]
    have hu0 : 0 < u n := lt_of_lt_of_le ha0 hau
    have hlower := stepApproximant_antitoneOn_Ioi n hu0 hb0 hub
    have hupper := stepApproximant_antitoneOn_Ioi n ha0 hu0 hau
    constructor <;> linarith

/-- Interior and left-endpoint convergence of the corrected dyadic-floor
samples. The right endpoint is separate because its floor index is the first
coefficient not covered by the finite polynomial identity. -/
theorem correctedPrefixGridSample_tendsto_of_lt_one
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n x)
      atTop (nhds (rvachevUp F (2 * x - 1))) := by
  have hcenter := correctedPrefixCellCenter_tendsto x hx0
  have hstep := stepApproximant_moving_tendsto F hF
    (fun n => correctedPrefixCellCenter n x) (2 * x - 1) hcenter
  exact hstep.congr' (Filter.Eventually.of_forall fun n =>
    (correctedPrefixGridSample_eq_stepApproximant n hx0 hx1).symm)

/-- Exact value of the exceptional right-endpoint sample. -/
theorem correctedPrefixGridSample_one (n : ℕ) :
    correctedPrefixGridSample n 1 =
      -(1 / (2 : ℝ) ^ n.choose 2) := by
  rw [correctedPrefixGridSample, correctedPrefixCoefficient]
  have hpowcast : (2 : ℝ) ^ (n + 1) = ((2 ^ (n + 1) : ℕ) : ℝ) := by
    norm_cast
  rw [one_mul, hpowcast, Nat.floor_natCast]
  rw [show n + 1 - 1 = n by omega,
    iteratedPrefix_at_dyadic (n + 1) (n + 1) le_rfl]
  push_cast
  ring

private theorem choose_two_tendsto_atTop :
    Tendsto (fun n : ℕ => n.choose 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with n hn
  have hnpos : 0 < n := by omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [choose_succ_two]
  omega

private theorem inverse_two_pow_choose_two_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n.choose 2) atTop (nhds 0) := by
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcomp := hhalf.comp choose_two_tendsto_atTop
  convert hcomp using 1
  ext n
  simp only [Function.comp_apply, one_div, inv_pow]

/-- The exceptional right-endpoint samples converge to the correct compact
support boundary value zero. -/
theorem correctedPrefixGridSample_tendsto_one
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n 1)
      atTop (nhds (rvachevUp F 1)) := by
  have hzero : rvachevUp F 1 = 0 := by
    rw [rvachevUp, if_neg (by norm_num)]
    simpa using hF.zero_of_nonpos 0 le_rfl
  rw [hzero]
  have hneg :
      Tendsto (fun n : ℕ => -(1 / (2 : ℝ) ^ n.choose 2)) atTop (nhds 0) := by
    simpa using inverse_two_pow_choose_two_tendsto_zero.neg
  exact hneg.congr' (Filter.Eventually.of_forall fun n =>
    (correctedPrefixGridSample_one n).symm)

/-- Corrected dyadic-floor prefix samples converge pointwise on `[0,1]` to
the centered Rvachev up function. No quantitative uniform rate is asserted. -/
theorem correctedPrefixGridSample_tendsto_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n x)
      atTop (nhds (rvachevUp F (2 * x - 1))) := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · subst x
    convert correctedPrefixGridSample_tendsto_one F hF using 1
    norm_num
  · exact correctedPrefixGridSample_tendsto_of_lt_one F hF hx.1 h

/-- Equivalent first-half rescaling: sample at `x/2` to recover the Fabius
function itself on `[0,1]`. -/
theorem correctedPrefixGridSample_tendsto_fabius
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n (x / 2))
      atTop (nhds (fabiusReal F x)) := by
  have hxhalf : x / 2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have h := correctedPrefixGridSample_tendsto_rvachevUp F hF hxhalf
  have harg : 2 * (x / 2) - 1 ≤ 0 := by linarith [hx.2]
  rw [rvachevUp, if_pos harg] at h
  convert h using 1
  ring_nf

end Fabius
