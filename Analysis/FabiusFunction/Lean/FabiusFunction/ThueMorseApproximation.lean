import FabiusFunction.ThueMorseGenerating
import FabiusFunction.StepApproximationLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Thue--Morse prefix approximations

This module identifies the corrected iterated Thue--Morse prefixes with the
polynomial/histogram approximants, first exactly at dyadic cell centers and
then asymptotically along moving cells.  It includes the exceptional right
endpoint, natural-floor clamping on the nonpositive half-line, and the
rescaling that recovers the Fabius function on `[0,1]`.  The exact coefficient
identification covers every prefix order: at order zero the dyadic cutoff
admits only index zero, where both sides equal one.  Both the finite polynomial
factorization and its formal-power-series quotient are likewise total at order
zero, with natural predecessor saturation selecting `p_0`.

Main results:

* `one_sub_X_pow_mul_approximationPolynomialInt_all`: the denominator-cleared
  finite-product identity at every order.
* `thueMorseBlockPolynomial_mul_invOneSubPow_eq_approximationPolynomialInt`:
  the formal-power-series quotient form of the same identity.
* `iteratedPrefix_eq_approximationPolynomial_coeff_all`: the iterated prefix
  sums are the coefficients of `p_(k-1)` below the dyadic cutoff.
* `correctedPrefixCoefficient_eq_stepApproximant_all`: the corrected prefix
  coefficients are exactly the step-approximant values at cell centers.
* `tendsto_moving_of_unimodal_of_tendsto`: the abstract squeeze lemma that
  transports pointwise convergence of a unimodal family to a moving argument.
* `stepApproximant_moving_tendsto`: its specialization to the step
  approximants and Rvachev's up function.
* `correctedPrefixGridSample_tendsto_rvachevUp_of_le_one` and
  `correctedPrefixGridSample_tendsto_fabius_of_le_one`: half-line pointwise
  convergence of the corrected dyadic-floor samples, together with their
  `Set.Icc` corollaries.
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

/-- All-order form of the denominator-cleared finite-product identity.  At
order zero, natural predecessor saturation selects `p_0` and both sides are
one. -/
theorem one_sub_X_pow_mul_approximationPolynomialInt_all (k : ℕ) :
    (1 - Polynomial.X) ^ k * approximationPolynomialInt (k - 1) =
      thueMorseBlockPolynomial k := by
  cases k with
  | zero =>
      rw [thueMorseBlockPolynomial_eq_product]
      simp [approximationPolynomialInt]
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        one_sub_X_pow_mul_approximationPolynomialInt n

/-- Dividing the finite Thue--Morse block by `(1-X)^k` in formal power series
recovers the integer approximation polynomial at every order, including
`k = 0`. -/
theorem thueMorseBlockPolynomial_mul_invOneSubPow_eq_approximationPolynomialInt
    (k : ℕ) :
    (thueMorseBlockPolynomial k : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ k).val =
      (approximationPolynomialInt (k - 1) : PowerSeries ℤ) := by
  have hpoly := one_sub_X_pow_mul_approximationPolynomialInt_all k
  have hcoe :
      (thueMorseBlockPolynomial k : PowerSeries ℤ) =
        (1 - PowerSeries.X) ^ k *
          (approximationPolynomialInt (k - 1) : PowerSeries ℤ) := by
    rw [← hpoly]
    simp
  rw [hcoe]
  have hunit :
      (1 - PowerSeries.X) ^ k *
          (PowerSeries.invOneSubPow ℤ k).val = 1 := by
    simpa [PowerSeries.invOneSubPow_zero] using
      (PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
        (S := ℤ) (d := 0) k)
  calc
    ((1 - PowerSeries.X) ^ k *
        (approximationPolynomialInt (k - 1) : PowerSeries ℤ)) *
        (PowerSeries.invOneSubPow ℤ k).val =
      (approximationPolynomialInt (k - 1) : PowerSeries ℤ) *
        ((1 - PowerSeries.X) ^ k *
          (PowerSeries.invOneSubPow ℤ k).val) := by ring
    _ = (approximationPolynomialInt (k - 1) : PowerSeries ℤ) := by
      rw [hunit, mul_one]

/-- Below the first omitted dyadic coefficient, the `k`-fold inclusive prefix
sum is the corresponding coefficient of `p_(k-1)`.  At order zero, natural
predecessor saturation selects `p_0`, and the cutoff forces the sole index
`m = 0`. -/
theorem iteratedPrefix_eq_approximationPolynomial_coeff_all
    (k m : ℕ) (hm : m < 2 ^ k) :
    iteratedPrefix k m = ((approximationPolynomial (k - 1)).coeff m : ℤ) := by
  calc
    iteratedPrefix k m =
        PowerSeries.coeff m
          ((thueMorseBlockPolynomial k : PowerSeries ℤ) *
            (PowerSeries.invOneSubPow ℤ k).val) :=
      (coeff_thueMorseBlockPolynomial_mul_invOneSubPow_eq_iteratedPrefix
        k k m hm).symm
    _ = PowerSeries.coeff m
          (approximationPolynomialInt (k - 1) : PowerSeries ℤ) := by
      rw [thueMorseBlockPolynomial_mul_invOneSubPow_eq_approximationPolynomialInt]
    _ = ((approximationPolynomial (k - 1)).coeff m : ℤ) := by
      simp [approximationPolynomialInt]

/-- Positive-order compatibility form of
`iteratedPrefix_eq_approximationPolynomial_coeff_all`.  The positivity
hypothesis is not needed by the proof and is retained only so that the
statement matches the source. -/
theorem iteratedPrefix_eq_approximationPolynomial_coeff
    (k m : ℕ) (_hk : 0 < k) (hm : m < 2 ^ k) :
    iteratedPrefix k m = ((approximationPolynomial (k - 1)).coeff m : ℤ) :=
  iteratedPrefix_eq_approximationPolynomial_coeff_all k m hm

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
      exact halfEndpointIntervalIndicator_eq_zero_of_right_lt
        (stepIntervalLeft_lt_right n l) hright
    · have hleft : polynomialAtomLocation n m < stepIntervalLeft n l := by
        unfold stepIntervalLeft polynomialAtomLocation
        apply (div_lt_div_iff_of_pos_right hden).2
        have hleNat : m + 1 ≤ l := by omega
        have hle : ((m + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hleNat
        push_cast at hle ⊢
        linarith
      exact halfEndpointIntervalIndicator_eq_zero_of_lt_left
        (stepIntervalLeft_lt_right n l) hleft

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
the step approximant at the corresponding centered cell, at every prefix
order.  At order zero the dyadic cutoff forces `m = 0`, and both sides equal
one. -/
theorem correctedPrefixCoefficient_eq_stepApproximant_all
    (k m : ℕ) (hm : m < 2 ^ k) :
    correctedPrefixCoefficient k m =
      stepApproximant (k - 1) (polynomialAtomLocation (k - 1) m) := by
  rw [correctedPrefixCoefficient, stepApproximant_at_polynomialAtomLocation,
    iteratedPrefix_eq_approximationPolynomial_coeff_all k m hm,
    choose_succ_two, pow_add]
  push_cast
  have hpow : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
  field_simp

/-- Positive-order compatibility form of
`correctedPrefixCoefficient_eq_stepApproximant_all`.  The positivity
hypothesis is not needed by the proof and is retained only so that the
statement matches the source. -/
theorem correctedPrefixCoefficient_eq_stepApproximant
    (k m : ℕ) (_hk : 0 < k) (hm : m < 2 ^ k) :
    correctedPrefixCoefficient k m =
      stepApproximant (k - 1) (polynomialAtomLocation (k - 1) m) :=
  correctedPrefixCoefficient_eq_stepApproximant_all k m hm

/-- The order-`n+1` corrected prefix sample at the left dyadic grid choice
`floor(2^(n+1) x)`. -/
noncomputable def correctedPrefixGridSample (n : ℕ) (x : ℝ) : ℝ :=
  correctedPrefixCoefficient (n + 1) ⌊x * (2 : ℝ) ^ (n + 1)⌋₊

/-- Exact value of the corrected prefix sample at the left endpoint. -/
theorem correctedPrefixGridSample_zero (n : ℕ) :
    correctedPrefixGridSample n 0 = 1 / (2 : ℝ) ^ n.choose 2 := by
  simp [correctedPrefixGridSample, correctedPrefixCoefficient]

/-- Natural floor clamping makes every nonpositive sample equal to the left
endpoint sample. -/
theorem correctedPrefixGridSample_eq_at_zero_of_nonpos
    (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    correctedPrefixGridSample n x = correctedPrefixGridSample n 0 := by
  rw [correctedPrefixGridSample, correctedPrefixGridSample,
    Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hx (by positivity))]
  norm_num

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
  apply correctedPrefixCoefficient_eq_stepApproximant_all (n + 1)
  rw [Nat.floor_lt (mul_nonneg hx0 (by positivity))]
  rw [Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  nlinarith

/-- Abstract moving-argument squeeze for a unimodal family.  A family `f` of
real functions that increases on `Iio 0`, decreases on `Ioi 0`, matches the
limit at the origin, never exceeds the peak value `g 0`, and converges
pointwise to `g` along a filter `l`, also converges to `g y` when evaluated
along any sequence `u` tending to `y`, provided only that `g` is continuous
at `y`.  No quantitative uniform rate is used: the two-sided monotone shape
is what transports the pointwise limits to the moving arguments. -/
theorem tendsto_moving_of_unimodal_of_tendsto
    {ι : Type*} {l : Filter ι} (f : ι → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmono : ∀ n, MonotoneOn (f n) (Iio 0))
    (hfanti : ∀ n, AntitoneOn (f n) (Ioi 0))
    (hfzero : ∀ n, f n 0 = g 0)
    (hfle : ∀ n x, f n x ≤ g 0)
    (hpt : ∀ x : ℝ, Tendsto (fun n => f n x) l (nhds (g x)))
    (u : ι → ℝ) (y : ℝ) (hgcont : ContinuousAt g y)
    (hu : Tendsto u l (nhds y)) :
    Tendsto (fun n => f n (u n)) l (nhds (g y)) := by
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
    have hga : dist (g (y - d)) (g y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hgb : dist (g (y + d)) (g y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hua := (Metric.tendsto_nhds.1 hu) d hd
    have hfa := (Metric.tendsto_nhds.1 (hpt (y - d))) (ε / 2) (by positivity)
    have hfb := (Metric.tendsto_nhds.1 (hpt (y + d))) (ε / 2) (by positivity)
    filter_upwards [hua, hfa, hfb] with n hun hfan hfbn
    rw [Real.dist_eq, abs_lt] at hun hfan hfbn hga hgb ⊢
    have hau : y - d ≤ u n := by linarith [hun.1]
    have hub : u n ≤ y + d := by linarith [hun.2]
    have hu0 : u n < 0 := lt_of_le_of_lt hub hb0
    have hlower := hfmono n ha0 hu0 hau
    have hupper := hfmono n hu0 hb0 hub
    constructor <;> linarith
  · rcases (Metric.continuousAt_iff.1 hgcont) (ε / 2) (by positivity) with
      ⟨δ, hδ, hgδ⟩
    let d : ℝ := δ / 2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdδ : d < δ := by dsimp [d]; linarith
    have hga : dist (g (-d)) (g 0) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hgb : dist (g d) (g 0) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hua := (Metric.tendsto_nhds.1 hu) d hd
    have hfa := (Metric.tendsto_nhds.1 (hpt (-d))) (ε / 2) (by positivity)
    have hfb := (Metric.tendsto_nhds.1 (hpt d)) (ε / 2) (by positivity)
    filter_upwards [hua, hfa, hfb] with n hun hfan hfbn
    rw [Real.dist_eq, abs_lt] at hun hfan hfbn hga hgb ⊢
    have hleft : -d < u n := by linarith [hun.1]
    have hright : u n < d := by linarith [hun.2]
    have hlower : g 0 - ε < f n (u n) := by
      rcases lt_trichotomy (u n) 0 with huneg | huzero | hupos
      · have hmono := hfmono n (neg_neg_of_pos hd) huneg hleft.le
        linarith
      · rw [huzero, hfzero n]
        linarith
      · have hanti := hfanti n hupos hd hright.le
        linarith
    have hupper : f n (u n) ≤ g 0 := hfle n (u n)
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
    have hga : dist (g (y - d)) (g y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hgb : dist (g (y + d)) (g y) < ε / 2 := by
      apply hgδ
      simpa [Real.dist_eq, abs_of_nonneg hd.le] using hdδ
    have hua := (Metric.tendsto_nhds.1 hu) d hd
    have hfa := (Metric.tendsto_nhds.1 (hpt (y - d))) (ε / 2) (by positivity)
    have hfb := (Metric.tendsto_nhds.1 (hpt (y + d))) (ε / 2) (by positivity)
    filter_upwards [hua, hfa, hfb] with n hun hfan hfbn
    rw [Real.dist_eq, abs_lt] at hun hfan hfbn hga hgb ⊢
    have hau : y - d ≤ u n := by linarith [hun.1]
    have hub : u n ≤ y + d := by linarith [hun.2]
    have hu0 : 0 < u n := lt_of_lt_of_le ha0 hau
    have hlower := hfanti n hu0 hb0 hub
    have hupper := hfanti n ha0 hu0 hau
    constructor <;> linarith

/-- Pointwise convergence of the step approximants is stable when their
arguments move toward the evaluation point. The proof uses the common
unimodal shape and continuity of the limit, not a uniform rate: it is the
specialization of `tendsto_moving_of_unimodal_of_tendsto` to the step
approximants. -/
theorem stepApproximant_moving_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (u : ℕ → ℝ) (y : ℝ)
    (hu : Tendsto u atTop (nhds y)) :
    Tendsto (fun n : ℕ => stepApproximant n (u n))
      atTop (nhds (rvachevUp F y)) :=
  tendsto_moving_of_unimodal_of_tendsto stepApproximant (rvachevUp F)
    stepApproximant_monotoneOn_Iio stepApproximant_antitoneOn_Ioi
    (fun _ => by rw [stepApproximant_apply_zero, rvachev_zero F hF])
    (fun n x => by
      rw [rvachev_zero F hF]
      exact stepApproximant_le_one n x)
    (stepApproximant_tendsto_rvachevUp F hF) u y
    (rvachev_contDiff F hF).continuous.continuousAt hu

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

/-- On the whole nonpositive half-line the natural-floor samples are the left
endpoint samples, and hence converge to the zero tail of `rvachevUp`. -/
theorem correctedPrefixGridSample_tendsto_of_nonpos
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≤ 0) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n x)
      atTop (nhds (rvachevUp F (2 * x - 1))) := by
  have htarget : rvachevUp F (2 * x - 1) = 0 :=
    rvachevUp_eq_zero_of_le_neg_one F hF (by linarith)
  rw [htarget]
  exact inverse_two_pow_choose_two_tendsto_zero.congr'
    (Filter.Eventually.of_forall fun n => by
      change 1 / (2 : ℝ) ^ n.choose 2 = correctedPrefixGridSample n x
      rw [correctedPrefixGridSample_eq_at_zero_of_nonpos n hx,
        correctedPrefixGridSample_zero])

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

/-- Corrected dyadic-floor prefix samples converge to the centered Rvachev
function on the full half-line `x ≤ 1`.  For `x ≤ 0` natural-floor clamping
reduces the samples to the left endpoint; on `(0,1)` the moving-cell theorem
applies, and `x = 1` is the exceptional endpoint calculation. -/
theorem correctedPrefixGridSample_tendsto_rvachevUp_of_le_one
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≤ 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n x)
      atTop (nhds (rvachevUp F (2 * x - 1))) := by
  rcases lt_or_eq_of_le hx with hxlt | rfl
  · rcases le_total x 0 with hx0 | hx0
    · exact correctedPrefixGridSample_tendsto_of_nonpos F hF hx0
    · exact correctedPrefixGridSample_tendsto_of_lt_one F hF hx0 hxlt
  · convert correctedPrefixGridSample_tendsto_one F hF using 1
    norm_num

/-- Corrected dyadic-floor prefix samples converge pointwise on `[0,1]` to
the centered Rvachev up function. No quantitative uniform rate is asserted. -/
theorem correctedPrefixGridSample_tendsto_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n x)
      atTop (nhds (rvachevUp F (2 * x - 1))) := by
  exact correctedPrefixGridSample_tendsto_rvachevUp_of_le_one F hF hx.2

/-- Half-line form of the first-half rescaling: sampling at `x/2` recovers
the Fabius function for every `x ≤ 1`, with no lower bound on `x`.  Below
zero both sides vanish, by natural-floor clamping on the left and by the
support of `rvachevUp` on the right. -/
theorem correctedPrefixGridSample_tendsto_fabius_of_le_one
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≤ 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n (x / 2))
      atTop (nhds (fabiusReal F x)) := by
  have h := correctedPrefixGridSample_tendsto_rvachevUp_of_le_one F hF
    (show x / 2 ≤ 1 by linarith)
  have harg : 2 * (x / 2) - 1 ≤ 0 := by linarith
  rw [rvachevUp, if_pos harg] at h
  convert h using 1
  ring_nf

/-- Equivalent first-half rescaling: sample at `x/2` to recover the Fabius
function itself on `[0,1]`.  Compatibility corollary of
`correctedPrefixGridSample_tendsto_fabius_of_le_one`. -/
theorem correctedPrefixGridSample_tendsto_fabius
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => correctedPrefixGridSample n (x / 2))
      atTop (nhds (fabiusReal F x)) := by
  exact correctedPrefixGridSample_tendsto_fabius_of_le_one F hF hx.2

end Fabius
