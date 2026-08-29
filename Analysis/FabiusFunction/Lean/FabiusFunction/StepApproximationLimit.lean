import FabiusFunction.StepMeasureBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shape and pointwise-limit infrastructure for the step approximants

This module proves the coefficient unimodality and the resulting monotonicity of the step
functions used in Theorem 2 of arXiv:1702.05442.  It also supplies the interval-average squeeze
that turns convergence of interval integrals into pointwise convergence to a continuous limit.

The paper uses closed interval indicators, which double-count shared endpoints.  The underlying
definition in `EarlyApproximants` uses the mathematically necessary half-endpoint representative;
in particular, `stepApproximant_apply_zero` holds literally for every index.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal MeasureTheory Topology Interval
open Filter Finset MeasureTheory Set

namespace Fabius

open Polynomial

/-- Below the window length `L`, multiplying by `geometricPolynomial L`
replaces the coefficient sequence of `p` by its prefix sums.  This is the
low-index input to the unimodality analysis of the coefficients of
`approximationPolynomial (k + 1)`. -/
theorem coeff_mul_geometric_of_lt (p : Polynomial ℕ) {L r : ℕ} (hr : r < L) :
    (p * geometricPolynomial L).coeff r = ∑ i ∈ range (r + 1), p.coeff i := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [geometricPolynomial_coeff, if_pos (by omega)]
  simp

/-- Sliding-window form of the same product, valid once the index `r` has
reached `p.natDegree`: only the coefficients `p.coeff i` with `r - i < L`
contribute.  High-index counterpart of `coeff_mul_geometric_of_lt`. -/
theorem coeff_mul_geometric_of_natDegree_le (p : Polynomial ℕ) {L r : ℕ}
    (hr : p.natDegree ≤ r) :
    (p * geometricPolynomial L).coeff r =
      ∑ i ∈ range (p.natDegree + 1),
        p.coeff i * if r - i < L then 1 else 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_subset (show range (p.natDegree + 1) ⊆ range (r + 1) by
    exact range_mono (Nat.succ_le_succ hr))]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [geometricPolynomial_coeff]
  · intro i hir hinat
    have hi : p.natDegree < i := by simpa using hinat
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
    simp

/-- On indices below the window length `L` the coefficients of
`p * geometricPolynomial L` are nondecreasing: `r ≤ s < L` forces the `r`-th
coefficient to be at most the `s`-th.  This is the rising half of the
unimodal coefficient profile of `approximationPolynomial (k + 1)`. -/
theorem coeff_mul_geometric_monotone_before (p : Polynomial ℕ) {L r s : ℕ}
    (hrs : r ≤ s) (hs : s < L) :
    (p * geometricPolynomial L).coeff r ≤ (p * geometricPolynomial L).coeff s := by
  rw [coeff_mul_geometric_of_lt p (hrs.trans_lt hs), coeff_mul_geometric_of_lt p hs]
  exact Finset.sum_le_sum_of_subset (range_mono (Nat.succ_le_succ hrs))

/-- On indices at or beyond `p.natDegree` the coefficients of
`p * geometricPolynomial L` are nonincreasing.  This is the falling half of
the unimodal coefficient profile of `approximationPolynomial (k + 1)`. -/
theorem coeff_mul_geometric_antitone_after (p : Polynomial ℕ) {L r s : ℕ}
    (hdegree : p.natDegree ≤ r) (hrs : r ≤ s) :
    (p * geometricPolynomial L).coeff s ≤ (p * geometricPolynomial L).coeff r := by
  rw [coeff_mul_geometric_of_natDegree_le p (hdegree.trans hrs),
    coeff_mul_geometric_of_natDegree_le p hdegree]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : s - i < L
  · rw [if_pos hs, if_pos (by omega)]
  · rw [if_neg hs]
    simp

/-- On the plateau `p.natDegree ≤ r < L` every coefficient of
`p * geometricPolynomial L` equals `p.eval 1`.  This fixes the common plateau
height that `stepApproximant_apply_zero` reads off at the origin. -/
theorem coeff_mul_geometric_eq_eval_one (p : Polynomial ℕ) {L r : ℕ}
    (hdegree : p.natDegree ≤ r) (hrL : r < L) :
    (p * geometricPolynomial L).coeff r = p.eval 1 := by
  rw [coeff_mul_geometric_of_lt p hrL, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  symm
  apply Finset.sum_subset (range_mono (Nat.succ_le_succ hdegree))
  intro i hir hinat
  have hi : p.natDegree < i := by simpa using hinat
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hi

/-- No coefficient of `approximationPolynomial (k + 1)` exceeds the plateau
value `(approximationPolynomial k).eval 1`.  This is the coefficient bound
behind the global height bound `stepApproximant_le_one`. -/
theorem approximationPolynomial_succ_coeff_le_eval_one (k m : ℕ) :
    (approximationPolynomial (k + 1)).coeff m ≤
      (approximationPolynomial k).eval 1 := by
  let L : ℕ := 2 ^ (k + 1)
  rw [approximationPolynomial_succ_product]
  by_cases hmL : m < L
  · rw [coeff_mul_geometric_of_lt _ hmL, Polynomial.eval_eq_sum_range]
    simp only [one_pow, mul_one]
    by_cases hmg : m ≤ (approximationPolynomial k).natDegree
    · exact Finset.sum_le_sum_of_subset (range_mono (Nat.succ_le_succ hmg))
    · apply le_of_eq
      symm
      apply Finset.sum_subset (range_mono (by omega))
      intro i hir hinat
      have hi : (approximationPolynomial k).natDegree < i := by simpa using hinat
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hi
  · calc
      (approximationPolynomial k * geometricPolynomial L).coeff m ≤
          (approximationPolynomial k * geometricPolynomial L).coeff
            (approximationPolynomial k).natDegree :=
        coeff_mul_geometric_antitone_after (approximationPolynomial k) le_rfl
          (by
            rw [approximationPolynomial_natDegree]
            have h := approximationDegree_eq k
            dsimp [L] at hmL ⊢
            omega)
      _ = (approximationPolynomial k).eval 1 :=
        coeff_mul_geometric_eq_eval_one _ le_rfl (by
          rw [approximationPolynomial_natDegree]
          dsimp [L]
          have h := approximationDegree_eq k
          omega)

/-- For `a < b < c` the half-endpoint indicators of `[a,b]` and `[b,c]` add
to the half-endpoint indicator of `[a,c]`: the two halves at the shared
endpoint `b` combine into a full `1`.  This additivity is what the
half-endpoint convention buys, and it drives every telescoping and Abel
summation below. -/
theorem halfEndpointIntervalIndicator_add_adjacent {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (x : ℝ) :
    halfEndpointIntervalIndicator a b x + halfEndpointIntervalIndicator b c x =
      halfEndpointIntervalIndicator a c x := by
  unfold halfEndpointIntervalIndicator
  split_ifs <;> grind

/- The abutting-cells identity `stepIntervalRight_eq_left_succ` now lives in
`EarlyApproximants.lean` beside the cell definitions; this file keeps its
original local `simp` scope for the telescoping arguments below. -/
attribute [simp] stepIntervalRight_eq_left_succ

/-- At a fixed level `n` the left endpoints `stepIntervalLeft n m` are
strictly increasing in the cell index `m`, so the histogram cells of
`φ_n` are laid out in order. -/
theorem stepIntervalLeft_strictMono (n : ℕ) : StrictMono (stepIntervalLeft n) := by
  intro a b hab
  unfold stepIntervalLeft
  have hden : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have habr : (a : ℝ) < b := by exact_mod_cast hab
  apply (div_lt_div_iff_of_pos_right hden).2
  linarith

/-- For `a < b`, the half-endpoint indicator of `[a,b]` is monotone on the
open ray `Iio b`.  The point `b` must be excluded: the indicator falls back
to `1/2` there. -/
theorem halfEndpointIntervalIndicator_monotoneOn_Iio_right {a b : ℝ}
    (_hab : a < b) :
    MonotoneOn (halfEndpointIntervalIndicator a b) (Iio b) := by
  intro x hx y hy hxy
  unfold halfEndpointIntervalIndicator
  split_ifs <;> grind

/-- For `a < b`, the half-endpoint indicator of `[a,b]` is antitone on the
open ray `Ioi a`.  The point `a` must be excluded: the indicator is only
`1/2` there. -/
theorem halfEndpointIntervalIndicator_antitoneOn_Ioi_left {a b : ℝ}
    (_hab : a < b) :
    AntitoneOn (halfEndpointIntervalIndicator a b) (Ioi a) := by
  intro x hx y hy hxy
  unfold halfEndpointIntervalIndicator
  split_ifs <;> grind

/-- The half-endpoint indicator of `[a,b]` vanishes strictly to the left of
`a`. -/
theorem halfEndpointIntervalIndicator_eq_zero_of_lt_left {a b x : ℝ} (hab : a < b)
    (hx : x < a) :
    halfEndpointIntervalIndicator a b x = 0 := by
  unfold halfEndpointIntervalIndicator
  split_ifs <;> grind

/-- The half-endpoint indicator of `[a,b]` vanishes strictly to the right of
`b`. -/
theorem halfEndpointIntervalIndicator_eq_zero_of_right_lt {a b x : ℝ} (hab : a < b)
    (hx : b < x) :
    halfEndpointIntervalIndicator a b x = 0 := by
  unfold halfEndpointIntervalIndicator
  split_ifs <;> grind

/-- The outer endpoints of the step approximant are symmetric about zero. -/
theorem stepIntervalRight_degree_eq_neg_left_zero (n : ℕ) :
    stepIntervalRight n (approximationDegree n) =
      -stepIntervalLeft n 0 := by
  unfold stepIntervalRight stepIntervalLeft
  ring

/-- A step approximant vanishes strictly to the left of its first cell. -/
theorem stepApproximant_eq_zero_of_lt_left_support
    (n : ℕ) {x : ℝ} (hx : x < stepIntervalLeft n 0) :
    stepApproximant n x = 0 := by
  unfold stepApproximant
  have hsum :
      (∑ m ∈ range (approximationDegree n + 1),
        ((approximationPolynomial n).coeff m : ℝ) *
          halfEndpointIntervalIndicator (stepIntervalLeft n m)
            (stepIntervalRight n m) x) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hxm : x < stepIntervalLeft n m :=
      hx.trans_le ((stepIntervalLeft_strictMono n).monotone (Nat.zero_le m))
    rw [halfEndpointIntervalIndicator_eq_zero_of_lt_left
      (stepIntervalLeft_lt_right n m) hxm, mul_zero]
  rw [hsum, mul_zero]

/-- A step approximant vanishes strictly to the right of its last cell. -/
theorem stepApproximant_eq_zero_of_right_support_lt
    (n : ℕ) {x : ℝ}
    (hx : stepIntervalRight n (approximationDegree n) < x) :
    stepApproximant n x = 0 := by
  unfold stepApproximant
  have hsum :
      (∑ m ∈ range (approximationDegree n + 1),
        ((approximationPolynomial n).coeff m : ℝ) *
          halfEndpointIntervalIndicator (stepIntervalLeft n m)
            (stepIntervalRight n m) x) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hmdegree : m ≤ approximationDegree n := by
      rw [Finset.mem_range] at hm
      omega
    have hmright :
        stepIntervalRight n m ≤
          stepIntervalRight n (approximationDegree n) := by
      simpa only [stepIntervalRight_eq_left_succ] using
        (stepIntervalLeft_strictMono n).monotone (Nat.succ_le_succ hmdegree)
    rw [halfEndpointIntervalIndicator_eq_zero_of_right_lt
      (stepIntervalLeft_lt_right n m) (hmright.trans_lt hx), mul_zero]
  rw [hsum, mul_zero]

/-- Exact compact-support enclosure for every step approximant.  The closed
endpoints are necessary because the chosen representative has half weight at
cell boundaries. -/
theorem support_stepApproximant_subset (n : ℕ) :
    Function.support (stepApproximant n) ⊆
      Icc (stepIntervalLeft n 0)
        (stepIntervalRight n (approximationDegree n)) := by
  intro x hx
  change stepApproximant n x ≠ 0 at hx
  constructor
  · by_contra hleft
    exact hx (stepApproximant_eq_zero_of_lt_left_support n (lt_of_not_ge hleft))
  · by_contra hright
    exact hx (stepApproximant_eq_zero_of_right_support_lt n (lt_of_not_ge hright))

/-- The half-endpoint indicator never exceeds `1`.  No ordering of `a` and
`b` is assumed. -/
theorem halfEndpointIntervalIndicator_le_one (a b x : ℝ) :
    halfEndpointIntervalIndicator a b x ≤ 1 := by
  unfold halfEndpointIntervalIndicator
  split_ifs <;> norm_num

/-- Telescoping over consecutive cells: for `j < N` the level-`n` cell
indicators with index in `Ico j N` sum to the single half-endpoint indicator
of `[stepIntervalLeft n j, stepIntervalLeft n N]`.  It is instantiated at
the whole cell block in `stepApproximant_le_one` and at the plateau block
`Ico (approximationDegree k) (2 ^ (k + 1))` in `stepApproximant_apply_zero`. -/
theorem sum_halfEndpointIntervalIndicator_Ico {n j N : ℕ} (hjN : j < N) (x : ℝ) :
    (∑ m ∈ Ico j N,
        halfEndpointIntervalIndicator (stepIntervalLeft n m)
          (stepIntervalRight n m) x) =
      halfEndpointIntervalIndicator (stepIntervalLeft n j)
        (stepIntervalLeft n N) x := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hj : j = N
      · subst j
        simp [stepIntervalRight_eq_left_succ]
      · have hjlt : j < N := by omega
        rw [sum_Ico_succ_top (by omega), ih hjlt]
        rw [stepIntervalRight_eq_left_succ]
        exact halfEndpointIntervalIndicator_add_adjacent
          (stepIntervalLeft_strictMono n hjlt)
          (stepIntervalLeft_strictMono n (Nat.lt_succ_self N)) x

/-- Abel summation, tail form, for a weighted sum of level-`n` cell
indicators with `0 < N`: the sum over `range N` equals `w 0` times the
indicator of the whole block `[stepIntervalLeft n 0, stepIntervalLeft n N]`
plus the increments `w j - w (j - 1)` against the tail blocks
`[stepIntervalLeft n j, stepIntervalLeft n N]`.  This is the rewriting used
by `weighted_step_sum_monotoneOn_Iio`. -/
theorem weighted_step_sum_eq_tail_sum (n N : ℕ) (hN : 0 < N)
    (w : ℕ → ℝ) (x : ℝ) :
    (∑ m ∈ range N, w m *
        halfEndpointIntervalIndicator (stepIntervalLeft n m)
          (stepIntervalRight n m) x) =
      w 0 * halfEndpointIntervalIndicator (stepIntervalLeft n 0)
          (stepIntervalLeft n N) x +
        ∑ j ∈ Ico 1 N, (w j - w (j - 1)) *
          halfEndpointIntervalIndicator (stepIntervalLeft n j)
            (stepIntervalLeft n N) x := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [stepIntervalRight_eq_left_succ]
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
        rw [sum_range_succ, ih hNpos, sum_Ico_succ_top (by omega)]
        have htail0 := halfEndpointIntervalIndicator_add_adjacent
          (stepIntervalLeft_strictMono n hNpos)
          (stepIntervalLeft_strictMono n (Nat.lt_succ_self N)) x
        have htail (j : ℕ) (hj : j ∈ Finset.Ico 1 N) :
            halfEndpointIntervalIndicator (stepIntervalLeft n j)
                (stepIntervalLeft n (N + 1)) x =
              halfEndpointIntervalIndicator (stepIntervalLeft n j)
                  (stepIntervalLeft n N) x +
                halfEndpointIntervalIndicator (stepIntervalLeft n N)
                  (stepIntervalLeft n (N + 1)) x := by
          have hjlt : j < N := (Finset.mem_Ico.mp hj).2
          exact (halfEndpointIntervalIndicator_add_adjacent
            (stepIntervalLeft_strictMono n hjlt)
            (stepIntervalLeft_strictMono n (Nat.lt_succ_self N)) x).symm
        have hsum :
            (∑ j ∈ Finset.Ico 1 N, (w j - w (j - 1)) *
              halfEndpointIntervalIndicator (stepIntervalLeft n j)
                (stepIntervalLeft n (N + 1)) x) =
              (∑ j ∈ Finset.Ico 1 N, (w j - w (j - 1)) *
                halfEndpointIntervalIndicator (stepIntervalLeft n j)
                  (stepIntervalLeft n N) x) +
              (∑ j ∈ Finset.Ico 1 N, (w j - w (j - 1))) *
                halfEndpointIntervalIndicator (stepIntervalLeft n N)
                  (stepIntervalLeft n (N + 1)) x := by
          rw [Finset.sum_congr rfl (fun j hj => by rw [htail j hj, mul_add]),
            Finset.sum_add_distrib, Finset.sum_mul]
        have htel : (∑ j ∈ Finset.Ico 1 N, (w j - w (j - 1))) = w (N - 1) - w 0 := by
          rw [sum_Ico_eq_sum_range]
          convert Finset.sum_range_sub w (N - 1) using 1
          · apply Finset.sum_congr rfl
            intro j hj
            congr 2 <;> omega
        rw [hsum, htel]
        rw [← htail0]
        have hNm1 : N - 1 + 1 = N := by omega
        rw [show w (N - 1) = w (N - 1 + 1 - 1) by
          apply congrArg w
          omega]
        rw [hNm1]
        rw [stepIntervalRight_eq_left_succ]
        ring

/-- Abel summation, prefix form, for the same weighted sum with `0 < N`: it
equals `w (N - 1)` times the indicator of the whole block plus the decrements
`w j - w (j + 1)` against the prefix blocks
`[stepIntervalLeft n 0, stepIntervalLeft n (j + 1)]`.  This is the rewriting
used by `weighted_step_sum_antitoneOn_Ioi`. -/
theorem weighted_step_sum_eq_prefix_sum (n N : ℕ) (hN : 0 < N)
    (w : ℕ → ℝ) (x : ℝ) :
    (∑ m ∈ range N, w m *
        halfEndpointIntervalIndicator (stepIntervalLeft n m)
          (stepIntervalRight n m) x) =
      w (N - 1) * halfEndpointIntervalIndicator (stepIntervalLeft n 0)
          (stepIntervalLeft n N) x +
        ∑ j ∈ Finset.Ico 0 (N - 1), (w j - w (j + 1)) *
          halfEndpointIntervalIndicator (stepIntervalLeft n 0)
            (stepIntervalLeft n (j + 1)) x := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [stepIntervalRight_eq_left_succ]
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
        rw [sum_range_succ, ih hNpos]
        have htail0 := halfEndpointIntervalIndicator_add_adjacent
          (stepIntervalLeft_strictMono n hNpos)
          (stepIntervalLeft_strictMono n (Nat.lt_succ_self N)) x
        have hsplit :
            (∑ j ∈ Finset.Ico 0 N, (w j - w (j + 1)) *
              halfEndpointIntervalIndicator (stepIntervalLeft n 0)
                (stepIntervalLeft n (j + 1)) x) =
              (∑ j ∈ Finset.Ico 0 (N - 1), (w j - w (j + 1)) *
                halfEndpointIntervalIndicator (stepIntervalLeft n 0)
                  (stepIntervalLeft n (j + 1)) x) +
                (w (N - 1) - w N) *
                  halfEndpointIntervalIndicator (stepIntervalLeft n 0)
                    (stepIntervalLeft n N) x := by
          have hNm1 : N - 1 + 1 = N := by omega
          simpa only [hNm1] using Finset.sum_Ico_succ_top (show 0 ≤ N - 1 by omega)
            (fun j => (w j - w (j + 1)) *
              halfEndpointIntervalIndicator (stepIntervalLeft n 0)
                (stepIntervalLeft n (j + 1)) x)
        rw [show N + 1 - 1 = N by omega, hsplit, ← htail0,
          stepIntervalRight_eq_left_succ]
        ring

/-- A weighted sum of level-`n` cell indicators is monotone on `Iio 0` when
the weights are nonnegative, the increments `w (j - 1) ≤ w j` hold for
`1 ≤ j < N` below the cut index `J`, and both `stepIntervalLeft n J` and
`stepIntervalLeft n N` are nonnegative, so that the cells whose weights may
fall lie to the right of `0`.  Used with `J = 2 ^ (k + 1)` in
`stepApproximant_monotoneOn_Iio`. -/
theorem weighted_step_sum_monotoneOn_Iio (n N J : ℕ) (hN : 0 < N)
    (w : ℕ → ℝ) (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_mono : ∀ j ∈ Finset.Ico 1 N, j < J → w (j - 1) ≤ w j)
    (hcut : 0 ≤ stepIntervalLeft n J)
    (hboundary : 0 ≤ stepIntervalLeft n N) :
    MonotoneOn
      (fun x => ∑ m ∈ range N, w m *
        halfEndpointIntervalIndicator (stepIntervalLeft n m)
          (stepIntervalRight n m) x) (Set.Iio 0) := by
  intro x hx y hy hxy
  change (∑ m ∈ range N, w m *
      halfEndpointIntervalIndicator (stepIntervalLeft n m)
        (stepIntervalRight n m) x) ≤
    ∑ m ∈ range N, w m *
      halfEndpointIntervalIndicator (stepIntervalLeft n m)
        (stepIntervalRight n m) y
  rw [weighted_step_sum_eq_tail_sum n N hN w x,
    weighted_step_sum_eq_tail_sum n N hN w y]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (hw_nonneg 0)
    exact halfEndpointIntervalIndicator_monotoneOn_Iio_right
      (stepIntervalLeft_strictMono n hN)
      (lt_of_lt_of_le hx hboundary) (lt_of_lt_of_le hy hboundary) hxy
  · apply Finset.sum_le_sum
    intro j hj
    by_cases hjJ : j < J
    · apply mul_le_mul_of_nonneg_left
      · exact halfEndpointIntervalIndicator_monotoneOn_Iio_right
          (stepIntervalLeft_strictMono n (Finset.mem_Ico.mp hj).2)
          (lt_of_lt_of_le hx hboundary) (lt_of_lt_of_le hy hboundary) hxy
      · exact sub_nonneg.mpr (hw_mono j hj hjJ)
    · have hb : stepIntervalLeft n J ≤ stepIntervalLeft n j :=
        (stepIntervalLeft_strictMono n).monotone (by omega)
      rw [halfEndpointIntervalIndicator_eq_zero_of_lt_left
          (stepIntervalLeft_strictMono n (Finset.mem_Ico.mp hj).2)
          (lt_of_lt_of_le hx (hcut.trans hb)),
        halfEndpointIntervalIndicator_eq_zero_of_lt_left
          (stepIntervalLeft_strictMono n (Finset.mem_Ico.mp hj).2)
          (lt_of_lt_of_le hy (hcut.trans hb))]

/-- Mirror of `weighted_step_sum_monotoneOn_Iio`: the weighted sum is
antitone on `Ioi 0` when the weights are nonnegative, the decrements
`w (j + 1) ≤ w j` hold for `J ≤ j < N - 1`, and both `stepIntervalLeft n J`
and `stepIntervalLeft n 0` are nonpositive.  Used with
`J = approximationDegree k` in `stepApproximant_antitoneOn_Ioi`. -/
theorem weighted_step_sum_antitoneOn_Ioi (n N J : ℕ) (hN : 0 < N)
    (w : ℕ → ℝ) (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_anti : ∀ j ∈ Finset.Ico 0 (N - 1), J ≤ j → w (j + 1) ≤ w j)
    (hcut : stepIntervalLeft n J ≤ 0)
    (hboundary : stepIntervalLeft n 0 ≤ 0) :
    AntitoneOn
      (fun x => ∑ m ∈ range N, w m *
        halfEndpointIntervalIndicator (stepIntervalLeft n m)
          (stepIntervalRight n m) x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change (∑ m ∈ range N, w m *
      halfEndpointIntervalIndicator (stepIntervalLeft n m)
        (stepIntervalRight n m) y) ≤
    ∑ m ∈ range N, w m *
      halfEndpointIntervalIndicator (stepIntervalLeft n m)
        (stepIntervalRight n m) x
  rw [weighted_step_sum_eq_prefix_sum n N hN w x,
    weighted_step_sum_eq_prefix_sum n N hN w y]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (hw_nonneg (N - 1))
    exact halfEndpointIntervalIndicator_antitoneOn_Ioi_left
      (stepIntervalLeft_strictMono n hN)
      (lt_of_le_of_lt hboundary hx) (lt_of_le_of_lt hboundary hy) hxy
  · apply Finset.sum_le_sum
    intro j hj
    by_cases hJj : J ≤ j
    · apply mul_le_mul_of_nonneg_left
      · exact halfEndpointIntervalIndicator_antitoneOn_Ioi_left
          (stepIntervalLeft_strictMono n (by omega))
          (lt_of_le_of_lt hboundary hx) (lt_of_le_of_lt hboundary hy) hxy
      · exact sub_nonneg.mpr (hw_anti j hj hJj)
    · have hb : stepIntervalLeft n (j + 1) ≤ stepIntervalLeft n J :=
        (stepIntervalLeft_strictMono n).monotone (by omega)
      rw [halfEndpointIntervalIndicator_eq_zero_of_right_lt
          (stepIntervalLeft_strictMono n (by omega))
          (lt_of_le_of_lt (hb.trans hcut) hx),
        halfEndpointIntervalIndicator_eq_zero_of_right_lt
          (stepIntervalLeft_strictMono n (by omega))
          (lt_of_le_of_lt (hb.trans hcut) hy)]

/-- The step approximant `φ_n` is monotone on the negative half-line
`Iio 0`, for every `n`.  Together with `stepApproximant_antitoneOn_Ioi` this
supplies the unimodality hypotheses of
`tendsto_of_unimodal_of_intervalIntegral_tendsto`. -/
theorem stepApproximant_monotoneOn_Iio (n : ℕ) :
    MonotoneOn (stepApproximant n) (Set.Iio 0) := by
  cases n with
  | zero =>
      intro x hx y hy hxy
      rw [stepApproximant_zero, stepApproximant_zero]
      exact halfEndpointIntervalIndicator_monotoneOn_Iio_right (by norm_num)
        (by norm_num at hy ⊢; linarith) (by norm_num at hy ⊢; linarith) hxy
  | succ k =>
      let L : ℕ := 2 ^ (k + 1)
      let N : ℕ := approximationDegree (k + 1) + 1
      let w : ℕ → ℝ := fun m => ((approximationPolynomial (k + 1)).coeff m : ℝ)
      have hN : 0 < N := by simp [N]
      have hw_nonneg : ∀ j, 0 ≤ w j := fun j => by positivity
      have hw_mono : ∀ j ∈ Finset.Ico 1 N, j < L → w (j - 1) ≤ w j := by
        intro j hj hjL
        dsimp [w]
        rw [approximationPolynomial_succ_product]
        exact_mod_cast coeff_mul_geometric_monotone_before (approximationPolynomial k)
          (show j - 1 ≤ j by omega) hjL
      have hgL : approximationDegree k < L := by
        dsimp [L]
        have h := approximationDegree_eq k
        omega
      have hcut : 0 ≤ stepIntervalLeft (k + 1) L := by
        unfold stepIntervalLeft
        rw [approximationDegree_succ]
        apply div_nonneg
        · have heq : (approximationDegree k : ℝ) + k + 2 = L := by
            exact_mod_cast approximationDegree_eq k
          push_cast
          linarith
        · positivity
      have hboundary : 0 ≤ stepIntervalLeft (k + 1) N := by
        unfold stepIntervalLeft
        apply div_nonneg
        · dsimp [N]
          push_cast
          have hg : (0 : ℝ) ≤ approximationDegree (k + 1) := by positivity
          linarith
        · positivity
      intro x hx y hy hxy
      unfold stepApproximant
      change _ * (∑ m ∈ range N, w m *
        halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
          (stepIntervalRight (k + 1) m) x) ≤
        _ * (∑ m ∈ range N, w m *
          halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
            (stepIntervalRight (k + 1) m) y)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact weighted_step_sum_monotoneOn_Iio (k + 1) N L hN w hw_nonneg
        hw_mono hcut hboundary hx hy hxy

/-- The step approximant `φ_n` is antitone on the positive half-line
`Ioi 0`, for every `n`.  Only the open ray is claimed; `0` itself carries the
peak value `1` recorded by `stepApproximant_apply_zero`. -/
theorem stepApproximant_antitoneOn_Ioi (n : ℕ) :
    AntitoneOn (stepApproximant n) (Set.Ioi 0) := by
  cases n with
  | zero =>
      intro x hx y hy hxy
      rw [stepApproximant_zero, stepApproximant_zero]
      exact halfEndpointIntervalIndicator_antitoneOn_Ioi_left (by norm_num)
        (by norm_num at hx ⊢; linarith) (by norm_num at hy ⊢; linarith) hxy
  | succ k =>
      let L : ℕ := 2 ^ (k + 1)
      let N : ℕ := approximationDegree (k + 1) + 1
      let J : ℕ := approximationDegree k
      let w : ℕ → ℝ := fun m => ((approximationPolynomial (k + 1)).coeff m : ℝ)
      have hN : 0 < N := by simp [N]
      have hw_nonneg : ∀ j, 0 ≤ w j := fun j => by positivity
      have hw_anti : ∀ j ∈ Finset.Ico 0 (N - 1), J ≤ j → w (j + 1) ≤ w j := by
        intro j hj hJj
        dsimp [w, J] at hJj ⊢
        rw [approximationPolynomial_succ_product]
        exact_mod_cast coeff_mul_geometric_antitone_after (approximationPolynomial k)
          (by rw [approximationPolynomial_natDegree]; exact hJj)
          (show j ≤ j + 1 by omega)
      have hgL : approximationDegree k < L := by
        dsimp [L]
        have h := approximationDegree_eq k
        omega
      have hcut : stepIntervalLeft (k + 1) J ≤ 0 := by
        unfold stepIntervalLeft
        rw [approximationDegree_succ]
        apply div_nonpos_of_nonpos_of_nonneg
        · dsimp [J]
          push_cast
          have hk : (0 : ℝ) ≤ k := by positivity
          linarith
        · positivity
      have hboundary : stepIntervalLeft (k + 1) 0 ≤ 0 := by
        unfold stepIntervalLeft
        apply div_nonpos_of_nonpos_of_nonneg
        · push_cast
          have hg : (0 : ℝ) ≤ approximationDegree (k + 1) := by positivity
          linarith
        · positivity
      intro x hx y hy hxy
      unfold stepApproximant
      change _ * (∑ m ∈ range N, w m *
        halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
          (stepIntervalRight (k + 1) m) y) ≤
        _ * (∑ m ∈ range N, w m *
          halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
            (stepIntervalRight (k + 1) m) x)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact weighted_step_sum_antitoneOn_Ioi (k + 1) N J hN w hw_nonneg
        hw_anti hcut hboundary hx hy hxy

/-- Normalization identity for the height of `φ_(k+1)`: its prefactor
`2 ^ (k + 1) / 2 ^ (k + 2).choose 2` times the plateau value
`(approximationPolynomial k).eval 1` is exactly `1`.  This is the closing
step of `stepApproximant_le_one`; `stepApproximant_apply_zero` re-derives the
same identity inline instead of invoking this lemma. -/
theorem stepScale_mul_previous_eval_one (k : ℕ) :
    (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ ((k + 2).choose 2) *
      (((approximationPolynomial k).eval 1 : ℕ) : ℝ) = 1 := by
  rw [approximationPolynomial_eval_one]
  have hchoose : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, show 2 = 1 + 1 by omega,
      Nat.choose_succ_succ]
    simp [Nat.choose_one_right]
    omega
  rw [hchoose, pow_add]
  push_cast
  field_simp
  rw [pow_add, pow_succ]
  ring

/-- Every step approximant is bounded above by `1` at every real point.
With `stepApproximant_nonneg` this gives `stepApproximant_mem_Icc`, and it
discharges the hypothesis of `polynomialAtomMass_le_cellWidth`. -/
theorem stepApproximant_le_one (n : ℕ) (x : ℝ) : stepApproximant n x ≤ 1 := by
  cases n with
  | zero =>
      rw [stepApproximant_zero]
      exact halfEndpointIntervalIndicator_le_one _ _ _
  | succ k =>
      let N : ℕ := approximationDegree (k + 1) + 1
      let c : ℝ := (((approximationPolynomial k).eval 1 : ℕ) : ℝ)
      have hN : 0 < N := by simp [N]
      have hc : 0 ≤ c := by positivity
      have hsum :
          (∑ m ∈ range N, ((approximationPolynomial (k + 1)).coeff m : ℝ) *
            halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
              (stepIntervalRight (k + 1) m) x) ≤ c := by
        calc
          _ ≤ ∑ m ∈ range N, c *
                halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
                  (stepIntervalRight (k + 1) m) x := by
              apply Finset.sum_le_sum
              intro m hm
              apply mul_le_mul_of_nonneg_right
              · dsimp [c]
                exact_mod_cast approximationPolynomial_succ_coeff_le_eval_one k m
              · exact halfEndpointIntervalIndicator_nonneg _ _ _
          _ = c * (∑ m ∈ range N,
                halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
                  (stepIntervalRight (k + 1) m) x) := by rw [Finset.mul_sum]
          _ = c * halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) 0)
                (stepIntervalLeft (k + 1) N) x := by
              congr 1
              simpa only [Nat.Ico_zero_eq_range] using
                sum_halfEndpointIntervalIndicator_Ico (n := k + 1) (j := 0) (N := N) hN x
          _ ≤ c := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left
                (halfEndpointIntervalIndicator_le_one _ _ _) hc
      unfold stepApproximant
      change (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ ((k + 2).choose 2) *
        (∑ m ∈ range N, ((approximationPolynomial (k + 1)).coeff m : ℝ) *
          halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
            (stepIntervalRight (k + 1) m) x) ≤ 1
      calc
        _ ≤ (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ ((k + 2).choose 2) * c :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := by
          dsimp [c]
          exact stepScale_mul_previous_eval_one k

/-- Every histogram approximant takes values in the unit interval. -/
theorem stepApproximant_mem_Icc (n : ℕ) (x : ℝ) :
    stepApproximant n x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨stepApproximant_nonneg n x, stepApproximant_le_one n x⟩

/-- Absolute-value form of `stepApproximant_mem_Icc`. -/
theorem abs_stepApproximant_le_one (n : ℕ) (x : ℝ) :
    |stepApproximant n x| ≤ 1 := by
  rw [abs_of_nonneg (stepApproximant_nonneg n x)]
  exact stepApproximant_le_one n x

/-- The mass of every polynomial atom is at most the width of its histogram
cell.  This closes the conditional estimate from `StepMeasureBridge` using
the global height bound. -/
theorem polynomialAtomMass_le_cellWidth_unconditional (n m : ℕ) :
    ((approximationPolynomial n).coeff m : ℝ) /
        (2 : ℝ) ^ ((n + 1).choose 2) ≤ 1 / (2 : ℝ) ^ n :=
  polynomialAtomMass_le_cellWidth n m
    (stepApproximant_le_one n (polynomialAtomLocation n m))

/-- Every step approximant takes its normalized peak value one at the origin. -/
@[simp] theorem stepApproximant_apply_zero (n : ℕ) : stepApproximant n 0 = 1 := by
  cases n with
  | zero =>
      rw [stepApproximant_zero]
      norm_num [halfEndpointIntervalIndicator]
  | succ k =>
      let L : ℕ := 2 ^ (k + 1)
      let N : ℕ := approximationDegree (k + 1) + 1
      let J : ℕ := approximationDegree k
      let c : ℝ := (((approximationPolynomial k).eval 1 : ℕ) : ℝ)
      have hJL : J < L := by
        dsimp [J, L]
        have h := approximationDegree_eq k
        omega
      have hLN : L ≤ N := by
        dsimp [L, N]
        rw [approximationDegree_succ_add]
        omega
      have hleft : stepIntervalLeft (k + 1) J < 0 := by
        unfold stepIntervalLeft
        rw [approximationDegree_succ]
        apply div_neg_of_neg_of_pos
        · dsimp [J]
          push_cast
          have hk : (0 : ℝ) ≤ k := by positivity
          linarith
        · positivity
      have hright : 0 < stepIntervalLeft (k + 1) L := by
        unfold stepIntervalLeft
        rw [approximationDegree_succ]
        apply (div_pos (by
          have heq : (approximationDegree k : ℝ) + k + 2 = L := by
            exact_mod_cast approximationDegree_eq k
          push_cast
          linarith) (by positivity))
      have houtside (m : ℕ) (hmN : m ∈ range N) (hm : m ∉ Finset.Ico J L) :
          ((approximationPolynomial (k + 1)).coeff m : ℝ) *
            halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
              (stepIntervalRight (k + 1) m) 0 = 0 := by
        rw [Finset.mem_Ico, not_and_or] at hm
        rcases hm with hm | hm
        · have hmj : m + 1 ≤ J := by omega
          have hb : stepIntervalRight (k + 1) m ≤ stepIntervalLeft (k + 1) J := by
            rw [stepIntervalRight_eq_left_succ]
            exact (stepIntervalLeft_strictMono (k + 1)).monotone hmj
          rw [halfEndpointIntervalIndicator_eq_zero_of_right_lt
            (stepIntervalLeft_lt_right _ _) (lt_of_le_of_lt hb hleft)]
          simp
        · have hb : stepIntervalLeft (k + 1) L ≤ stepIntervalLeft (k + 1) m :=
            (stepIntervalLeft_strictMono (k + 1)).monotone (by omega)
          rw [halfEndpointIntervalIndicator_eq_zero_of_lt_left
            (stepIntervalLeft_lt_right _ _) (lt_of_lt_of_le hright hb)]
          simp
      have hcoeff (m : ℕ) (hm : m ∈ Finset.Ico J L) :
          ((approximationPolynomial (k + 1)).coeff m : ℝ) = c := by
        dsimp [c]
        rw [approximationPolynomial_succ_product]
        norm_cast
        apply coeff_mul_geometric_eq_eval_one
        · rw [approximationPolynomial_natDegree]
          exact (Finset.mem_Ico.mp hm).1
        · exact (Finset.mem_Ico.mp hm).2
      unfold stepApproximant
      change (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ ((k + 1 + 1).choose 2) *
        (∑ m ∈ range N, ((approximationPolynomial (k + 1)).coeff m : ℝ) *
          halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) m)
            (stepIntervalRight (k + 1) m) 0) = 1
      rw [← Finset.sum_subset
        (show Finset.Ico J L ⊆ range N by
          intro m hm
          rw [Finset.mem_range]
          exact (Finset.mem_Ico.mp hm).2.trans_le hLN)
        houtside]
      rw [Finset.sum_congr rfl (fun m hm => by rw [hcoeff m hm])]
      rw [← Finset.mul_sum, sum_halfEndpointIntervalIndicator_Ico hJL]
      have hindicator : halfEndpointIntervalIndicator (stepIntervalLeft (k + 1) J)
          (stepIntervalLeft (k + 1) L) 0 = 1 := by
        rw [halfEndpointIntervalIndicator, if_neg]
        · rw [if_pos ⟨hleft, hright⟩]
        · exact not_or_intro hleft.ne' hright.ne
      rw [hindicator, mul_one]
      dsimp [c]
      rw [approximationPolynomial_eval_one]
      have hchoose : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 by omega, show 2 = 1 + 1 by omega,
          Nat.choose_succ_succ]
        simp [Nat.choose_one_right]
        omega
      rw [show k + 1 + 1 = k + 2 by omega, hchoose, pow_add]
      push_cast
      field_simp
      rw [pow_add, pow_succ]
      ring

/-- Along any filter, convergence of all interval integrals upgrades to
pointwise convergence on the negative half-line for a family monotone there. -/
theorem tendsto_of_monotoneOn_Iio_of_intervalIntegral_tendsto
    {ι : Type*} {l : Filter ι}
    (f : ι → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ)
    (hx : x < 0)
    (hfmono : ∀ n, MonotoneOn (f n) (Iio 0))
    (hfint : ∀ n a b, IntervalIntegrable (f n) volume a b)
    (hgcont : Continuous g)
    (hint : ∀ a b, Tendsto (fun n => ∫ y in a..b, f n y) l
      (𝓝 (∫ y in a..b, g y))) :
    Tendsto (fun n => f n x) l (𝓝 (g x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hgcont.continuousAt (ε / 4) (by positivity)
  let d : ℝ := min (δ / 2) (-x / 2)
  have hd : 0 < d := lt_min (half_pos hδ) (half_pos (neg_pos.mpr hx))
  have hdx : x + d < 0 := by
    have hdle : d ≤ -x / 2 := min_le_right _ _
    linarith
  have hdδ : d < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hgclose : ∀ y ∈ Icc (x - d) (x + d), |g y - g x| < ε / 4 := by
    intro y hy
    have hydist : dist y x < δ := by
      rw [Real.dist_eq]
      have : |y - x| ≤ d := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      exact this.trans_lt hdδ
    simpa [Real.dist_eq] using hcont hydist
  have hgleftLower : d * (g x - ε / 4) ≤ ∫ y in (x - d)..x, g y := by
    rw [show d * (g x - ε / 4) = ∫ _ in (x - d)..x, (g x - ε / 4) by
      simp [intervalIntegral.integral_const]; ring]
    apply intervalIntegral.integral_mono_on (by linarith : x - d ≤ x)
      (continuous_const.intervalIntegrable _ _)
      (hgcont.intervalIntegrable _ _)
    intro y hy
    have h := hgclose y ⟨hy.1, hy.2.trans (le_add_of_nonneg_right hd.le)⟩
    rw [abs_lt] at h
    linarith
  have hgrightUpper : (∫ y in x..(x + d), g y) ≤ d * (g x + ε / 4) := by
    rw [show d * (g x + ε / 4) = ∫ _ in x..(x + d), (g x + ε / 4) by
      simp [intervalIntegral.integral_const]; ring]
    apply intervalIntegral.integral_mono_on (le_add_of_nonneg_right hd.le)
      (hgcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    have h := hgclose y ⟨(sub_le_self x hd.le).trans hy.1, hy.2⟩
    rw [abs_lt] at h
    linarith
  have hleft := (hint (x - d) x).div_const d
  have hright := (hint x (x + d)).div_const d
  have hleft_eventually := (Metric.tendsto_nhds.1 hleft)
    (ε / 4) (by positivity)
  have hright_eventually := (Metric.tendsto_nhds.1 hright)
    (ε / 4) (by positivity)
  filter_upwards [hleft_eventually, hright_eventually] with n havgl havgr
  rw [Real.dist_eq, abs_lt] at havgl havgr ⊢
  have hleftMono : (∫ y in (x - d)..x, f n y) ≤ d * f n x := by
    have hconst : (∫ _ in (x - d)..x, f n x) = d * f n x := by
      simp [intervalIntegral.integral_const]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (by linarith : x - d ≤ x)
      (hfint n _ _) (continuous_const.intervalIntegrable _ _)
    intro y hy
    exact hfmono n (by show y < 0; linarith [hy.2, hx]) hx hy.2
  have hrightMono : d * f n x ≤ ∫ y in x..(x + d), f n y := by
    have hconst : (∫ _ in x..(x + d), f n x) = d * f n x := by
      simp [intervalIntegral.integral_const]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (le_add_of_nonneg_right hd.le)
      (continuous_const.intervalIntegrable _ _) (hfint n _ _)
    intro y hy
    exact hfmono n hx (by show y < 0; linarith [hy.2, hdx]) hy.1
  constructor
  · have : g x - ε / 2 < (∫ y in (x - d)..x, f n y) / d := by
      have htarget : g x - ε / 4 ≤ (∫ y in (x - d)..x, g y) / d := by
        apply (le_div_iff₀ hd).2
        linarith
      linarith
    have havg_le : (∫ y in (x - d)..x, f n y) / d ≤ f n x := by
      apply (div_le_iff₀ hd).2
      simpa [mul_comm] using hleftMono
    linarith
  · have : (∫ y in x..(x + d), f n y) / d < g x + ε / 2 := by
      have htarget : (∫ y in x..(x + d), g y) / d ≤ g x + ε / 4 := by
        apply (div_le_iff₀ hd).2
        linarith
      linarith
    have hle_avg : f n x ≤ (∫ y in x..(x + d), f n y) / d := by
      apply (le_div_iff₀ hd).2
      simpa [mul_comm] using hrightMono
    linarith

/-- Arbitrary-filter pointwise convergence for even unimodal families,
deduced from convergence of interval integrals. -/
theorem tendsto_of_even_unimodal_of_intervalIntegral_tendsto
    {ι : Type*} {l : Filter ι}
    (f : ι → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmono : ∀ n, MonotoneOn (f n) (Iio 0))
    (hfeven : ∀ n x, f n (-x) = f n x)
    (hfzero : ∀ n, f n 0 = g 0)
    (hfint : ∀ n a b, IntervalIntegrable (f n) volume a b)
    (hgcont : Continuous g)
    (hgeven : ∀ x, g (-x) = g x)
    (hint : ∀ a b, Tendsto (fun n => ∫ y in a..b, f n y) l
      (𝓝 (∫ y in a..b, g y))) :
    ∀ x, Tendsto (fun n => f n x) l (𝓝 (g x)) := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact tendsto_of_monotoneOn_Iio_of_intervalIntegral_tendsto f g x hx
      hfmono hfint hgcont hint
  · subst x
    simpa only [hfzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => g 0) l (𝓝 (g 0)))
  · have hneg : -x < 0 := neg_neg_of_pos hx
    have hlim := tendsto_of_monotoneOn_Iio_of_intervalIntegral_tendsto f g (-x) hneg
      hfmono hfint hgcont hint
    simpa only [hfeven, hgeven] using hlim

/-- Positive-half-line counterpart of
`tendsto_of_monotoneOn_Iio_of_intervalIntegral_tendsto`. -/
theorem tendsto_of_antitoneOn_Ioi_of_intervalIntegral_tendsto
    {ι : Type*} {l : Filter ι}
    (f : ι → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ)
    (hx : 0 < x)
    (hfanti : ∀ n, AntitoneOn (f n) (Ioi 0))
    (hfint : ∀ n a b, IntervalIntegrable (f n) volume a b)
    (hgcont : Continuous g)
    (hint : ∀ a b, Tendsto (fun n => ∫ y in a..b, f n y) l
      (𝓝 (∫ y in a..b, g y))) :
    Tendsto (fun n => f n x) l (𝓝 (g x)) := by
  let fr : ι → ℝ → ℝ := fun n y => f n (-y)
  let gr : ℝ → ℝ := fun y => g (-y)
  have hfrmono : ∀ n, MonotoneOn (fr n) (Iio 0) := by
    intro n y hy z hz hyz
    exact hfanti n (by exact neg_pos.mpr (show z < 0 from hz))
      (by exact neg_pos.mpr (show y < 0 from hy))
      (neg_le_neg hyz)
  have hfrint : ∀ n a b, IntervalIntegrable (fr n) volume a b := by
    intro n a b
    simpa only [fr, neg_neg] using
      ((IntervalIntegrable.iff_comp_neg (f := f n) (a := -a) (b := -b)).mp
        (hfint n (-a) (-b)))
  have hgrcont : Continuous gr := hgcont.comp continuous_neg
  have hrint : ∀ a b, Tendsto (fun n => ∫ y in a..b, fr n y) l
      (𝓝 (∫ y in a..b, gr y)) := by
    intro a b
    simpa only [fr, gr, intervalIntegral.integral_comp_neg] using hint (-b) (-a)
  have hlim := tendsto_of_monotoneOn_Iio_of_intervalIntegral_tendsto
    fr gr (-x) (neg_neg_of_pos hx) hfrmono hfrint hgrcont hrint
  simpa only [fr, gr, neg_neg] using hlim

/-- Arbitrary-filter pointwise convergence for a family increasing to zero
and decreasing after zero, from convergence of all interval integrals. -/
theorem tendsto_of_unimodal_of_intervalIntegral_tendsto
    {ι : Type*} {l : Filter ι}
    (f : ι → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmono : ∀ n, MonotoneOn (f n) (Iio 0))
    (hfanti : ∀ n, AntitoneOn (f n) (Ioi 0))
    (hfzero : ∀ n, f n 0 = g 0)
    (hfint : ∀ n a b, IntervalIntegrable (f n) volume a b)
    (hgcont : Continuous g)
    (hint : ∀ a b, Tendsto (fun n => ∫ y in a..b, f n y) l
      (𝓝 (∫ y in a..b, g y))) :
    ∀ x, Tendsto (fun n => f n x) l (𝓝 (g x)) := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact tendsto_of_monotoneOn_Iio_of_intervalIntegral_tendsto f g x hx
      hfmono hfint hgcont hint
  · subst x
    simpa only [hfzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => g 0) l (𝓝 (g 0)))
  · exact tendsto_of_antitoneOn_Ioi_of_intervalIntegral_tendsto f g x hx
      hfanti hfint hgcont hint

/-- Theorem 2 of arXiv:1702.05442: the corrected half-endpoint step approximants converge
pointwise to Rvachev's up function. -/
theorem stepApproximant_tendsto_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    Tendsto (fun n : ℕ => stepApproximant n x) atTop (𝓝 (rvachevUp F x)) := by
  exact tendsto_of_unimodal_of_intervalIntegral_tendsto
    stepApproximant (rvachevUp F)
    stepApproximant_monotoneOn_Iio
    stepApproximant_antitoneOn_Ioi
    (fun n => by rw [stepApproximant_apply_zero, rvachev_zero F hF])
    stepApproximant_intervalIntegrable
    (rvachev_contDiff F hF).continuous
    (intervalIntegral_stepApproximant_tendsto F hF) x

/-- Canonical specialization of Theorem 2. -/
theorem stepApproximant_tendsto_fabius (x : ℝ) :
    Tendsto (fun n : ℕ => stepApproximant n x) atTop
      (𝓝 (rvachevUp fabius x)) :=
  stepApproximant_tendsto_rvachevUp fabius fabius_spec x

end Fabius
