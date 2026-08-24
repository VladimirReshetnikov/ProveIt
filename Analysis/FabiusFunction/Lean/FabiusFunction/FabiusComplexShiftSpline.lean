import FabiusFunction.FabiusDiscreteLimitComplexShift
import FabiusFunction.FabiusDiscreteLimitToeplitz
import FabiusFunction.FabiusUniformSpline
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false

open scoped BigOperators Topology
open Finset Filter

namespace Fabius

noncomputable section

/-- The fixed-cutoff complex translation of the centered finite Fabius spline. -/
def fabiusComplexShiftSpline (p : ℕ) (q : ℂ) (x : ℝ) : ℂ :=
  ((-1 : ℂ) ^ p /
      ((2 : ℂ) ^ p.choose 2 * (p.factorial : ℂ))) *
    ∑ r ∈ Finset.range (fabiusDiscreteLimitRangeLength x p),
      (-1 : ℂ) ^ thueMorseBit r *
        ((r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + q) ^ p

private theorem neg_one_pow_thueMorseBit_complex (r : ℕ) :
    (-1 : ℂ) ^ thueMorseBit r = (thueMorseSign r : ℂ) := by
  exact_mod_cast neg_one_pow_thueMorseBit r

/-- The literal shifted spline is the generic normalized branch evaluated at
`2^p x-q`. -/
theorem fabiusComplexShiftSpline_eq_branch (p : ℕ) (q : ℂ) (x : ℝ) :
    fabiusComplexShiftSpline p q x =
      normalizedThueMorseSplineBranch p
        (fabiusDiscreteLimitRangeLength x p)
        ((2 : ℂ) ^ p * (x : ℂ) - q) := by
  rw [fabiusComplexShiftSpline, normalizedThueMorseSplineBranch]
  simp_rw [neg_one_pow_thueMorseBit_complex]
  have hterm (r : ℕ) :
      ((r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + q) ^ p =
        (-1 : ℂ) ^ p *
          (((2 : ℂ) ^ p * (x : ℂ) - q) - (r : ℂ)) ^ p := by
    rw [show (r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + q =
        -(((2 : ℂ) ^ p * (x : ℂ) - q) - (r : ℂ)) by ring, neg_pow]
  simp_rw [hterm]
  simp_rw [show ∀ r : ℕ,
      (thueMorseSign r : ℂ) *
          ((-1 : ℂ) ^ p *
            (((2 : ℂ) ^ p * (x : ℂ) - q) - (r : ℂ)) ^ p) =
        (-1 : ℂ) ^ p *
          ((thueMorseSign r : ℂ) *
            (((2 : ℂ) ^ p * (x : ℂ) - q) - (r : ℂ)) ^ p) by
      intro r; ring]
  rw [← Finset.mul_sum]
  have hsquare : (-1 : ℂ) ^ p * (-1 : ℂ) ^ p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = (((-1 : ℂ) ^ p * (-1 : ℂ) ^ p) /
          ((2 : ℂ) ^ p.choose 2 * (p.factorial : ℂ))) *
        ∑ r ∈ range (fabiusDiscreteLimitRangeLength x p),
          (thueMorseSign r : ℂ) *
            (((2 : ℂ) ^ p * (x : ℂ) - q) - (r : ℂ)) ^ p := by ring
    _ = _ := by rw [hsquare]; ring

/-- Exact fixed-branch Taylor expansion about the centered shift `q=1/2`. -/
theorem fabiusComplexShiftSpline_eq_taylorBranches
    (p : ℕ) (q : ℂ) (x : ℝ) :
    fabiusComplexShiftSpline p q x =
      ∑ d ∈ Finset.range (p + 1),
        ((2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))) *
          ((1 / 2 : ℂ) - q) ^ (p - d) *
            normalizedThueMorseSplineBranch d
              (fabiusDiscreteLimitRangeLength x p)
              ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) := by
  rw [fabiusComplexShiftSpline_eq_branch]
  have harg :
      (2 : ℂ) ^ p * (x : ℂ) - q =
        ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) + ((1 / 2 : ℂ) - q) := by
    ring
  rw [harg, normalizedThueMorseSplineBranch_add]

/-- Difference version of the exact Taylor expansion. -/
theorem fabiusComplexShiftSpline_sub_center_eq_taylorBranches
    (p : ℕ) (q : ℂ) (x : ℝ) :
    fabiusComplexShiftSpline p q x -
        fabiusComplexShiftSpline p (1 / 2 : ℂ) x =
      ∑ d ∈ Finset.range p,
        ((2 : ℂ) ^ d.choose 2 /
            ((2 : ℂ) ^ p.choose 2 * ((p - d).factorial : ℂ))) *
          ((1 / 2 : ℂ) - q) ^ (p - d) *
            normalizedThueMorseSplineBranch d
              (fabiusDiscreteLimitRangeLength x p)
              ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) := by
  rw [fabiusComplexShiftSpline_eq_branch,
    fabiusComplexShiftSpline_eq_branch]
  have hargq :
      (2 : ℂ) ^ p * (x : ℂ) - q =
        ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) + ((1 / 2 : ℂ) - q) := by
    ring
  rw [hargq]
  convert normalizedThueMorseSplineBranch_add_sub p
    (fabiusDiscreteLimitRangeLength x p)
    ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) ((1 / 2 : ℂ) - q) using 1

/-- Conditional quantitative translation bound.  The spline module supplies
the lower-branch hypothesis unconditionally on the nonnegative half-line. -/
theorem norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp_of_bound
    (p : ℕ) (q : ℂ) (x : ℝ) (hp : 1 ≤ p)
    (hbound : ∀ d ∈ Finset.range p,
      ‖normalizedThueMorseSplineBranch d
        (fabiusDiscreteLimitRangeLength x p)
        ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2)‖ ≤ 1) :
    ‖fabiusComplexShiftSpline p q x -
        fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) *
        Real.exp ‖q - (1 / 2 : ℂ)‖ := by
  rw [fabiusComplexShiftSpline_eq_branch,
    fabiusComplexShiftSpline_eq_branch]
  have hargq :
      (2 : ℂ) ^ p * (x : ℂ) - q =
        ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) + ((1 / 2 : ℂ) - q) := by
    ring
  rw [hargq]
  have h := norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp
    p (fabiusDiscreteLimitRangeLength x p)
    ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) ((1 / 2 : ℂ) - q) hp hbound
  simpa only [norm_neg, show (1 / 2 : ℂ) - q = -(q - 1 / 2) by ring] using h

/-- Centering at `q=1/2` recovers the real uniform spline. -/
theorem fabiusComplexShiftSpline_center (p : ℕ) (x : ℝ) :
    fabiusComplexShiftSpline p (1 / 2 : ℂ) x =
      (fabiusUniformSpline p x : ℂ) := by
  rw [fabiusComplexShiftSpline, fabiusUniformSpline]
  push_cast
  simp_rw [neg_one_pow_thueMorseBit_complex]

private theorem pow_scale_sub (p d : ℕ) (hd : d ≤ p) (x : ℝ) :
    (2 : ℝ) ^ d * ((2 : ℝ) ^ (p - d) * x) = (2 : ℝ) ^ p * x := by
  calc
    (2 : ℝ) ^ d * ((2 : ℝ) ^ (p - d) * x) =
        ((2 : ℝ) ^ d * (2 : ℝ) ^ (p - d)) * x := by ring
    _ = (2 : ℝ) ^ (d + (p - d)) * x := by rw [pow_add]
    _ = (2 : ℝ) ^ p * x := by rw [Nat.add_sub_of_le hd]

/-- A lower branch at the scale-`p` cutoff is a degree-`d` centered spline
at the rescaled nonnegative argument. -/
theorem normalizedThueMorseSplineBranch_center_eq_uniformSpline
    (p d : ℕ) (hd : d ≤ p) (x : ℝ) :
    normalizedThueMorseSplineBranch d
        (fabiusDiscreteLimitRangeLength x p)
        ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) =
      (fabiusUniformSpline d ((2 : ℝ) ^ (p - d) * x) : ℂ) := by
  rw [normalizedThueMorseSplineBranch, fabiusUniformSpline]
  have hscale := pow_scale_sub p d hd x
  have hcount :
      fabiusDiscreteLimitRangeLength ((2 : ℝ) ^ (p - d) * x) d =
        fabiusDiscreteLimitRangeLength x p := by
    rw [fabiusDiscreteLimitRangeLength, fabiusDiscreteLimitRangeLength,
      hscale]
  rw [hcount]
  push_cast
  have hscaleC :
      (2 : ℂ) ^ d * ((2 : ℂ) ^ (p - d) * (x : ℂ)) =
        (2 : ℂ) ^ p * (x : ℂ) := by
    exact_mod_cast hscale
  rw [hscaleC]
  have hterm (r : ℕ) :
      (((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) - (r : ℂ)) ^ d =
        (-1 : ℂ) ^ d *
          ((r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + 1 / 2) ^ d := by
    rw [show ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2) - (r : ℂ) =
        -((r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + 1 / 2) by ring, neg_pow]
  simp_rw [hterm]
  simp_rw [show ∀ r : ℕ,
      (thueMorseSign r : ℂ) *
          ((-1 : ℂ) ^ d *
            ((r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + 1 / 2) ^ d) =
        (-1 : ℂ) ^ d *
          ((thueMorseSign r : ℂ) *
            ((r : ℂ) - (2 : ℂ) ^ p * (x : ℂ) + 1 / 2) ^ d) by
      intro r; ring]
  rw [← Finset.mul_sum]
  ring

/-- All lower branches in the complex Taylor formula have norm at most one. -/
theorem norm_normalizedThueMorseSplineBranch_center_le_one
    (p d : ℕ) (hd : d ≤ p) {x : ℝ} (hx : 0 ≤ x) :
    ‖normalizedThueMorseSplineBranch d
        (fabiusDiscreteLimitRangeLength x p)
        ((2 : ℂ) ^ p * (x : ℂ) - 1 / 2)‖ ≤ 1 := by
  rw [normalizedThueMorseSplineBranch_center_eq_uniformSpline p d hd x,
    Complex.norm_real]
  exact abs_fabiusUniformSpline_le_one d (mul_nonneg (by positivity) hx)

/-- Uniform translation bound on the nonnegative half-line. -/
theorem norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp
    (p : ℕ) (q : ℂ) {x : ℝ} (hx : 0 ≤ x) (hp : 1 ≤ p) :
    ‖fabiusComplexShiftSpline p q x -
        fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) *
        Real.exp ‖q - (1 / 2 : ℂ)‖ := by
  exact norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp_of_bound
    p q x hp (fun d hd =>
      norm_normalizedThueMorseSplineBranch_center_le_one p d
        (Nat.le_of_lt (Finset.mem_range.mp hd)) hx)

private theorem half_pow_sub_one_tendsto_zero :
    Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ (p - 1)) atTop (nhds 0) := by
  have hpow : Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ p) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hpow.comp (tendsto_sub_atTop_nat 1)

/-- A fixed complex translation is asymptotically independent of `q`. -/
theorem fabiusComplexShiftSpline_sub_center_tendsto_zero
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun p : ℕ =>
      fabiusComplexShiftSpline p q x -
        fabiusComplexShiftSpline p (1 / 2 : ℂ) x)
      atTop (nhds 0) := by
  let C : ℝ := Real.exp ‖q - (1 / 2 : ℂ)‖
  have hbound : Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ (p - 1) * C)
      atTop (nhds 0) := by
    simpa using half_pow_sub_one_tendsto_zero.mul_const C
  apply squeeze_zero_norm' (t₀ := atTop) (a := fun p : ℕ =>
    (1 / 2 : ℝ) ^ (p - 1) * C)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with p hp
    exact norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp
      p q hx hp
  · exact hbound

/-- Every fixed complex shift has the same global Fabius limit. -/
theorem fabiusComplexShiftSpline_tendsto_globalFabius
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun p : ℕ => fabiusComplexShiftSpline p q x)
      atTop (nhds (globalFabius x : ℂ)) := by
  have hcenterReal := fabiusUniformSpline_tendsto_globalFabius hx
  have hcenter : Tendsto
      (fun p : ℕ => (fabiusUniformSpline p x : ℂ))
      atTop (nhds (globalFabius x : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hcenterReal
  have hcenter' : Tendsto
      (fun p : ℕ => fabiusComplexShiftSpline p (1 / 2 : ℂ) x)
      atTop (nhds (globalFabius x : ℂ)) := by
    simpa only [fabiusComplexShiftSpline_center] using hcenter
  have hdiff := fabiusComplexShiftSpline_sub_center_tendsto_zero q hx
  have hadd := hdiff.add hcenter'
  simpa only [sub_add_cancel, zero_add] using hadd

/-- Explicit specialization for an arbitrary real shift, including irrational
ones. -/
theorem fabiusComplexShiftSpline_tendsto_globalFabius_real
    (q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun p : ℕ => fabiusComplexShiftSpline p (q : ℂ) x)
      atTop (nhds (globalFabius x : ℂ)) :=
  fabiusComplexShiftSpline_tendsto_globalFabius (q : ℂ) hx

/-- Rational-shift specialization. -/
theorem fabiusComplexShiftSpline_tendsto_globalFabius_rat
    (q : ℚ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun p : ℕ => fabiusComplexShiftSpline p (q : ℂ) x)
      atTop (nhds (globalFabius x : ℂ)) :=
  fabiusComplexShiftSpline_tendsto_globalFabius (q : ℂ) hx

/-- Gaussian-rational-shift specialization. -/
theorem fabiusComplexShiftSpline_tendsto_globalFabius_gaussianRat
    (a b : ℚ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun p : ℕ =>
      fabiusComplexShiftSpline p ((a : ℂ) + (b : ℂ) * Complex.I) x)
      atTop (nhds (globalFabius x : ℂ)) :=
  fabiusComplexShiftSpline_tendsto_globalFabius
    ((a : ℂ) + (b : ℂ) * Complex.I) hx

end

end Fabius
