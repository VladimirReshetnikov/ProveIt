import FabiusFunction.FabiusUniformSpline
import FabiusFunction.InverseQuarterAnchor
import FabiusFunction.ThueMorseMoments

/-!
# The exact quarter polynomial of the finite Fabius spline

The inverse-frontier report writes `P_n` for the density of the first `n`
centered uniform summands, shifted from `[-1,1]` to the Fabius interval.  On
`[0,1]` its displayed Thue--Morse formula is exactly the repository's
`fabiusUniformSpline (n - 1)`: both have degree `n - 1`, cutoff
`2⁻ⁿ + j 2^(1-n)`, and normalization `2^C(n,2) / (n-1)!`.  The definition
`reportFiniteFabiusApproximant` records this *one-step index shift* explicitly.
In particular, the report's `P_n` is not `fabiusUniformSpline n`.

The report's `G_n`, on the other hand, is an increasing inverse branch of
`P_n`.  There is no finite-prefix inverse with that meaning in the current
repository: `fabiusInv` is the inverse of the limiting bounded Fabius
function.  Consequently this file proves the exact local formula for `P_n`
unconditionally and states the final `G_n` identity only for a supplied local
left inverse.  This keeps the two constructions separate.

The proof is finite algebra.  At `x = 1/4 + z`, `|z| <= 2⁻ⁿ`, the cell
cutoff contains one complete Thue--Morse block of length `2^(n-3)`; at the
right endpoint it contains one additional term, whose power is zero.
Prouhet cancellation leaves only the first three surviving block moments.
The two moments just beyond the cancellation order are proved below in closed
form.  Substitution gives, for every `n >= 3`,

`P_n (1/4 + z) = 5/72 + z + 4 z^2 - (4/9) 4⁻ⁿ`.

Thus the analytic premise `IsQuarterLocalPolynomial` from
`InverseQuarterAnchor` is completely discharged for the actual finite spline;
no limiting, differentiability, or almost-everywhere argument is used.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

/-! ## The report's indexing convention -/

/-- The finite approximant called `P_n` in the inverse-frontier report.

The subtraction makes the name total at `n = 0`; all mathematical uses below
assume `3 <= n`.  The important content is the deliberate index shift
`P_n = fabiusUniformSpline (n - 1)`. -/
def reportFiniteFabiusApproximant (n : ℕ) (x : ℝ) : ℝ :=
  fabiusUniformSpline (n - 1) x

/-- Successor form of the report/repository index correspondence:
`P_(p+1)` is the degree-`p` repository spline. -/
@[simp]
theorem reportFiniteFabiusApproximant_succ (p : ℕ) :
    reportFiniteFabiusApproximant (p + 1) = fabiusUniformSpline p := by
  funext x
  simp [reportFiniteFabiusApproximant]

/-- On the fundamental interval, the report's `P_n` is the
midpoint-corrected CDF of the first `n-1` positive uniform coordinates.
This is the repository's probabilistic realization of the same spline; the
report instead obtains it as the left-half density of `n` centered uniforms. -/
theorem reportFiniteFabiusApproximant_eq_centeredPartialCDF
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    reportFiniteFabiusApproximant n x =
      ProbabilityRepresentation.uniformCenteredPartialCDF (n - 1) x := by
  exact ProbabilityRepresentation.fabiusUniformSpline_eq_centeredPartialCDF
    (n - 1) (by omega) hx

/-! ## The first two moments beyond Prouhet cancellation -/

private lemma cast_choose_add_two_left (m : ℕ) :
    ((Nat.choose (m + 2) m : ℕ) : ℝ) =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 := by
  have hsym : Nat.choose (m + 2) m = Nat.choose (m + 2) 2 :=
    Nat.choose_symm_of_eq_add rfl
  rw [hsym, Nat.cast_choose_two ℝ]
  push_cast
  ring

private lemma cast_choose_add_three_left (m : ℕ) :
    ((Nat.choose (m + 3) m : ℕ) : ℝ) =
      ((m : ℝ) + 3) * ((m : ℝ) + 2) * ((m : ℝ) + 1) / 6 := by
  have hsym : Nat.choose (m + 3) m = Nat.choose (m + 3) 3 :=
    Nat.choose_symm_of_eq_add rfl
  rw [hsym]
  have hnat :
      Nat.choose (m + 3) 3 * 3 =
        Nat.choose (m + 3) 2 * (m + 3 - 2) := by
    simpa using Nat.choose_succ_right_eq (m + 3) 2
  have hreal := congrArg (fun a : ℕ => (a : ℝ)) hnat
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hreal
  have hsub : m + 3 - 2 = m + 1 := by omega
  rw [hsub, Nat.cast_choose_two ℝ] at hreal
  push_cast at hreal ⊢
  nlinarith

/-- The real signed Thue--Morse moment one degree beyond the Prouhet threshold.

Writing `T_m(d) = sum_{r<2^m} epsilon_r r^d`, this is
`T_m(m+1) = T_m(m) (m+1)(2^m-1)/2`.  Besides driving the quarter-spline
calculation, this public form is reusable in other degree-one residual
problems. -/
theorem thueMorsePowerSumRing_add_one_real (m : ℕ) :
    thueMorsePowerSumRing ℝ m (m + 1) =
      (-1 : ℝ) ^ m * (2 : ℝ) ^ m.choose 2 * (m.factorial : ℝ) *
        (((m : ℝ) + 1) * ((2 : ℝ) ^ m - 1) / 2) := by
  induction m with
  | zero =>
      norm_num [thueMorsePowerSumRing, thueMorseSign, binaryWeight]
  | succ m ih =>
      have hzero :
          (∑ k ∈ range m,
            (Nat.choose (m + 2) k : ℝ) * (2 : ℝ) ^ k *
              thueMorsePowerSumRing ℝ m k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [thueMorsePowerSumRing_eq_zero_of_lt m k (mem_range.mp hk),
          mul_zero]
      have hchoose := cast_choose_add_two_left m
      rw [show m + 1 + 1 = m + 2 by omega,
        thueMorsePowerSumRing_succ (R := ℝ) m (m + 2),
        show m + 2 = (m + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, hzero, zero_add,
        thueMorsePowerSumRing_self, ih,
        Nat.choose_succ_self_right]
      rw [hchoose, choose_succ_two, pow_add, pow_succ,
        Nat.factorial_succ]
      push_cast
      ring

/-- The real signed Thue--Morse moment two degrees beyond the Prouhet threshold.

Its two summands are the square of the first logarithmic coefficient and the
quadratic coefficient of the finite exponential product.  This is the exact
finite identity behind the constant `5/72` and the correction `4/9` below. -/
theorem thueMorsePowerSumRing_add_two_real (m : ℕ) :
    thueMorsePowerSumRing ℝ m (m + 2) =
      (-1 : ℝ) ^ m * (2 : ℝ) ^ m.choose 2 * (m.factorial : ℝ) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2) *
          ((((2 : ℝ) ^ m - 1) ^ 2 / 8) +
            ((4 : ℝ) ^ m - 1) / 72)) := by
  induction m with
  | zero =>
      norm_num [thueMorsePowerSumRing, thueMorseSign, binaryWeight]
  | succ m ih =>
      have hzero :
          (∑ k ∈ range m,
            (Nat.choose (m + 3) k : ℝ) * (2 : ℝ) ^ k *
              thueMorsePowerSumRing ℝ m k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [thueMorsePowerSumRing_eq_zero_of_lt m k (mem_range.mp hk),
          mul_zero]
      have hchooseThree := cast_choose_add_three_left m
      have hchooseTwo :
          ((Nat.choose (m + 3) (m + 1) : ℕ) : ℝ) =
            ((m : ℝ) + 3) * ((m : ℝ) + 2) / 2 := by
        have hsym :
            Nat.choose (m + 3) (m + 1) = Nat.choose (m + 3) 2 :=
          Nat.choose_symm_of_eq_add (by omega)
        rw [hsym, Nat.cast_choose_two ℝ]
        push_cast
        ring
      have hfour : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := by
        calc
          (4 : ℝ) ^ m = ((2 : ℝ) * 2) ^ m := by norm_num
          _ = ((2 : ℝ) ^ m) ^ 2 := by rw [mul_pow, pow_two]
      have hpowTwo :
          (2 : ℝ) ^ (m * 2) = ((2 : ℝ) ^ m) ^ 2 := by
        rw [pow_mul]
      have hpowThree :
          (2 : ℝ) ^ (m * 3) = ((2 : ℝ) ^ m) ^ 3 := by
        rw [pow_mul]
      rw [show m + 1 + 2 = m + 3 by omega,
        thueMorsePowerSumRing_succ (R := ℝ) m (m + 3),
        show m + 3 = (m + 2) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, hzero, zero_add,
        thueMorsePowerSumRing_self,
        thueMorsePowerSumRing_add_one_real, ih,
        Nat.choose_succ_self_right]
      rw [hchooseThree, hchooseTwo, choose_succ_two, pow_add, pow_succ,
        Nat.factorial_succ]
      push_cast
      ring_nf

/-! ## A reusable degree-two residual extractor -/

/-- A complete dyadic Thue--Morse block applied to a translated power of
degree `m+2` depends only on the three moments in degrees `m`, `m+1`, and
`m+2`.  This is the exact `degree two beyond Prouhet` extractor used by the
quarter calculation. -/
theorem thueMorse_translated_power_sum_add_two_real (m : ℕ) (x : ℝ) :
    (∑ h : Fin (2 ^ m), (thueMorseSign h.val : ℝ) *
        (x + (h.val : ℝ)) ^ (m + 2)) =
      thueMorsePowerSumRing ℝ m (m + 2) +
        ((m : ℝ) + 2) * x * thueMorsePowerSumRing ℝ m (m + 1) +
        (Nat.choose (m + 2) 2 : ℝ) * x ^ 2 *
          thueMorsePowerSumRing ℝ m m := by
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (k : ℕ) :
      (∑ h : Fin (2 ^ m),
        (thueMorseSign h.val : ℝ) *
          (x ^ k * (h.val : ℝ) ^ (m + 2 - k) *
            (Nat.choose (m + 2) k : ℝ))) =
        (x ^ k * (Nat.choose (m + 2) k : ℝ)) *
          thueMorsePowerSumRing ℝ m (m + 2 - k) := by
    rw [thueMorsePowerSumRing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _hh
    ring
  simp_rw [hinner]
  rw [show m + 2 + 1 = 3 + m by omega, Finset.sum_range_add]
  have htail :
      (∑ k ∈ range m,
        (x ^ (3 + k) * (Nat.choose (m + 2) (3 + k) : ℝ)) *
          thueMorsePowerSumRing ℝ m (m + 2 - (3 + k))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < m := mem_range.mp hk
    have hdegree : m + 2 - (3 + k) < m := by omega
    rw [thueMorsePowerSumRing_eq_zero_of_lt m _ hdegree, mul_zero]
  rw [htail, add_zero]
  norm_num [Finset.sum_range_succ, Nat.choose_one_right] <;> ring

/-- Normalized form of the degree-two residual extractor.  All factorial,
sign, and triangular-power factors have been cancelled, leaving the two
elementary dyadic statistics `2^m-1` and `4^m-1`. -/
theorem normalized_thueMorse_translated_power_sum_add_two
    (m : ℕ) (x : ℝ) :
    ((-1 : ℝ) ^ (m + 2) /
        ((2 : ℝ) ^ (m + 2).choose 2 * ((m + 2).factorial : ℝ))) *
      (∑ h : Fin (2 ^ m), (thueMorseSign h.val : ℝ) *
        (x + (h.val : ℝ)) ^ (m + 2)) =
      ((((2 : ℝ) ^ m - 1) ^ 2 / 8 + ((4 : ℝ) ^ m - 1) / 72) /
          (2 : ℝ) ^ (2 * m + 1)) +
        (x * ((2 : ℝ) ^ m - 1) + x ^ 2) /
          (2 : ℝ) ^ (2 * m + 2) := by
  rw [thueMorse_translated_power_sum_add_two_real,
    thueMorsePowerSumRing_add_two_real,
    thueMorsePowerSumRing_add_one_real,
    thueMorsePowerSumRing_self]
  have hsign : (-1 : ℝ) ^ (m + 2) = (-1 : ℝ) ^ m := by
    rw [pow_add]
    norm_num
  have hchoose : (m + 2).choose 2 = m.choose 2 + (2 * m + 1) := by
    rw [choose_add_two_two, choose_succ_two]
    omega
  have hpow :
      (2 : ℝ) ^ (m + 2).choose 2 =
        (2 : ℝ) ^ m.choose 2 * (2 : ℝ) ^ (2 * m + 1) := by
    rw [hchoose, pow_add]
  have hfactorial :
      (((m + 2).factorial : ℕ) : ℝ) =
        ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hchooseCast :
      ((Nat.choose (m + 2) 2 : ℕ) : ℝ) =
        ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two ℝ]
    push_cast
    ring
  rw [hsign, hpow, hfactorial, hchooseCast]
  have hsignEven : (-1 : ℝ) ^ (m * 2) = 1 := by
    rw [mul_comm, pow_mul]
    norm_num
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hm1, hm2, hfac]
  ring_nf
  rw [hsignEven]
  ring

/-! ## The quarter block and the half-cell endpoint -/

/-- The normalized complete Thue--Morse block at the quarter anchor is the
report's exact quadratic, including its finite-depth correction.  This is the
pure block identity; `fabiusUniformSpline_quarter_eq_thueMorseBlock` below
supplies the separate cutoff argument which identifies the block with the
actual spline. -/
theorem normalized_quarter_thueMorse_block (m : ℕ) (z : ℝ) :
    ((-1 : ℝ) ^ (m + 2) /
        ((2 : ℝ) ^ (m + 2).choose 2 * ((m + 2).factorial : ℝ))) *
      (∑ h : Fin (2 ^ m), (thueMorseSign h.val : ℝ) *
        ((h.val : ℝ) - (2 : ℝ) ^ (m + 2) * (1 / 4 + z) + 1 / 2) ^
          (m + 2)) =
      5 / 72 + z + 4 * z ^ 2 -
        (4 / 9) * ((4 : ℝ) ^ (m + 3))⁻¹ := by
  let x : ℝ := -(2 : ℝ) ^ (m + 2) * (1 / 4 + z) + 1 / 2
  have hnormalized := normalized_thueMorse_translated_power_sum_add_two m x
  have hsum :
      (∑ h : Fin (2 ^ m), (thueMorseSign h.val : ℝ) *
        ((h.val : ℝ) - (2 : ℝ) ^ (m + 2) * (1 / 4 + z) + 1 / 2) ^
          (m + 2)) =
        ∑ h : Fin (2 ^ m), (thueMorseSign h.val : ℝ) *
          (x + (h.val : ℝ)) ^ (m + 2) := by
    apply Finset.sum_congr rfl
    intro h _hh
    dsimp only [x]
    congr 2
    ring
  rw [hsum, hnormalized]
  have htwoAdd :
      (2 : ℝ) ^ (m + 2) = 4 * (2 : ℝ) ^ m := by
    rw [pow_add]
    norm_num <;> ring
  have htwoDoubleOne :
      (2 : ℝ) ^ (2 * m + 1) = 2 * ((2 : ℝ) ^ m) ^ 2 := by
    rw [pow_add]
    have hdouble : (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    rw [hdouble]
    ring
  have htwoDoubleTwo :
      (2 : ℝ) ^ (2 * m + 2) = 4 * ((2 : ℝ) ^ m) ^ 2 := by
    rw [pow_add]
    have hdouble : (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    rw [hdouble]
    norm_num <;> ring
  have hfour : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := by
    calc
      (4 : ℝ) ^ m = ((2 : ℝ) * 2) ^ m := by norm_num
      _ = ((2 : ℝ) ^ m) ^ 2 := by rw [mul_pow, pow_two]
  have hfourAdd :
      (4 : ℝ) ^ (m + 3) = 64 * ((2 : ℝ) ^ m) ^ 2 := by
    rw [pow_add, hfour]
    norm_num <;> ring
  dsimp only [x]
  rw [htwoAdd, htwoDoubleOne, htwoDoubleTwo, hfour, hfourAdd]
  have hpowne : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp [hpowne] <;> ring

private theorem dyadic_quarterCellRadius_scale (m : ℕ) :
    (2 : ℝ) ^ (m + 2) * (((2 : ℝ) ^ (m + 3))⁻¹) = 1 / 2 := by
  rw [show m + 3 = (m + 2) + 1 by omega, pow_succ]
  field_simp
  rw [← pow_add]

private theorem dyadic_quarterAnchor_scale (m : ℕ) :
    (2 : ℝ) ^ (m + 2) * (1 / 4) = (2 : ℝ) ^ m := by
  rw [pow_add]
  norm_num <;> ring

private theorem quarter_range_length_of_mem_left_closed_right_open
    (m : ℕ) {z : ℝ}
    (hzlow : -((2 : ℝ) ^ (m + 3))⁻¹ ≤ z)
    (hzhigh : z < ((2 : ℝ) ^ (m + 3))⁻¹) :
    fabiusDiscreteLimitRangeLength (1 / 4 + z) (m + 2) = 2 ^ m := by
  have hzscaleLow :
      -(1 / 2 : ℝ) ≤ (2 : ℝ) ^ (m + 2) * z := by
    calc
      -(1 / 2 : ℝ) =
          (2 : ℝ) ^ (m + 2) * (-((2 : ℝ) ^ (m + 3))⁻¹) := by
            rw [mul_neg, dyadic_quarterCellRadius_scale]
      _ ≤ (2 : ℝ) ^ (m + 2) * z :=
        mul_le_mul_of_nonneg_left hzlow (by positivity)
  have hzscaleHigh :
      (2 : ℝ) ^ (m + 2) * z < 1 / 2 := by
    calc
      (2 : ℝ) ^ (m + 2) * z <
          (2 : ℝ) ^ (m + 2) * (((2 : ℝ) ^ (m + 3))⁻¹) :=
        mul_lt_mul_of_pos_left hzhigh (by positivity)
      _ = 1 / 2 := dyadic_quarterCellRadius_scale m
  have hargNonneg :
      0 ≤ (2 : ℝ) ^ (m + 2) * (1 / 4 + z) + 1 / 2 := by
    rw [mul_add, dyadic_quarterAnchor_scale]
    have hpowNonneg : 0 ≤ (2 : ℝ) ^ m := by positivity
    linarith
  rw [fabiusDiscreteLimitRangeLength]
  apply (Nat.floor_eq_iff hargNonneg).2
  rw [show (2 : ℝ) ^ (m + 2) * (1 / 4 + z) + 1 / 2 =
      (2 : ℝ) ^ m + (2 : ℝ) ^ (m + 2) * z + 1 / 2 by
        rw [mul_add, dyadic_quarterAnchor_scale]]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

private theorem quarter_range_length_at_endpoint (m : ℕ) :
    fabiusDiscreteLimitRangeLength
        (1 / 4 + ((2 : ℝ) ^ (m + 3))⁻¹) (m + 2) =
      2 ^ m + 1 := by
  rw [fabiusDiscreteLimitRangeLength]
  have harg :
      (2 : ℝ) ^ (m + 2) *
          (1 / 4 + ((2 : ℝ) ^ (m + 3))⁻¹) + 1 / 2 =
        ((2 ^ m + 1 : ℕ) : ℝ) := by
    rw [mul_add, dyadic_quarterAnchor_scale,
      dyadic_quarterCellRadius_scale]
    push_cast
    ring
  rw [harg, Nat.floor_natCast]

/-- On the report's full closed quarter cell, the repository spline is exactly
its one complete dyadic Thue--Morse block.  The half-cell rounding adds the
next index only at the right endpoint, where its positive-degree power is
literally zero. -/
theorem fabiusUniformSpline_quarter_eq_thueMorseBlock
    (m : ℕ) {z : ℝ}
    (hz : z ∈ Icc (-((2 : ℝ) ^ (m + 3))⁻¹)
      (((2 : ℝ) ^ (m + 3))⁻¹)) :
    fabiusUniformSpline (m + 2) (1 / 4 + z) =
      ((-1 : ℝ) ^ (m + 2) /
        ((2 : ℝ) ^ (m + 2).choose 2 * ((m + 2).factorial : ℝ))) *
        ∑ h : Fin (2 ^ m), (thueMorseSign h.val : ℝ) *
          ((h.val : ℝ) - (2 : ℝ) ^ (m + 2) * (1 / 4 + z) + 1 / 2) ^
            (m + 2) := by
  rcases lt_or_eq_of_le hz.2 with hzlt | rfl
  · rw [fabiusUniformSpline,
      quarter_range_length_of_mem_left_closed_right_open m hz.1 hzlt]
    rw [← Fin.sum_univ_eq_sum_range]
  · rw [fabiusUniformSpline, quarter_range_length_at_endpoint,
      Finset.sum_range_succ]
    have hlast :
        ((2 ^ m : ℕ) : ℝ) -
            (2 : ℝ) ^ (m + 2) *
              (1 / 4 + ((2 : ℝ) ^ (m + 3))⁻¹) + 1 / 2 = 0 := by
      rw [mul_add, dyadic_quarterAnchor_scale,
        dyadic_quarterCellRadius_scale]
      push_cast
      ring
    rw [hlast, zero_pow (by omega : m + 2 ≠ 0), mul_zero, add_zero]
    rw [← Fin.sum_univ_eq_sum_range]

/-- The finite repository spline has the exact quarter quadratic throughout
the whole closed dyadic cell around `1/4`.  This semantic theorem hides the
Thue--Morse moment extraction and cutoff bookkeeping used in its proof. -/
theorem fabiusUniformSpline_quarter_eq_quadratic
    (m : ℕ) {z : ℝ}
    (hz : z ∈ Icc (-((2 : ℝ) ^ (m + 3))⁻¹)
      (((2 : ℝ) ^ (m + 3))⁻¹)) :
    fabiusUniformSpline (m + 2) (1 / 4 + z) =
      5 / 72 + z + 4 * z ^ 2 -
        (4 / 9) * ((4 : ℝ) ^ (m + 3))⁻¹ := by
  rw [fabiusUniformSpline_quarter_eq_thueMorseBlock m hz]
  exact normalized_quarter_thueMorse_block m z

/-- Report-indexed form of the exact quadratic on the whole closed quarter
cell.  This theorem centralizes the one-step conversion
`P_n = fabiusUniformSpline (n-1)`; both the one-sided inverse API below and the
symmetric wrapper in `QuarterSplineTwoSided` are direct consequences. -/
theorem reportFiniteFabiusApproximant_quarter_eq_quadratic
    {n : ℕ} (hn : 3 ≤ n) {z : ℝ}
    (hz : z ∈ Icc (-((2 : ℝ) ^ n)⁻¹) (((2 : ℝ) ^ n)⁻¹)) :
    reportFiniteFabiusApproximant n (1 / 4 + z) =
      5 / 72 + z + 4 * z ^ 2 - (4 / 9) * ((4 : ℝ) ^ n)⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hadd : 3 + m = m + 3 := by omega
  have hsub : m + 3 - 1 = m + 2 := by omega
  have hz' :
      z ∈ Icc (-((2 : ℝ) ^ (m + 3))⁻¹) (((2 : ℝ) ^ (m + 3))⁻¹) := by
    simpa only [hadd] using hz
  simpa only [reportFiniteFabiusApproximant, hsub, hadd] using
    fabiusUniformSpline_quarter_eq_quadratic m hz'

/-! ## The exact local polynomial and inverse transfer -/

/-- The degree-`m+2` repository spline has the report's exact quarter
polynomial on the closed nonnegative half-cell at prefix depth `m+3`.  This is
the direct source-level discharge of `IsQuarterLocalPolynomial`, before
translating to the report's `n` index. -/
theorem fabiusUniformSpline_isQuarterLocalPolynomial (m : ℕ) :
    IsQuarterLocalPolynomial (fabiusUniformSpline (m + 2))
      (((4 : ℝ) ^ (m + 3))⁻¹) (((2 : ℝ) ^ (m + 3))⁻¹) := by
  intro z hz
  apply fabiusUniformSpline_quarter_eq_quadratic m
  have hradius : 0 ≤ ((2 : ℝ) ^ (m + 3))⁻¹ := by positivity
  exact ⟨by linarith [hz.1], hz.2⟩

/-- For every report depth `n >= 3`, its actual finite approximant `P_n`
has the exact quarter polynomial on the closed right half-cell of radius
`2⁻ⁿ`. -/
theorem reportFiniteFabiusApproximant_isQuarterLocalPolynomial
    {n : ℕ} (hn : 3 ≤ n) :
    IsQuarterLocalPolynomial (reportFiniteFabiusApproximant n)
      (((4 : ℝ) ^ n)⁻¹) (((2 : ℝ) ^ n)⁻¹) := by
  intro z hz
  apply reportFiniteFabiusApproximant_quarter_eq_quadratic hn
  have hradius : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  exact ⟨by linarith [hz.1], hz.2⟩

/-- Pointwise form of the exact quarter-cell formula from the report. -/
theorem reportFiniteFabiusApproximant_quarter (n : ℕ) (hn : 3 ≤ n)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) (((2 : ℝ) ^ n)⁻¹)) :
    reportFiniteFabiusApproximant n (1 / 4 + z) =
      5 / 72 + z + 4 * z ^ 2 - (4 / 9) * ((4 : ℝ) ^ n)⁻¹ :=
  reportFiniteFabiusApproximant_isQuarterLocalPolynomial hn z hz

/-- Any quarter local polynomial is strictly increasing on its nonnegative
half-cell.  The parameter `Q` cancels: the difference factors as
`(v-u) (1 + 4(u+v))`, whose factors are positive for `0 <= u < v`. -/
theorem IsQuarterLocalPolynomial.strictMonoOn
    {P : ℝ → ℝ} {Q radius : ℝ}
    (hlocal : IsQuarterLocalPolynomial P Q radius) :
    StrictMonoOn P (Icc (1 / 4 : ℝ) (1 / 4 + radius)) := by
  intro x hx y hy hxy
  let u : ℝ := x - 1 / 4
  let v : ℝ := y - 1 / 4
  have hu : u ∈ Icc (0 : ℝ) radius := by
    dsimp only [u]
    constructor <;> linarith [hx.1, hx.2]
  have hv : v ∈ Icc (0 : ℝ) radius := by
    dsimp only [v]
    constructor <;> linarith [hy.1, hy.2]
  have hxu : x = 1 / 4 + u := by dsimp only [u]; ring
  have hyv : y = 1 / 4 + v := by dsimp only [v]; ring
  rw [hxu, hyv, hlocal u hu, hlocal v hv]
  have huv : 0 < v - u := by dsimp only [u, v]; linarith
  have hfactor : 0 < (v - u) * (1 + 4 * (u + v)) := by
    apply mul_pos huv
    nlinarith [hu.1, hv.1]
  nlinarith

/-- The finite spline is strictly increasing on its nonnegative quarter
half-cell.  This supplies the uniqueness half of the report's phrase "the
increasing inverse branch" directly from the exact quadratic. -/
theorem strictMonoOn_reportFiniteFabiusApproximant_quarter
    (n : ℕ) (hn : 3 ≤ n) :
    StrictMonoOn (reportFiniteFabiusApproximant n)
      (Icc (1 / 4 : ℝ) (1 / 4 + ((2 : ℝ) ^ n)⁻¹)) := by
  exact (reportFiniteFabiusApproximant_isQuarterLocalPolynomial hn).strictMonoOn

/-- The report's exact finite-depth quarter value, now with its local
polynomial premise discharged for the concrete spline. -/
theorem reportFiniteFabiusApproximant_quarterPrefix_value
    (n : ℕ) (hn : 3 ≤ n) :
    reportFiniteFabiusApproximant n
        (1 / 4 + quarterPrefixDisplacement n) = 5 / 72 := by
  exact quarterPrefix_value_of_localPolynomial n
    (reportFiniteFabiusApproximant_isQuarterLocalPolynomial hn)

/-- Exact quarter-quantile formula for any chosen local left inverse of the
finite spline.  This is precisely the report's `G_n` statement once `G` is
specified to be its increasing inverse branch; it is intentionally not
identified with the limiting inverse `fabiusInv`. -/
theorem reportFiniteFabiusApproximant_quarterPrefix_quantile
    {G : ℝ → ℝ} (n : ℕ) (hn : 3 ≤ n)
    (hleft : ∀ x ∈ Icc (1 / 4 : ℝ)
        (1 / 4 + ((2 : ℝ) ^ n)⁻¹),
      G (reportFiniteFabiusApproximant n x) = x) :
    G (5 / 72) =
      1 / 4 +
        (Real.sqrt (1 + (64 / 9) * ((4 : ℝ) ^ n)⁻¹) - 1) / 8 := by
  exact quarterPrefix_quantile_of_localPolynomial n
    (reportFiniteFabiusApproximant_isQuarterLocalPolynomial hn) hleft

end

end Fabius
