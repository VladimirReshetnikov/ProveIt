import FabiusFunction.ProbabilityRepresentation
import FabiusFunction.FabiusDiscreteLimitToeplitz
import FabiusFunction.DyadicClosedForm
import FabiusFunction.ThueMorsePrefix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Centered finite splines and their probabilistic limit

The centered Thue--Morse power sums used by the discrete-limit formula are
identified here with distribution functions of finite weighted sums of
independent uniform coordinates.  The probabilistic model gives sharp
support bounds, saturation on the final half-cell, monotonicity on the
fundamental interval, and pointwise convergence to the bounded Fabius
function.  These statements include the degree-zero step spline.  A
block-translation identity extends the estimates across the nonnegative axis,
while exact empty-prefix vanishing supplies the nonpositive half-line.  The
real affine Prouhet identities used in the translation and complement formulas
come from `FabiusFunction.ThueMorsePrefix`.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal MeasureTheory unitInterval Topology
open Filter Finset Set MeasureTheory ProbabilityTheory

namespace Fabius

noncomputable section

/-- The half-cell-centered spline occurring in the discrete-limit formula. -/
def fabiusUniformSpline (p : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ p /
      ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ))) *
    ∑ r ∈ Finset.range
        (fabiusDiscreteLimitRangeLength x p),
      (thueMorseSign r : ℝ) *
        ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p

/-- Empty-prefix half-cell vanishing for a centered spline at one fixed scale. -/
theorem fabiusUniformSpline_eq_zero_of_lt_half
    (p : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ p * x < 1 / 2) :
    fabiusUniformSpline p x = 0 := by
  rw [fabiusUniformSpline,
    fabiusDiscreteLimitRangeLength_eq_zero_of_lt_half p hx]
  simp

/-- In positive degree the centered spline also vanishes at the half-cell
boundary: when the prefix first becomes nonempty, its sole power term is zero. -/
theorem fabiusUniformSpline_eq_zero_of_le_half
    (p : ℕ) (hp : 0 < p) {x : ℝ} (hx : (2 : ℝ) ^ p * x ≤ 1 / 2) :
    fabiusUniformSpline p x = 0 := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact fabiusUniformSpline_eq_zero_of_lt_half p hlt
  · rw [fabiusUniformSpline, fabiusDiscreteLimitRangeLength, heq]
    norm_num [hp.ne']

/-- The centered spline vanishes at and to the left of the origin because
its finite prefix is empty there. -/
theorem fabiusUniformSpline_eq_zero_of_nonpos
    (p : ℕ) {x : ℝ} (hx : x ≤ 0) :
    fabiusUniformSpline p x = 0 := by
  apply fabiusUniformSpline_eq_zero_of_lt_half p
  have hscale : (2 : ℝ) ^ p * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
  linarith

/-- In particular, every centered spline vanishes on the negative axis. -/
theorem fabiusUniformSpline_eq_zero_of_neg
    (p : ℕ) {x : ℝ} (hx : x < 0) :
    fabiusUniformSpline p x = 0 :=
  fabiusUniformSpline_eq_zero_of_nonpos p hx.le

/-- At degree zero the normalizing constant is `1` and each power term is
`1` under the `0 ^ 0 = 1` convention, so the centered spline reduces to the
plain prefix sum of Thue--Morse signs. -/
@[simp] lemma fabiusUniformSpline_zero (x : ℝ) :
    fabiusUniformSpline 0 x =
      ∑ r ∈ Finset.range (fabiusDiscreteLimitRangeLength x 0),
        (thueMorseSign r : ℝ) := by
  simp [fabiusUniformSpline]

private lemma sum_range_thueMorseSign_two_mul (a : ℕ) :
    (∑ r ∈ Finset.range (2 * a), (thueMorseSign r : ℝ)) = 0 := by
  have h := thueMorse_sum_two_mul a (fun _ => (1 : ℚ))
  have hq :
      (∑ r ∈ Finset.range (2 * a), (thueMorseSign r : ℚ)) = 0 := by
    calc
      (∑ r ∈ Finset.range (2 * a), (thueMorseSign r : ℚ)) =
          ∑ i : Fin (2 * a), (thueMorseSign i.val : ℚ) * 1 := by
        simpa using (Fin.sum_univ_eq_sum_range
          (fun r : ℕ => (thueMorseSign r : ℚ) * 1) (2 * a)).symm
      _ = ∑ j : Fin a, (thueMorseSign j.val : ℚ) * (1 - 1) := h
      _ = 0 := by simp
  exact_mod_cast hq

private lemma abs_sum_range_thueMorseSign_le_one (N : ℕ) :
    |∑ r ∈ Finset.range N, (thueMorseSign r : ℝ)| ≤ 1 := by
  rcases N.even_or_odd with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [show a + a = 2 * a by omega, sum_range_thueMorseSign_two_mul]
    norm_num
  · rw [Finset.sum_range_succ, sum_range_thueMorseSign_two_mul, zero_add]
    norm_num [thueMorseSign]

/-- The degree-zero centered spline is a partial sum of Thue--Morse signs, and
every such partial sum lies in `[-1, 1]`; hence the bound, at every real point
and with no interval restriction.  This is the degree-zero base case of
`abs_fabiusUniformSpline_le_one`. -/
lemma abs_fabiusUniformSpline_zero_le_one (x : ℝ) :
    |fabiusUniformSpline 0 x| ≤ 1 := by
  rw [fabiusUniformSpline_zero]
  exact abs_sum_range_thueMorseSign_le_one _

private lemma fabiusDiscreteLimitRangeLength_two_mul_add
    (p block : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    fabiusDiscreteLimitRangeLength (2 * block + y) p =
      block * 2 ^ (p + 1) + fabiusDiscreteLimitRangeLength y p := by
  rw [fabiusDiscreteLimitRangeLength]
  have hz : 0 ≤ (2 : ℝ) ^ p * y + 1 / 2 := by positivity
  have harg :
      (2 : ℝ) ^ p * (2 * (block : ℝ) + y) + 1 / 2 =
        ((2 : ℝ) ^ p * y + 1 / 2) +
          (block * 2 ^ (p + 1) : ℕ) := by
    rw [pow_succ]
    push_cast
    ring
  rw [harg, Nat.floor_add_natCast hz]
  rw [Nat.add_comm]
  rfl

private lemma fabiusDiscreteLimitRangeLength_le_block
    (p : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y < 2) :
    fabiusDiscreteLimitRangeLength y p ≤ 2 ^ (p + 1) := by
  rw [fabiusDiscreteLimitRangeLength]
  have hz : 0 ≤ (2 : ℝ) ^ p * y + 1 / 2 := by positivity
  have hzlt : (2 : ℝ) ^ p * y + 1 / 2 <
      ((2 ^ (p + 1) + 1 : ℕ) : ℝ) := by
    rw [pow_succ]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [mul_lt_mul_of_pos_left hy2
      (show (0 : ℝ) < 2 ^ p by positivity)]
  have h := (Nat.floor_lt hz).2 hzlt
  omega

/-- Translation by a complete length-two block changes the centered spline
only by the corresponding Thue--Morse sign. -/
theorem fabiusUniformSpline_block_translate
    (p block : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y < 2) :
    fabiusUniformSpline p (2 * block + y) =
      (thueMorseSign block : ℝ) * fabiusUniformSpline p y := by
  let period : ℕ := 2 ^ (p + 1)
  let count : ℕ := fabiusDiscreteLimitRangeLength y p
  let f : ℕ → ℝ := fun r =>
    (thueMorseSign r : ℝ) *
      ((r : ℝ) - (2 : ℝ) ^ p * (2 * block + y) + 1 / 2) ^ p
  have hcount : count ≤ period := by
    exact fabiusDiscreteLimitRangeLength_le_block p hy0 hy2
  have hfull :
      (∑ q ∈ Finset.range block,
        ∑ r ∈ Finset.range period, f (q * period + r)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hz := thueMorse_affine_power_sum_eq_zero_real
      (p + 1) p (Nat.lt_succ_self p)
      (((q : ℝ) - block) * (period : ℝ) -
        (2 : ℝ) ^ p * y + 1 / 2) 1
    have hzrange :
        (∑ r ∈ Finset.range period,
          (thueMorseSign r : ℝ) *
            ((((q : ℝ) - block) * (period : ℝ) -
              (2 : ℝ) ^ p * y + 1 / 2) + 1 * (r : ℝ)) ^ p) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      simpa only [period] using hz
    calc
      (∑ r ∈ Finset.range period, f (q * period + r)) =
          (thueMorseSign q : ℝ) *
            ∑ r ∈ Finset.range period,
              (thueMorseSign r : ℝ) *
                ((((q : ℝ) - block) * (period : ℝ) -
                  (2 : ℝ) ^ p * y + 1 / 2) + 1 * (r : ℝ)) ^ p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hrlt : r < period := Finset.mem_range.mp hr
        dsimp only [f]
        rw [thueMorseSign_block_concat (p + 1) q r
          (by simpa [period] using hrlt)]
        push_cast
        dsimp only [period]
        rw [pow_succ]
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      _ = 0 := by rw [hzrange, mul_zero]
  rw [fabiusUniformSpline, fabiusUniformSpline,
    fabiusDiscreteLimitRangeLength_two_mul_add p block hy0]
  change _ * (∑ r ∈ Finset.range (block * period + count), f r) = _
  rw [sum_range_block_decomposition_with_remainder f block period count,
    hfull, zero_add]
  have hresidual :
      (∑ r ∈ Finset.range count, f (block * period + r)) =
        (thueMorseSign block : ℝ) *
          ∑ r ∈ Finset.range count,
            (thueMorseSign r : ℝ) *
              ((r : ℝ) - (2 : ℝ) ^ p * y + 1 / 2) ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrlt : r < period :=
      (Finset.mem_range.mp hr).trans_le hcount
    dsimp only [f]
    rw [thueMorseSign_block_concat (p + 1) block r
      (by simpa [period] using hrlt)]
    push_cast
    dsimp only [period]
    rw [pow_succ]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hresidual]
  ring

/-- Fixed-range positive-part form of the centered spline.  On `[0,1]` and
at positive orders it agrees with `fabiusUniformSpline`. -/
private def fabiusUniformPositiveSpline (p : ℕ) (x : ℝ) : ℝ :=
  (1 / ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ))) *
    ∑ r ∈ Finset.range (2 ^ p),
      (thueMorseSign r : ℝ) *
        (max ((2 : ℝ) ^ p * x - 1 / 2 - (r : ℝ)) 0) ^ p

private lemma intervalIntegral_max_pow (p : ℕ) (hp : 0 < p)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (max t 0) ^ p) =
      ((max b 0) ^ (p + 1) - (max a 0) ^ (p + 1)) / (p + 1) := by
  rcases le_total b 0 with hb | hb
  · have hzero : ∀ t ∈ uIcc a b, max t 0 ^ p = 0 := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      rw [max_eq_right (ht.2.trans hb), zero_pow hp.ne']
    rw [intervalIntegral.integral_congr hzero]
    simp only [intervalIntegral.integral_zero]
    rw [max_eq_right hb, max_eq_right (hab.trans hb)]
    simp
  · rcases le_total 0 a with ha | ha
    · have heq : ∀ t ∈ uIcc a b, max t 0 ^ p = t ^ p := by
        intro t ht
        rw [uIcc_of_le hab] at ht
        rw [max_eq_left (ha.trans ht.1)]
      rw [intervalIntegral.integral_congr heq, integral_pow,
        max_eq_left hb, max_eq_left ha]
    · have hleft : (∫ t in a..0, (max t 0) ^ p) = 0 := by
        have hzero : ∀ t ∈ uIcc a 0, max t 0 ^ p = 0 := by
          intro t ht
          rw [uIcc_of_le ha] at ht
          rw [max_eq_right ht.2, zero_pow hp.ne']
        rw [intervalIntegral.integral_congr hzero,
          intervalIntegral.integral_zero]
      have hright : (∫ t in (0 : ℝ)..b, (max t 0) ^ p) =
          b ^ (p + 1) / (p + 1) := by
        have heq : ∀ t ∈ uIcc (0 : ℝ) b, max t 0 ^ p = t ^ p := by
          intro t ht
          rw [uIcc_of_le hb] at ht
          rw [max_eq_left ht.1]
        rw [intervalIntegral.integral_congr heq, integral_pow]
        simp
      have hcont : Continuous (fun t : ℝ => max t 0 ^ p) :=
        (continuous_id.max continuous_const).pow p
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable a 0) (hcont.intervalIntegrable 0 b),
        hleft, hright, zero_add, max_eq_left hb, max_eq_right ha]
      simp

private lemma intervalIntegral_max_sub_mul_pow (p : ℕ) (hp : 0 < p)
    (A c : ℝ) (hc : 0 < c) :
    (∫ u in (0 : ℝ)..1, (max (A - c * u) 0) ^ p) =
      ((max A 0) ^ (p + 1) - (max (A - c) 0) ^ (p + 1)) /
        (c * (p + 1)) := by
  calc
    (∫ u in (0 : ℝ)..1, (max (A - c * u) 0) ^ p) =
        c⁻¹ • ∫ t in A - c * 1..A - c * 0, (max t 0) ^ p := by
      exact intervalIntegral.integral_comp_sub_mul
        (fun t : ℝ => max t 0 ^ p) hc.ne' A
    _ = ((max A 0) ^ (p + 1) - (max (A - c) 0) ^ (p + 1)) /
        (c * (p + 1)) := by
      rw [intervalIntegral_max_pow p hp (by linarith)]
      simp only [smul_eq_mul, mul_zero, sub_zero, mul_one]
      field_simp

private lemma mem_range_fabiusDiscreteLimitRangeLength_iff
    (p r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    r ∈ Finset.range (fabiusDiscreteLimitRangeLength x p) ↔
      (r : ℝ) ≤ (2 : ℝ) ^ p * x - 1 / 2 := by
  have hz : 0 ≤ (2 : ℝ) ^ p * x + 1 / 2 := by
    exact add_nonneg (mul_nonneg (by positivity) hx) (by norm_num)
  rw [Finset.mem_range, fabiusDiscreteLimitRangeLength]
  constructor
  · intro hr
    have hrNat : r + 1 ≤ ⌊(2 : ℝ) ^ p * x + 1 / 2⌋₊ := by omega
    have hrCast : (r : ℝ) + 1 ≤
        (⌊(2 : ℝ) ^ p * x + 1 / 2⌋₊ : ℝ) := by exact_mod_cast hrNat
    have hfloor : (⌊(2 : ℝ) ^ p * x + 1 / 2⌋₊ : ℝ) ≤
        (2 : ℝ) ^ p * x + 1 / 2 := Nat.floor_le hz
    linarith
  · intro hr
    have hcast : ((r + 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ p * x + 1 / 2 := by
      push_cast
      linarith
    have hnat : r + 1 ≤ ⌊(2 : ℝ) ^ p * x + 1 / 2⌋₊ :=
      Nat.le_floor hcast
    omega

private lemma fabiusDiscreteLimitRangeLength_le_pow
    (p : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusDiscreteLimitRangeLength x p ≤ 2 ^ p := by
  let z : ℝ := (2 : ℝ) ^ p * x + 1 / 2
  have hz : 0 ≤ z := by
    dsimp [z]
    exact add_nonneg (mul_nonneg (by positivity) hx.1) (by norm_num)
  have hzlt : z < ((2 ^ p + 1 : ℕ) : ℝ) := by
    have hmul : (2 : ℝ) ^ p * x ≤ (2 : ℝ) ^ p :=
      mul_le_of_le_one_right (by positivity) hx.2
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [z]
    linarith
  have := (Nat.floor_lt hz).2 hzlt
  change ⌊z⌋₊ ≤ 2 ^ p
  omega

private lemma fabiusDiscreteLimitRangeLength_one_add
    (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    fabiusDiscreteLimitRangeLength (1 + x) p =
      2 ^ p + fabiusDiscreteLimitRangeLength x p := by
  rw [fabiusDiscreteLimitRangeLength]
  have hz : 0 ≤ (2 : ℝ) ^ p * x + 1 / 2 := by positivity
  have harg : (2 : ℝ) ^ p * (1 + x) + 1 / 2 =
      ((2 : ℝ) ^ p * x + 1 / 2) + (2 ^ p : ℕ) := by
    push_cast
    ring
  rw [harg, Nat.floor_add_natCast hz, Nat.add_comm]
  rfl

/-- On the second unit cell the centered spline is the complementary first
cell spline.  The identity includes order zero under Lean's `0 ^ 0 = 1`
convention. -/
theorem fabiusUniformSpline_one_add
    (p : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    fabiusUniformSpline p (1 + x) = 1 - fabiusUniformSpline p x := by
  let count : ℕ := fabiusDiscreteLimitRangeLength x p
  have hcount : count ≤ 2 ^ p :=
    fabiusDiscreteLimitRangeLength_le_pow p ⟨hx0, hx1⟩
  let base : ℝ := -(2 : ℝ) ^ p * (1 + x) + 1 / 2
  have hfirst :
      (∑ r ∈ Finset.range (2 ^ p),
        (thueMorseSign r : ℝ) *
          ((r : ℝ) - (2 : ℝ) ^ p * (1 + x) + 1 / 2) ^ p) =
        (-1 : ℝ) ^ p * (2 : ℝ) ^ p.choose 2 * p.factorial := by
    have h := thueMorse_affine_power_sum_self_real p base 1
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      (∑ r : Fin (2 ^ p),
          (thueMorseSign r.val : ℝ) *
            ((r.val : ℝ) - (2 : ℝ) ^ p * (1 + x) + 1 / 2) ^ p) =
          ∑ r : Fin (2 ^ p),
            (thueMorseSign r.val : ℝ) * (base + (r.val : ℝ)) ^ p := by
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [base]
        ring
      _ = _ := by simpa using h
  have hsecond :
      (∑ r ∈ Finset.range count,
        (thueMorseSign (2 ^ p + r) : ℝ) *
          (((2 ^ p + r : ℕ) : ℝ) -
            (2 : ℝ) ^ p * (1 + x) + 1 / 2) ^ p) =
        -(∑ r ∈ Finset.range count,
          (thueMorseSign r : ℝ) *
            ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrlt : r < 2 ^ p :=
      (Finset.mem_range.mp hr).trans_le hcount
    rw [thueMorseSign_add_pow_two p r hrlt]
    push_cast
    ring
  rw [fabiusUniformSpline, fabiusUniformSpline,
    fabiusDiscreteLimitRangeLength_one_add p hx0,
    Finset.sum_range_add, hfirst, hsecond]
  let D : ℝ := (2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ)
  let S : ℝ := ∑ r ∈ Finset.range count,
    (thueMorseSign r : ℝ) *
      ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p
  have hden : D ≠ 0 := by
    dsimp [D]
    positivity
  have hsign : (-1 : ℝ) ^ p * (-1 : ℝ) ^ p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  change (-1 : ℝ) ^ p /
        ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ)) *
      ((-1 : ℝ) ^ p * (2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ) +
        -∑ r ∈ Finset.range count,
          (thueMorseSign r : ℝ) *
            ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p) =
    1 - (-1 : ℝ) ^ p /
        ((2 : ℝ) ^ p.choose 2 * (p.factorial : ℝ)) *
      ∑ r ∈ Finset.range count,
        (thueMorseSign r : ℝ) *
          ((r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2) ^ p
  have hmain :
      (-1 : ℝ) ^ p / D * ((-1 : ℝ) ^ p * D + -S) =
        1 - (-1 : ℝ) ^ p / D * S := by
    calc
      (-1 : ℝ) ^ p / D * ((-1 : ℝ) ^ p * D + -S) =
        ((-1 : ℝ) ^ p * (-1 : ℝ) ^ p) * (D / D) -
          (-1 : ℝ) ^ p / D * S := by ring
      _ = 1 - (-1 : ℝ) ^ p / D * S := by
        rw [hsign, div_self hden, one_mul]
  simpa only [D, S, count, mul_assoc] using hmain

private theorem fabiusUniformSpline_eq_positiveSpline
    (p : ℕ) (hp : 0 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline p x = fabiusUniformPositiveSpline p x := by
  let y : ℝ := (2 : ℝ) ^ p * x - 1 / 2
  have hcount : fabiusDiscreteLimitRangeLength x p ≤ 2 ^ p :=
    fabiusDiscreteLimitRangeLength_le_pow p hx
  have hsum :
      (∑ r ∈ range (2 ^ p),
          (thueMorseSign r : ℝ) * (max (y - (r : ℝ)) 0) ^ p) =
        ∑ r ∈ range (fabiusDiscreteLimitRangeLength x p),
          (thueMorseSign r : ℝ) * (y - (r : ℝ)) ^ p := by
    rw [← Finset.sum_subset (range_mono hcount)]
    · apply Finset.sum_congr rfl
      intro r hr
      have hry : (r : ℝ) ≤ y := by
        dsimp [y]
        exact (mem_range_fabiusDiscreteLimitRangeLength_iff p r hx.1).mp hr
      rw [max_eq_left (sub_nonneg.mpr hry)]
    · intro r hrBig hrSmall
      have hry : y < (r : ℝ) := lt_of_not_ge (fun h =>
        hrSmall ((mem_range_fabiusDiscreteLimitRangeLength_iff p r hx.1).mpr h))
      rw [max_eq_right (sub_nonpos.mpr hry.le), zero_pow hp.ne']
      ring
  rw [fabiusUniformSpline, fabiusUniformPositiveSpline]
  have hrewrite (r : ℕ) :
      (r : ℝ) - (2 : ℝ) ^ p * x + 1 / 2 = (r : ℝ) - y := by
    dsimp [y]
    ring
  simp_rw [hrewrite]
  have hpositive (r : ℕ) :
      (2 : ℝ) ^ p * x - 1 / 2 - (r : ℝ) = y - (r : ℝ) := by
    rfl
  simp_rw [hpositive]
  have hterm :
      (∑ r ∈ range (fabiusDiscreteLimitRangeLength x p),
          (thueMorseSign r : ℝ) * ((r : ℝ) - y) ^ p) =
        (-1 : ℝ) ^ p *
          ∑ r ∈ range (fabiusDiscreteLimitRangeLength x p),
            (thueMorseSign r : ℝ) * (y - (r : ℝ)) ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show (r : ℝ) - y = -(y - (r : ℝ)) by ring, neg_pow]
    ring
  rw [hterm, ← hsum]
  have hsquare : (-1 : ℝ) ^ p * (-1 : ℝ) ^ p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  field_simp
  rw [pow_two, hsquare, one_mul]

private theorem fabiusUniformPositiveSpline_smoothing
    (p : ℕ) (hp : 0 < p) (x : ℝ) :
    fabiusUniformPositiveSpline (p + 1) x =
      ∫ u in (0 : ℝ)..1, fabiusUniformPositiveSpline p (2 * x - u) := by
  let P : ℕ → ℝ := fun r =>
    (max ((2 : ℝ) ^ (p + 1) * x - 1 / 2 - (r : ℝ)) 0) ^ (p + 1)
  have hpowNat : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by
    rw [pow_succ]
    omega
  have hsecond :
      (∑ r ∈ range (2 ^ p),
          (thueMorseSign (2 ^ p + r) : ℝ) * P (2 ^ p + r)) =
        -∑ r ∈ range (2 ^ p),
          (thueMorseSign r : ℝ) * P (2 ^ p + r) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [thueMorseSign_add_pow_two p r (Finset.mem_range.mp hr)]
    push_cast
    ring
  have hsum :
      (∑ r ∈ range (2 ^ p),
          (thueMorseSign r : ℝ) * (P r - P (2 ^ p + r))) =
        ∑ r ∈ range (2 ^ (p + 1)),
          (thueMorseSign r : ℝ) * P r := by
    rw [hpowNat, Finset.sum_range_add, hsecond]
    calc
      (∑ r ∈ range (2 ^ p),
          (thueMorseSign r : ℝ) * (P r - P (2 ^ p + r))) =
          (∑ r ∈ range (2 ^ p), (thueMorseSign r : ℝ) * P r) -
            ∑ r ∈ range (2 ^ p),
              (thueMorseSign r : ℝ) * P (2 ^ p + r) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = _ := by ring
  simp only [fabiusUniformPositiveSpline]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro r hr
    apply Continuous.intervalIntegrable
    fun_prop
  simp_rw [intervalIntegral.integral_const_mul]
  have hintegral (r : ℕ) :
      (∫ u in (0 : ℝ)..1,
          (max ((2 : ℝ) ^ p * (2 * x - u) - 1 / 2 - (r : ℝ)) 0) ^ p) =
        (P r - P (2 ^ p + r)) /
          ((2 : ℝ) ^ p * (p + 1)) := by
    let A : ℝ := (2 : ℝ) ^ (p + 1) * x - 1 / 2 - (r : ℝ)
    have harg (u : ℝ) :
        (2 : ℝ) ^ p * (2 * x - u) - 1 / 2 - (r : ℝ) =
          A - (2 : ℝ) ^ p * u := by
      dsimp [A]
      rw [pow_succ]
      ring
    simp_rw [harg]
    rw [intervalIntegral_max_sub_mul_pow p hp A ((2 : ℝ) ^ p) (by positivity)]
    congr 2
    dsimp [P, A]
    congr 2
    push_cast
    ring
  simp_rw [hintegral]
  have hfactor :
      (∑ r ∈ range (2 ^ p),
          (thueMorseSign r : ℝ) *
            ((P r - P (2 ^ p + r)) / ((2 : ℝ) ^ p * (p + 1)))) =
        (1 / ((2 : ℝ) ^ p * (p + 1))) *
          ∑ r ∈ range (2 ^ p),
            (thueMorseSign r : ℝ) * (P r - P (2 ^ p + r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hfactor, hsum]
  dsimp only [P]
  rw [choose_succ_two, pow_add, Nat.factorial_succ]
  push_cast
  field_simp

private lemma fabiusUniformPositiveSpline_one (x : ℝ) :
    fabiusUniformPositiveSpline 1 x =
      max 0 (min 1 (2 * x - 1 / 2)) := by
  let z : ℝ := 2 * x - 1 / 2
  have hformula : fabiusUniformPositiveSpline 1 x =
      max z 0 - max (z - 1) 0 := by
    simp only [sub_eq_add_neg]
    norm_num [fabiusUniformPositiveSpline, Finset.sum_range_succ,
      thueMorseSign, binaryWeight, z]
    ring_nf
  rw [hformula]
  change max z 0 - max (z - 1) 0 = max 0 (min 1 z)
  rcases le_total z 0 with hz0 | hz0
  · have hz1 : z ≤ 1 := hz0.trans (by norm_num)
    rw [max_eq_right hz0, max_eq_right (by linarith), min_eq_right hz1,
      max_eq_left hz0]
    ring
  · rcases le_total z 1 with hz1 | hz1
    · rw [max_eq_left hz0, max_eq_right (by linarith), min_eq_right hz1,
        max_eq_right hz0]
      ring
    · rw [max_eq_left hz0, max_eq_left (by linarith), min_eq_left hz1,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      ring

namespace ProbabilityRepresentation

/-- The first `p` coordinates of the random series. -/
def uniformPartialSum (p : ℕ) (ω : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range p, (ω i : ℝ) / 2 / (2 : ℝ) ^ i

/-- The empty prefix contributes nothing. -/
lemma uniformPartialSum_zero (ω : SampleSpace) : uniformPartialSum 0 ω = 0 := by
  simp [uniformPartialSum]

/-- Peels the last coordinate off the prefix.  This is the induction step used
by `uniformPartialSum_le_one_sub_inv_pow`. -/
lemma uniformPartialSum_succ (p : ℕ) (ω : SampleSpace) :
    uniformPartialSum (p + 1) ω =
      uniformPartialSum p ω + (ω p : ℝ) / 2 / (2 : ℝ) ^ p := by
  simp [uniformPartialSum, Finset.sum_range_succ]

/-- Peels the *first* coordinate off instead: the length `p + 1` prefix of `ω`
is the average of `ω 0` with the length `p` prefix of `tail ω`.  This
pointwise identity is what makes `uniformPartialDistribution_selfSimilar`
true. -/
lemma uniformPartialSum_succ_split (p : ℕ) (ω : SampleSpace) :
    uniformPartialSum (p + 1) ω =
      ((ω 0 : ℝ) + uniformPartialSum p (tail ω)) / 2 := by
  rw [uniformPartialSum, Finset.sum_range_succ']
  simp only [pow_zero, div_one]
  rw [uniformPartialSum]
  have hsum :
      (∑ k ∈ Finset.range p, (ω (k + 1) : ℝ) / 2 / (2 : ℝ) ^ (k + 1)) =
        (∑ k ∈ Finset.range p,
          ((tail ω k : ℝ) / 2 / (2 : ℝ) ^ k)) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [tail, pow_succ]
    ring
  rw [hsum]
  ring

/-- Measurability of the finite prefix map, needed to push `uniformProduct`
forward along it in `uniformPartialDistribution`. -/
lemma measurable_uniformPartialSum (p : ℕ) : Measurable (uniformPartialSum p) := by
  unfold uniformPartialSum
  fun_prop

private lemma summable_uniformCoordinateTerm (ω : SampleSpace) :
    Summable (fun i : ℕ => (ω i : ℝ) / 2 / (2 : ℝ) ^ i) := by
  refine (summable_geometric_two' 1).of_norm_bounded (fun i => ?_)
  have hi : 0 ≤ (ω i : ℝ) / 2 / (2 : ℝ) ^ i :=
    div_nonneg (div_nonneg (ω i).property.1 (by norm_num)) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hi]
  gcongr
  exact (ω i).property.2

/-- Distribution of the first `p` weighted uniform coordinates. -/
def uniformPartialDistribution (p : ℕ) : Measure ℝ :=
  uniformProduct.map (uniformPartialSum p)

/-- A pushforward of the product probability measure is again a probability
measure.  This instance is what makes Mathlib's `cdf` API applicable to
`uniformPartialDistribution`, hence available for `uniformPartialCDF`. -/
instance uniformPartialDistribution_isProbability (p : ℕ) :
    IsProbabilityMeasure (uniformPartialDistribution p) := by
  unfold uniformPartialDistribution
  exact Measure.isProbabilityMeasure_map (measurable_uniformPartialSum p).aemeasurable

/-- CDF of the first `p` weighted uniform coordinates. -/
def uniformPartialCDF (p : ℕ) (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf (uniformPartialDistribution p) x

/-- Every finite partial-sum CDF is monotone in its threshold. -/
theorem monotone_uniformPartialCDF (p : ℕ) :
    Monotone (uniformPartialCDF p) := by
  intro x y hxy
  exact ProbabilityTheory.monotone_cdf (uniformPartialDistribution p) hxy

/-- Unfolds the finite CDF as the measure of the sublevel set
`{ω | uniformPartialSum p ω ≤ x}` in the sample space.  The support bounds and
the comparisons with `weightedSumCDF` are all proved through this form. -/
lemma uniformPartialCDF_eq_measureReal (p : ℕ) (x : ℝ) :
    uniformPartialCDF p x =
      uniformProduct.real {ω | uniformPartialSum p ω ≤ x} := by
  rw [uniformPartialCDF, ProbabilityTheory.cdf_eq_real,
    uniformPartialDistribution,
    map_measureReal_apply (measurable_uniformPartialSum p) measurableSet_Iic]
  rfl

/-- The joint law of the head coordinate and the length `p` prefix of the tail
is the product of Lebesgue measure on `[0,1]` with
`uniformPartialDistribution p`.  This independence statement is the input to
`uniformPartialDistribution_selfSimilar`. -/
lemma uniformProduct_map_head_uniformPartialSum (p : ℕ) :
    uniformProduct.map
        (fun ω : SampleSpace => (ω 0, uniformPartialSum p (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (uniformPartialDistribution p) := by
  let g : Set.Icc (0 : ℝ) 1 × SampleSpace →
      Set.Icc (0 : ℝ) 1 × ℝ :=
    Prod.map id (uniformPartialSum p)
  have hg : Measurable g := by
    dsimp [g]
    exact measurable_id.prodMap (measurable_uniformPartialSum p)
  have h := congrArg (Measure.map g) uniformProduct_map_head_tail
  have hprod :
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
          (uniformPartialDistribution p) =
        Measure.map g
          ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod uniformProduct) := by
    dsimp [uniformPartialDistribution, g]
    simpa using (Measure.map_prod_map
      (volume : Measure (Set.Icc (0 : ℝ) 1)) uniformProduct
      measurable_id (measurable_uniformPartialSum p))
  rw [hprod, ← h]
  rw [Measure.map_map hg
    ((measurable_pi_apply 0).prodMk measurable_tail)]
  apply Measure.map_congr
  filter_upwards with ω
  rfl

/-- Self-similarity of the finite laws: the order `p + 1` distribution is the
image of `[0,1] × (order p distribution)` under `(u, z) ↦ (u + z) / 2`.
Integrating it out gives `uniformPartialCDF_eq_integral`. -/
lemma uniformPartialDistribution_selfSimilar (p : ℕ) :
    uniformPartialDistribution (p + 1) =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (uniformPartialDistribution p)).map
          (fun z => ((z.1 : ℝ) + z.2) / 2) := by
  change uniformProduct.map (uniformPartialSum (p + 1)) =
    ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
      (uniformProduct.map (uniformPartialSum p))).map
        (fun z => ((z.1 : ℝ) + z.2) / 2)
  have hjoint := uniformProduct_map_head_uniformPartialSum p
  change uniformProduct.map
      (fun ω : SampleSpace => (ω 0, uniformPartialSum p (tail ω))) =
    (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
      (uniformProduct.map (uniformPartialSum p)) at hjoint
  rw [← hjoint]
  rw [Measure.map_map (f := fun ω : SampleSpace =>
      (ω 0, uniformPartialSum p (tail ω)))
    (g := fun z : Set.Icc (0 : ℝ) 1 × ℝ =>
      ((z.1 : ℝ) + z.2) / 2)
    (by fun_prop)
    ((measurable_pi_apply 0).prodMk
      ((measurable_uniformPartialSum p).comp measurable_tail))]
  apply Measure.map_congr
  filter_upwards with ω
  exact uniformPartialSum_succ_split p ω

/-- Smoothing recurrence for the finite CDFs: the order `p + 1` CDF at `y` is
the average over `u ∈ [0,1]` of the order `p` CDF at `2 * y - u`.  It is the
probabilistic counterpart of `fabiusUniformPositiveSpline_smoothing`. -/
lemma uniformPartialCDF_eq_integral (p : ℕ) (y : ℝ) :
    uniformPartialCDF (p + 1) y =
      ∫ u : Set.Icc (0 : ℝ) 1, uniformPartialCDF p (2 * y - (u : ℝ)) := by
  let A : Set (Set.Icc (0 : ℝ) 1 × ℝ) :=
    {z | ((z.1 : ℝ) + z.2) / 2 ≤ y}
  have hA : MeasurableSet A := by
    apply measurableSet_le <;> fun_prop
  have hcombine : Measurable
      (fun z : Set.Icc (0 : ℝ) 1 × ℝ => ((z.1 : ℝ) + z.2) / 2) := by
    fun_prop
  rw [uniformPartialCDF, ProbabilityTheory.cdf_eq_real,
    uniformPartialDistribution_selfSimilar,
    map_measureReal_apply hcombine measurableSet_Iic]
  change ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
    (uniformPartialDistribution p)).real A = _
  calc
    ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (uniformPartialDistribution p)).real A =
        ∫ z, A.indicator (fun _ => (1 : ℝ)) z
          ∂((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
            (uniformPartialDistribution p)) := by
      symm
      exact integral_indicator_one hA
    _ = ∫ u : Set.Icc (0 : ℝ) 1,
        ∫ v : ℝ, A.indicator (fun _ => (1 : ℝ)) (u, v)
          ∂(uniformPartialDistribution p) := by
      apply integral_prod
      exact (integrable_const (1 : ℝ)).indicator hA
    _ = ∫ u : Set.Icc (0 : ℝ) 1,
        uniformPartialCDF p (2 * y - (u : ℝ)) := by
      apply integral_congr_ae
      filter_upwards with u
      let Au : Set ℝ := {v | (((u : ℝ) + v) / 2 : ℝ) ≤ y}
      have hAu : MeasurableSet Au := by
        apply measurableSet_le <;> fun_prop
      calc
        (∫ v : ℝ, A.indicator (fun _ => (1 : ℝ)) (u, v)
            ∂(uniformPartialDistribution p)) =
            ∫ v : ℝ, Au.indicator (fun _ => (1 : ℝ)) v
              ∂(uniformPartialDistribution p) := by
          apply integral_congr_ae
          filter_upwards with v
          rfl
        _ = (uniformPartialDistribution p).real Au :=
          integral_indicator_one hAu
        _ = uniformPartialCDF p (2 * y - (u : ℝ)) := by
          rw [uniformPartialCDF, ProbabilityTheory.cdf_eq_real]
          congr 2
          ext v
          simp only [Au, mem_setOf_eq, Set.mem_Iic]
          constructor <;> intro hv <;> linarith

/-- CDF of the partial random sum after the midpoint correction at scale `p`. -/
def uniformCenteredPartialCDF (p : ℕ) (x : ℝ) : ℝ :=
  uniformPartialCDF p (x - 1 / (2 : ℝ) ^ (p + 1))

/-- Midpoint correction preserves monotonicity of the finite CDF. -/
theorem monotone_uniformCenteredPartialCDF (p : ℕ) :
    Monotone (uniformCenteredPartialCDF p) := by
  intro x y hxy
  exact monotone_uniformPartialCDF p (sub_le_sub_right hxy _)

/-- The same smoothing recurrence for the midpoint-corrected CDFs; the
correction `1 / 2 ^ (p + 1)` is exactly the one carried along by
`u ↦ 2 * x - u`.  This is the step matched against
`fabiusUniformPositiveSpline_smoothing` in the induction identifying the two
families. -/
lemma uniformCenteredPartialCDF_eq_integral (p : ℕ) (x : ℝ) :
    uniformCenteredPartialCDF (p + 1) x =
      ∫ u : Set.Icc (0 : ℝ) 1,
        uniformCenteredPartialCDF p (2 * x - (u : ℝ)) := by
  rw [uniformCenteredPartialCDF, uniformPartialCDF_eq_integral]
  apply integral_congr_ae
  filter_upwards with u
  rw [uniformCenteredPartialCDF]
  congr 1
  rw [show p + 1 + 1 = (p + 1) + 1 by omega, pow_succ]
  field_simp
  ring

private lemma fabiusUniformPositiveSpline_one_eq_centeredPartialCDF (x : ℝ) :
    fabiusUniformPositiveSpline 1 x = uniformCenteredPartialCDF 1 x := by
  rw [fabiusUniformPositiveSpline_one, uniformCenteredPartialCDF,
    uniformPartialCDF_eq_measureReal]
  have hsum (ω : SampleSpace) : uniformPartialSum 1 ω = (ω 0 : ℝ) / 2 := by
    simp [uniformPartialSum]
  simp_rw [hsum]
  let z : ℝ := 2 * x - 1 / 2
  have hineq (ω : SampleSpace) :
      (ω 0 : ℝ) / 2 ≤ x - 1 / (2 : ℝ) ^ (1 + 1) ↔
        (ω 0 : ℝ) ≤ z := by
    dsimp [z]
    norm_num
    constructor <;> intro h <;> linarith
  simp_rw [hineq]
  change max 0 (min 1 z) = uniformProduct.real {ω | (ω 0 : ℝ) ≤ z}
  rcases lt_or_ge z 0 with hz0 | hz0
  · have hset : {ω : SampleSpace | (ω 0 : ℝ) ≤ z} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      linarith [(ω 0).property.1]
    rw [hset, measureReal_empty, min_eq_right (by linarith : z ≤ 1),
      max_eq_left hz0.le]
  · rcases le_or_gt z 1 with hz1 | hz1
    · let a : Set.Icc (0 : ℝ) 1 := ⟨z, hz0, hz1⟩
      have hset : {ω : SampleSpace | (ω 0 : ℝ) ≤ z} =
          (fun ω : SampleSpace => ω 0) ⁻¹' Iic a := by
        ext ω
        rfl
      rw [hset, ← map_measureReal_apply (measurable_pi_apply 0) measurableSet_Iic,
        coordinate_has_uniform_law, measureReal_def, unitInterval.volume_Iic]
      simp [a, hz0, hz1]
    · have hset : {ω : SampleSpace | (ω 0 : ℝ) ≤ z} = Set.univ := by
        ext ω
        simp only [mem_setOf_eq, Set.mem_univ, iff_true]
        exact (ω 0).property.2.trans hz1.le
      rw [hset, probReal_univ, min_eq_left hz1.le,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

private theorem fabiusUniformPositiveSpline_eq_centeredPartialCDF
    (p : ℕ) (hp : 0 < p) (x : ℝ) :
    fabiusUniformPositiveSpline p x = uniformCenteredPartialCDF p x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  clear hp
  induction j generalizing x with
  | zero => exact fabiusUniformPositiveSpline_one_eq_centeredPartialCDF x
  | succ j ih =>
      change fabiusUniformPositiveSpline ((j + 1) + 1) x =
        uniformCenteredPartialCDF ((j + 1) + 1) x
      rw [fabiusUniformPositiveSpline_smoothing (j + 1) (by omega),
        uniformCenteredPartialCDF_eq_integral]
      calc
        (∫ u in (0 : ℝ)..1,
            fabiusUniformPositiveSpline (j + 1) (2 * x - u)) =
            ∫ u in Set.Icc (0 : ℝ) 1,
              fabiusUniformPositiveSpline (j + 1) (2 * x - u) := by
          rw [integral_Icc_eq_integral_Ioc,
            intervalIntegral.integral_of_le (by norm_num)]
        _ = ∫ u : Set.Icc (0 : ℝ) 1,
            fabiusUniformPositiveSpline (j + 1) (2 * x - (u : ℝ)) := by
          symm
          simpa using (integral_subtype (G := ℝ) measurableSet_Icc
            (fun u : ℝ => fabiusUniformPositiveSpline (j + 1) (2 * x - u)))
        _ = ∫ u : Set.Icc (0 : ℝ) 1,
            uniformCenteredPartialCDF (j + 1) (2 * x - (u : ℝ)) := by
          apply integral_congr_ae
          filter_upwards with u
          exact ih (2 * x - (u : ℝ))

/-- In positive degree, on the fundamental interval `[0,1]`, the centered spline
is exactly the midpoint-corrected CDF of the first `p` weighted uniform
coordinates.  This is the bridge from the combinatorial Thue--Morse sum to
probability, and it supplies the monotonicity, the `[0,1]` range bound and the
convergence results below.  The all-degree wrapper
`fabiusUniformSpline_eq_centeredPartialCDF_all` appears after the separate
degree-zero bridge needed to prove it. -/
theorem fabiusUniformSpline_eq_centeredPartialCDF
    (p : ℕ) (hp : 0 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline p x = uniformCenteredPartialCDF p x := by
  rw [fabiusUniformSpline_eq_positiveSpline p hp hx,
    fabiusUniformPositiveSpline_eq_centeredPartialCDF p hp x]

/-- Every positive-degree centered finite spline is monotone on the
fundamental interval `[0,1]`. -/
theorem monotoneOn_fabiusUniformSpline
    (p : ℕ) (hp : 0 < p) :
    MonotoneOn (fabiusUniformSpline p) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [fabiusUniformSpline_eq_centeredPartialCDF p hp hx,
    fabiusUniformSpline_eq_centeredPartialCDF p hp hy]
  exact monotone_uniformCenteredPartialCDF p hxy

/-- Positive-degree compatibility form of the centered spline's `[0,1]` range
bound on the fundamental interval.  The all-degree theorem
`fabiusUniformSpline_mem_Icc_all` appears after the degree-zero CDF bridge.
Used in `FabiusFunction.FabiusComputableSpline` to see that the exact rational
spline value is nonnegative. -/
theorem fabiusUniformSpline_mem_Icc
    (p : ℕ) (hp : 0 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline p x ∈ Icc (0 : ℝ) 1 := by
  rw [fabiusUniformSpline_eq_centeredPartialCDF p hp hx]
  constructor
  · rw [uniformCenteredPartialCDF, uniformPartialCDF]
    exact ProbabilityTheory.cdf_nonneg (uniformPartialDistribution p) _
  · rw [uniformCenteredPartialCDF, uniformPartialCDF]
    exact ProbabilityTheory.cdf_le_one (uniformPartialDistribution p) _

/-- Absolute-value form of `fabiusUniformSpline_mem_Icc`: in positive degree the
centered spline is bounded by one on the fundamental interval `[0,1]`. -/
theorem abs_fabiusUniformSpline_le_one_of_mem_Icc
    (p : ℕ) (hp : 0 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |fabiusUniformSpline p x| ≤ 1 := by
  have hs := fabiusUniformSpline_mem_Icc p hp hx
  apply (abs_le).2
  constructor
  · linarith [hs.1]
  · exact hs.2

/-- The prefix sums are nonnegative, the coordinates lying in `[0,1]`.  This
gives the left support bound `uniformPartialCDF_eq_zero_of_neg`. -/
lemma uniformPartialSum_nonneg (p : ℕ) (ω : SampleSpace) :
    0 ≤ uniformPartialSum p ω := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (div_nonneg (ω i).property.1 (by norm_num)) (by positivity)

/-- Sharp upper endpoint of the first `p` weighted coordinates. -/
lemma uniformPartialSum_le_one_sub_inv_pow (p : ℕ) (ω : SampleSpace) :
    uniformPartialSum p ω ≤ 1 - 1 / (2 : ℝ) ^ p := by
  induction p with
  | zero => simp [uniformPartialSum]
  | succ p ih =>
      rw [uniformPartialSum_succ]
      calc
        uniformPartialSum p ω + (ω p : ℝ) / 2 / (2 : ℝ) ^ p ≤
            (1 - 1 / (2 : ℝ) ^ p) + 1 / 2 / (2 : ℝ) ^ p := by
          gcongr
          exact (ω p).property.2
        _ = 1 - 1 / (2 : ℝ) ^ (p + 1) := by
          rw [pow_succ]
          field_simp
          ring

/-- Truncation only loses mass: the length `p` prefix never exceeds the full
random series.  This is the lower half of `uniformPartialCDF_sandwich`. -/
lemma uniformPartialSum_le_weightedCoordinateSum (p : ℕ) (ω : SampleSpace) :
    uniformPartialSum p ω ≤ weightedCoordinateSum ω := by
  rw [uniformPartialSum, weightedCoordinateSum]
  exact (summable_uniformCoordinateTerm ω).sum_le_tsum (range p)
    (fun i hi =>
      div_nonneg (div_nonneg (ω i).property.1 (by norm_num)) (by positivity))

/-- Complementary tail bound: the full random series exceeds its length `p`
prefix by at most `1 / 2 ^ p`, by summing the geometric majorant.  This is the
upper half of `uniformPartialCDF_sandwich`. -/
lemma weightedCoordinateSum_le_uniformPartialSum_add (p : ℕ) (ω : SampleSpace) :
    weightedCoordinateSum ω ≤ uniformPartialSum p ω + 1 / (2 : ℝ) ^ p := by
  let f : ℕ → ℝ := fun i => (ω i : ℝ) / 2 / (2 : ℝ) ^ i
  let g : ℕ → ℝ := fun i => (1 : ℝ) / 2 / (2 : ℝ) ^ i
  have hf : Summable f := summable_uniformCoordinateTerm ω
  have hg : Summable g := summable_geometric_two' 1
  have htail : (∑' i : ℕ, f (i + p)) ≤ ∑' i : ℕ, g (i + p) := by
    apply Summable.tsum_le_tsum
    · intro i
      dsimp [f, g]
      gcongr
      exact (ω (i + p)).property.2
    · exact (summable_nat_add_iff p).2 hf
    · exact (summable_nat_add_iff p).2 hg
  have hsplitF := hf.sum_add_tsum_nat_add p
  have hsplitG := hg.sum_add_tsum_nat_add p
  rw [weightedCoordinateSum, uniformPartialSum]
  change (∑' i : ℕ, f i) ≤ (∑ i ∈ range p, f i) + 1 / (2 : ℝ) ^ p
  rw [← hsplitF]
  gcongr
  calc
    (∑' i : ℕ, f (i + p)) ≤ ∑' i : ℕ, g (i + p) := htail
    _ = 1 / (2 : ℝ) ^ p := by
      calc
        (∑' i : ℕ, g (i + p)) =
            (1 / (2 : ℝ) ^ p) * ∑' i : ℕ, g i := by
          have hfun : (fun i : ℕ => g (i + p)) =
              fun i : ℕ => (1 / (2 : ℝ) ^ p) * g i := by
            funext i
            simp only [g, pow_add]
            field_simp
          rw [hfun, tsum_mul_left]
        _ = 1 / (2 : ℝ) ^ p := by
          rw [show (∑' i : ℕ, g i) = 1 by
            simpa only [g] using tsum_geometric_two' 1]
          ring

/-- Quantitative pointwise error of truncating the weighted coordinate
series after `p` terms. -/
theorem abs_uniformPartialSum_sub_weightedCoordinateSum_le
    (p : ℕ) (ω : SampleSpace) :
    |uniformPartialSum p ω - weightedCoordinateSum ω| ≤
      1 / (2 : ℝ) ^ p := by
  rw [abs_of_nonpos (sub_nonpos.mpr
    (uniformPartialSum_le_weightedCoordinateSum p ω))]
  linarith [weightedCoordinateSum_le_uniformPartialSum_add p ω]

/-- The finite weighted-coordinate sums converge pointwise to the full
random series. -/
theorem uniformPartialSum_tendsto_weightedCoordinateSum (ω : SampleSpace) :
    Tendsto (fun p : ℕ => uniformPartialSum p ω) atTop
      (nhds (weightedCoordinateSum ω)) := by
  rw [weightedCoordinateSum]
  simpa only [uniformPartialSum] using
    (summable_uniformCoordinateTerm ω).hasSum.tendsto_sum_nat

/-- The partial-sum distribution has no mass below zero. -/
theorem uniformPartialCDF_eq_zero_of_neg
    (p : ℕ) {x : ℝ} (hx : x < 0) :
    uniformPartialCDF p x = 0 := by
  rw [uniformPartialCDF_eq_measureReal]
  have hset : {ω : SampleSpace | uniformPartialSum p ω ≤ x} = ∅ := by
    ext ω
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact not_le_of_gt (hx.trans_le (uniformPartialSum_nonneg p ω))
  rw [hset]
  simp

/-- The partial-sum CDF is one at and above its sharp upper endpoint. -/
theorem uniformPartialCDF_eq_one_of_max_le
    (p : ℕ) {x : ℝ} (hx : 1 - 1 / (2 : ℝ) ^ p ≤ x) :
    uniformPartialCDF p x = 1 := by
  rw [uniformPartialCDF_eq_measureReal]
  have hset : {ω : SampleSpace | uniformPartialSum p ω ≤ x} = Set.univ := by
    ext ω
    simp only [mem_setOf_eq, Set.mem_univ, iff_true]
    exact (uniformPartialSum_le_one_sub_inv_pow p ω).trans hx
  rw [hset, probReal_univ]

/-- In particular, the partial-sum CDF is one at and above one. -/
theorem uniformPartialCDF_eq_one_of_one_le
    (p : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    uniformPartialCDF p x = 1 := by
  apply uniformPartialCDF_eq_one_of_max_le
  have : 0 ≤ 1 / (2 : ℝ) ^ p := by positivity
  linarith

/-- Support bound for the midpoint-corrected partial CDF at its left edge. -/
theorem uniformCenteredPartialCDF_eq_zero_of_lt
    (p : ℕ) {x : ℝ} (hx : x < 1 / (2 : ℝ) ^ (p + 1)) :
    uniformCenteredPartialCDF p x = 0 := by
  apply uniformPartialCDF_eq_zero_of_neg
  simpa only [uniformCenteredPartialCDF] using sub_neg.mpr hx

/-- Support bound for the midpoint-corrected partial CDF at its right edge. -/
theorem uniformCenteredPartialCDF_eq_one_of_le
    (p : ℕ) {x : ℝ} (hx : 1 - 1 / (2 : ℝ) ^ (p + 1) ≤ x) :
    uniformCenteredPartialCDF p x = 1 := by
  apply uniformPartialCDF_eq_one_of_max_le
  have hpow : 1 / (2 : ℝ) ^ p =
      2 * (1 / (2 : ℝ) ^ (p + 1)) := by
    rw [pow_succ]
    field_simp
  rw [hpow]
  linarith

/-- At degree zero, the elementary step spline agrees with the centered
partial CDF throughout the fundamental interval. -/
theorem fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline 0 x = uniformCenteredPartialCDF 0 x := by
  by_cases hhalf : x < 1 / 2
  · rw [fabiusUniformSpline_eq_zero_of_lt_half 0 (by simpa using hhalf),
      uniformCenteredPartialCDF_eq_zero_of_lt 0 (by simpa using hhalf)]
  · have hhalf' : 1 / 2 ≤ x := le_of_not_gt hhalf
    have hlen : fabiusDiscreteLimitRangeLength x 0 = 1 := by
      rw [fabiusDiscreteLimitRangeLength, pow_zero, one_mul]
      apply (Nat.floor_eq_iff (by linarith [hx.1])).2
      constructor <;> norm_num <;> linarith [hhalf', hx.2]
    have hcdf : uniformCenteredPartialCDF 0 x = 1 :=
      uniformCenteredPartialCDF_eq_one_of_le 0 (by
        norm_num
        linarith)
    rw [fabiusUniformSpline_zero, hlen, hcdf]
    norm_num [thueMorseSign, binaryWeight]

/-- On `[0,1]`, every centered finite spline is exactly the midpoint-corrected
CDF of the first `p` weighted uniform coordinates.  This includes the
degree-zero step spline, whose inclusive jump is at `1 / 2`. -/
theorem fabiusUniformSpline_eq_centeredPartialCDF_all
    (p : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline p x = uniformCenteredPartialCDF p x := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc hx
  · exact fabiusUniformSpline_eq_centeredPartialCDF p hp hx

/-- Centered finite splines take values in `[0,1]` on the fundamental interval
in every degree, including the degree-zero step spline. -/
theorem fabiusUniformSpline_mem_Icc_all
    (p : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline p x ∈ Icc (0 : ℝ) 1 := by
  rw [fabiusUniformSpline_eq_centeredPartialCDF_all p hx,
    uniformCenteredPartialCDF, uniformPartialCDF]
  exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

/-- Centered finite splines are monotone on `[0,1]` in every degree,
including the degree-zero step spline. -/
theorem monotoneOn_fabiusUniformSpline_all (p : ℕ) :
    MonotoneOn (fabiusUniformSpline p) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [fabiusUniformSpline_eq_centeredPartialCDF_all p hx,
    fabiusUniformSpline_eq_centeredPartialCDF_all p hy]
  exact monotone_uniformCenteredPartialCDF p hxy

/-- Two-sided comparison of the finite CDF with the limiting CDF
`weightedSumCDF`: the truncation shows up only as the threshold shift
`1 / 2 ^ p`, never as an additive error on the value.  Squeezing this gives
`uniformPartialCDF_tendsto_weightedSumCDF`. -/
theorem uniformPartialCDF_sandwich (p : ℕ) (x : ℝ) :
    weightedSumCDF x ≤ uniformPartialCDF p x ∧
      uniformPartialCDF p x ≤ weightedSumCDF (x + 1 / (2 : ℝ) ^ p) := by
  simp only [weightedSumCDF_eq_measureReal, uniformPartialCDF_eq_measureReal]
  constructor
  · refine measureReal_mono (fun ω hω =>
      (uniformPartialSum_le_weightedCoordinateSum p ω).trans hω) ?_
    simp
  · refine measureReal_mono (fun ω hω => ?_) ?_
    change uniformPartialSum p ω ≤ x at hω
    exact (weightedCoordinateSum_le_uniformPartialSum_add p ω).trans
      (add_le_add_left hω _)
    simp

/-- The finite CDFs converge to `weightedSumCDF` at every real point, by
squeezing the sandwich between two arguments that tend to `x` and using
continuity of the limiting CDF. -/
theorem uniformPartialCDF_tendsto_weightedSumCDF (x : ℝ) :
    Tendsto (fun p : ℕ => uniformPartialCDF p x) atTop (nhds (weightedSumCDF x)) := by
  have hshift : Tendsto (fun p : ℕ => x + 1 / (2 : ℝ) ^ p)
      atTop (nhds x) := by
    have hhalf : Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ p) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hc : Tendsto (fun _ : ℕ => x) atTop (nhds x) := tendsto_const_nhds
    simpa only [one_div, inv_pow, add_zero] using hc.add hhalf
  have hupper : Tendsto
      (fun p : ℕ => weightedSumCDF (x + 1 / (2 : ℝ) ^ p))
      atTop (nhds (weightedSumCDF x)) :=
    continuous_weightedSumCDF.continuousAt.tendsto.comp hshift
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
  · exact fun p => (uniformPartialCDF_sandwich p x).1
  · exact fun p => (uniformPartialCDF_sandwich p x).2

/-- Midpoint-corrected form of `uniformPartialCDF_sandwich`, with the threshold
shifted symmetrically by `1 / 2 ^ (p + 1)`.  Together with the Lipschitz bound
for `fabiusReal` this yields the explicit `(2 ^ p)⁻¹` spline error proved in
`FabiusFunction.FabiusComputability`. -/
theorem uniformCenteredPartialCDF_sandwich (p : ℕ) (x : ℝ) :
    weightedSumCDF (x - 1 / (2 : ℝ) ^ (p + 1)) ≤
        uniformCenteredPartialCDF p x ∧
      uniformCenteredPartialCDF p x ≤
        weightedSumCDF (x + 1 / (2 : ℝ) ^ (p + 1)) := by
  rw [uniformCenteredPartialCDF]
  have hs := uniformPartialCDF_sandwich p (x - 1 / (2 : ℝ) ^ (p + 1))
  convert hs using 1
  rw [pow_succ]
  field_simp
  ring_nf

/-- The midpoint-corrected finite CDFs converge to `weightedSumCDF` at every
real point. -/
theorem uniformCenteredPartialCDF_tendsto_weightedSumCDF (x : ℝ) :
    Tendsto (fun p : ℕ => uniformCenteredPartialCDF p x)
      atTop (nhds (weightedSumCDF x)) := by
  have hhalf : Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ p)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdelta : Tendsto (fun p : ℕ => 1 / (2 : ℝ) ^ (p + 1))
      atTop (nhds 0) := by
    have h := hhalf.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ (p + 1))
      atTop (nhds 0) at h
    simpa only [one_div, inv_pow] using h
  have hargLower : Tendsto
      (fun p : ℕ => x - 1 / (2 : ℝ) ^ (p + 1)) atTop (nhds x) := by
    simpa only [sub_zero] using
      (show Tendsto (fun _ : ℕ => x) atTop (nhds x) from
        tendsto_const_nhds).sub hdelta
  have hargUpper : Tendsto
      (fun p : ℕ => x + 1 / (2 : ℝ) ^ (p + 1)) atTop (nhds x) := by
    simpa only [add_zero] using
      (show Tendsto (fun _ : ℕ => x) atTop (nhds x) from
        tendsto_const_nhds).add hdelta
  have hlower : Tendsto
      (fun p : ℕ => weightedSumCDF (x - 1 / (2 : ℝ) ^ (p + 1)))
      atTop (nhds (weightedSumCDF x)) :=
    continuous_weightedSumCDF.continuousAt.tendsto.comp hargLower
  have hupper : Tendsto
      (fun p : ℕ => weightedSumCDF (x + 1 / (2 : ℝ) ^ (p + 1)))
      atTop (nhds (weightedSumCDF x)) :=
    continuous_weightedSumCDF.continuousAt.tendsto.comp hargUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · exact fun p => (uniformCenteredPartialCDF_sandwich p x).1
  · exact fun p => (uniformCenteredPartialCDF_sandwich p x).2

/-- On the fundamental interval `[0,1]` the centered splines converge pointwise
to the bounded Fabius function.  The all-degree finite-CDF identification
transfers the convergence without discarding the degree-zero term. -/
theorem fabiusUniformSpline_tendsto_fabiusReal_of_mem_Icc
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p x) atTop
      (nhds (fabiusReal fabius x)) := by
  rw [← weightedSumCDF_eq_fabiusReal fabius fabius_spec x]
  apply (uniformCenteredPartialCDF_tendsto_weightedSumCDF x).congr'
  exact Eventually.of_forall fun p =>
    (fabiusUniformSpline_eq_centeredPartialCDF_all p hx).symm

/-- The same limit phrased through the signed global extension, still only on
`[0,1]`.  The block-translation argument in
`fabiusUniformSpline_tendsto_globalFabius` extends it to the whole nonnegative
axis. -/
theorem fabiusUniformSpline_tendsto_globalFabius_of_mem_Icc
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p x) atTop
      (nhds (globalFabius x)) := by
  rw [globalFabius, extendedFabius_eq_fabiusReal fabius fabius_spec hx]
  exact fabiusUniformSpline_tendsto_fabiusReal_of_mem_Icc hx

end ProbabilityRepresentation

/-- Centered finite splines are monotone on `[0,1]` in every degree.
This root-namespace alias exposes the probabilistic monotonicity theorem as
part of the primary spline API. -/
theorem monotoneOn_fabiusUniformSpline_all (p : ℕ) :
    MonotoneOn (fabiusUniformSpline p) (Icc (0 : ℝ) 1) :=
  ProbabilityRepresentation.monotoneOn_fabiusUniformSpline_all p

/-- Every centered finite spline is saturated at one on its last half-cell in
the fundamental interval.  The upper bound `x ≤ 1` is essential because the
spline continues by signed block translations beyond that interval. -/
theorem fabiusUniformSpline_eq_one_of_le
    (p : ℕ) {x : ℝ}
    (hx : 1 - 1 / (2 : ℝ) ^ (p + 1) ≤ x)
    (hx1 : x ≤ 1) :
    fabiusUniformSpline p x = 1 := by
  have hleft : 0 ≤ 1 - 1 / (2 : ℝ) ^ (p + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  rw [ProbabilityRepresentation.fabiusUniformSpline_eq_centeredPartialCDF_all
      p ⟨hleft.trans hx, hx1⟩,
    ProbabilityRepresentation.uniformCenteredPartialCDF_eq_one_of_le p hx]

/-- Every centered finite spline takes the value one at the right endpoint of
the fundamental interval, in every degree. -/
theorem fabiusUniformSpline_one_eq_one (p : ℕ) :
    fabiusUniformSpline p 1 = 1 := by
  apply fabiusUniformSpline_eq_one_of_le p
  · exact sub_le_self _ (by positivity)
  · exact le_rfl

/-- The centered finite splines converge pointwise on the whole nonnegative
axis to the signed global Fabius extension. -/
theorem fabiusUniformSpline_tendsto_globalFabius
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p x) atTop
      (nhds (globalFabius x)) := by
  let block : ℕ := ⌊x / 2⌋₊
  let y : ℝ := x - 2 * (block : ℝ)
  have hfloor : (block : ℝ) ≤ x / 2 := by
    dsimp [block]
    exact Nat.floor_le (div_nonneg hx (by norm_num))
  have hfloor' : x / 2 < (block : ℝ) + 1 := by
    dsimp [block]
    exact Nat.lt_floor_add_one (x / 2)
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy2 : y < 2 := by dsimp [y]; linarith
  have hxform : x = 2 * (block : ℝ) + y := by dsimp [y]; ring
  have hspline (p : ℕ) :
      fabiusUniformSpline p x =
        (thueMorseSign block : ℝ) * fabiusUniformSpline p y := by
    rw [hxform]
    exact fabiusUniformSpline_block_translate p block hy0 hy2
  have hglobal : globalFabius x =
      (thueMorseSign block : ℝ) * extendedFabius fabius y := by
    have hxblock := extendedFabius_eq_single_translate fabius fabius_spec block
      (x := x) (by rw [hxform]; linarith)
      (by rw [hxform]; linarith)
    have hyblock := extendedFabius_eq_single_translate fabius fabius_spec 0
      (x := y) (by norm_num; exact hy0) (by norm_num; exact hy2.le)
    rw [globalFabius, hxblock, hyblock]
    norm_num [binaryWeight, thueMorseSign]
    ring
  rw [show (fun p : ℕ => fabiusUniformSpline p x) =
      fun p => (thueMorseSign block : ℝ) * fabiusUniformSpline p y by
        funext p
        exact hspline p,
    hglobal]
  by_cases hy1 : y ≤ 1
  · have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨hy0, hy1⟩
    have hlim :=
      ProbabilityRepresentation.fabiusUniformSpline_tendsto_fabiusReal_of_mem_Icc
        hyI
    have hext := extendedFabius_eq_fabiusReal fabius fabius_spec hyI
    rw [hext]
    exact tendsto_const_nhds.mul hlim
  · let z : ℝ := y - 1
    have hzI : z ∈ Icc (0 : ℝ) 1 := by
      dsimp [z]
      constructor <;> linarith
    have hlim :=
      ProbabilityRepresentation.fabiusUniformSpline_tendsto_fabiusReal_of_mem_Icc
        hzI
    have hone (p : ℕ) :
        fabiusUniformSpline p y = 1 - fabiusUniformSpline p z := by
      have hyz : y = 1 + z := by dsimp [z]; ring
      rw [hyz]
      exact fabiusUniformSpline_one_add p hzI.1 hzI.2
    have hext : extendedFabius fabius y = 1 - fabiusReal fabius z := by
      have hyz : y = 1 + z := by dsimp [z]; ring
      rw [hyz]
      exact extendedFabius_one_add fabius fabius_spec hzI
    rw [show (fun p : ℕ => (thueMorseSign block : ℝ) *
        fabiusUniformSpline p y) =
        fun p => (thueMorseSign block : ℝ) *
          (1 - fabiusUniformSpline p z) by
          funext p
          rw [hone p],
      hext]
    exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hlim)

/-- The centered finite splines converge to the signed global extension on
the whole real line.  The nonpositive case is exact at every finite scale. -/
theorem fabiusUniformSpline_tendsto_globalFabius_all (x : ℝ) :
    Tendsto (fun p : ℕ => fabiusUniformSpline p x) atTop
      (nhds (globalFabius x)) := by
  rcases le_total 0 x with hx | hx
  · exact fabiusUniformSpline_tendsto_globalFabius hx
  · have hspline (p : ℕ) : fabiusUniformSpline p x = 0 :=
      fabiusUniformSpline_eq_zero_of_nonpos p hx
    have hglobal : globalFabius x = 0 := by
      change extendedFabius fabius x = 0
      exact extendedFabius_eq_zero_of_nonpos fabius fabius_spec hx
    simp [hspline, hglobal]

/-- Every centered finite spline is bounded in absolute value by one on the
nonnegative axis. -/
theorem abs_fabiusUniformSpline_le_one
    (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |fabiusUniformSpline p x| ≤ 1 := by
  let block : ℕ := ⌊x / 2⌋₊
  let y : ℝ := x - 2 * (block : ℝ)
  have hfloor : (block : ℝ) ≤ x / 2 := by
    dsimp [block]
    exact Nat.floor_le (div_nonneg hx (by norm_num))
  have hfloor' : x / 2 < (block : ℝ) + 1 := by
    dsimp [block]
    exact Nat.lt_floor_add_one (x / 2)
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy2 : y < 2 := by dsimp [y]; linarith
  have hxform : x = 2 * (block : ℝ) + y := by dsimp [y]; ring
  have hspline : fabiusUniformSpline p x =
      (thueMorseSign block : ℝ) * fabiusUniformSpline p y := by
    rw [hxform]
    exact fabiusUniformSpline_block_translate p block hy0 hy2
  have hsign : |(thueMorseSign block : ℝ)| = 1 := by
    rw [thueMorseSign]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [hspline, abs_mul, hsign, one_mul]
  by_cases hy1 : y ≤ 1
  · have hy := ProbabilityRepresentation.fabiusUniformSpline_mem_Icc_all
      p ⟨hy0, hy1⟩
    rw [abs_of_nonneg hy.1]
    exact hy.2
  · let z : ℝ := y - 1
    have hzI : z ∈ Icc (0 : ℝ) 1 := by
      dsimp [z]
      constructor <;> linarith
    have hz := ProbabilityRepresentation.fabiusUniformSpline_mem_Icc_all p hzI
    have hone : fabiusUniformSpline p y = 1 - fabiusUniformSpline p z := by
      have hyz : y = 1 + z := by dsimp [z]; ring
      rw [hyz]
      exact fabiusUniformSpline_one_add p hzI.1 hzI.2
    rw [hone, abs_of_nonneg (sub_nonneg.mpr hz.2)]
    linarith [hz.1]

end

end Fabius
