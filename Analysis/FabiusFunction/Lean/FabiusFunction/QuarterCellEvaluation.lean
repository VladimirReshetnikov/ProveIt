import FabiusFunction.PlateauConstant
import FabiusFunction.UniformSplineStrictMono
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Sum

/-!
# Closed-form evaluation of the quarter-anchor cell polynomial

`PlateauLocalization` identifies the centered spline
`fabiusUniformSpline p` on the closed cell of radius `2 ^ -(p+1)` about
`2 ^ -r` with the explicit polynomial
`uniformSplineCellPolynomial p (2 ^ (p - r))`, `PlateauDegree` shows
that polynomial has degree exactly `r`, and `PlateauConstant` evaluates
its *top* coefficient.  At the quarter anchor `r = 2` that leaves the
two lower coefficients unknown, and with them the one hypothesis that
`QuarterQuantile` and `UniformSplineStrictMono` still carry: the exact
local identity

`fabiusUniformSpline p (1/4 + z) = 5/72 + z + 4 z² - (4/9) 4^-(p+1)`
for `|z| ≤ 2^-(p+1)` and `2 ≤ p`.

This module proves that identity and discharges the hypothesis.

## The two missing moments

By `coeff_uniformSplineCellPolynomial` the degree-`j` coefficient of the
cell polynomial at the quarter anchor is a constant times the
half-shifted Thue--Morse moment

`M_q(m) = ∑_{k < 2^m} ε(k) (k + 1/2)^q`

at `m = p - 2` and `q = p - j`.  For `j = 2` this is the sharp order
`q = m`, evaluated by `sum_thueMorseSign_mul_half_shift_pow_self`.  For
`j = 1` and `j = 0` it is one and two orders *above* the block order,
where the Prouhet cancellation
`sum_thueMorseSign_mul_half_shift_pow_eq_zero` no longer applies.

The corpus has two neighbouring results, and neither hands over these
two values.  `sum_thueMorseSign_mul_pow_add` determines every
*unshifted* power moment over `ℚ`, but as a sum over
`Finset.finsuppAntidiag (range m)` rather than in closed form, and it
would still have to be pushed across the half shift and the cast
`ℚ → ℝ`.  `sum_thueMorseSign_mul_midpoint_pow_eq_zero` kills the
midpoint-centred moment of order `r` whenever `m + r` is odd: its
hypothesis holds at `r = m + 1` but fails at `r = m + 2`, where
`m + (m + 2)` is even.

Both moments are therefore proved here directly over `ℝ`, by induction
on the block order.  The engine is the doubling recursion
`ε(2^m + k) = -ε(k)` (`thueMorseSign_add_pow_two`) combined with the
binomial expansion of the shift and the vanishing of every moment below
the block order; the sharp moment is the only input for the first, and
the sharp moment together with the first for the second.

## What the identity needs

Writing `p = m + 2`, the three surviving coefficients come out as `4`,
`-1` and `5/72 - (1/9) 4^-(m+2)`, so the cell polynomial is
`4 X² - X + (5/72 - (1/9) 4^-(m+2))` and, at `X = 1/4 + z`, exactly the
displayed local polynomial `quarterLocalPoly (p+1) z`.

Two hypotheses of the display are checked here rather than assumed.
The index is `p + 1`, not `p`: `fabiusUniformSpline 2 (1/4) = 1/16`
(`fabiusUniformSpline_two_quarter`), whereas the `4^-p` reading would
make it `1/24`
(`fabiusUniformSpline_two_quarter_ne_shifted_exponent`).  And `2 ≤ p` is
necessary: `not_forall_quarterLocalPoly_of_lt_two` refutes the identity
at `p = 0` and `p = 1`, where both splines still vanish at `1/4`.

## Main declarations

* `sum_thueMorseSign_mul_half_shift_pow_succ` — **the moment one order
  above the block order**:
  `∑_{k<2^m} ε(k)(k+1/2)^(m+1) = (-1)^m (m+1)! 2^C(m,2) 2^m / 2`,
  with `sum_thueMorseSign_mul_half_shift_pow_succ_eq_neg_half` reading
  it as `-1/2` times the sharp moment of the doubled block.
* `sum_thueMorseSign_mul_half_shift_pow_add_two` — **the moment two
  orders above**:
  `∑_{k<2^m} ε(k)(k+1/2)^(m+2)
      = (-1)^m (m+2)! 2^C(m,2) (10·4^m - 1) / 72`.
* `coeff_uniformSplineCellPolynomial_quarter_two`,
  `coeff_uniformSplineCellPolynomial_quarter_one`,
  `coeff_uniformSplineCellPolynomial_quarter_zero` — **the three
  coefficients** of the quarter-anchor cell polynomial of
  `fabiusUniformSpline (m+2)`: `4`, `-1` and `5/72 - (1/9)4^-(m+2)`.
* `natDegree_uniformSplineCellPolynomial_quarter_eq`,
  `eval_uniformSplineCellPolynomial_quarter` — the cell polynomial has
  degree exactly `2` and equals `4 X² - X + (5/72 - (1/9)4^-(m+2))` at
  every real point.
* `fabiusUniformSpline_quarter_cell` — **the closed-form evaluation**:
  for `2 ≤ p` and `|z| ≤ 2^-(p+1)`,
  `fabiusUniformSpline p (1/4 + z) = 5/72 + z + 4z² - (4/9)4^-(p+1)`.
* `fabiusUniformSpline_eq_quarterLocalPoly` — the same identity in the
  centred `quarterLocalPoly` form used by the quantile chain.
* `fabiusUniformSpline_zero_quarter`,
  `fabiusUniformSpline_one_quarter`,
  `not_forall_quarterLocalPoly_of_lt_two` — **`2 ≤ p` is necessary**.
* `fabiusUniformSpline_two_quarter`,
  `fabiusUniformSpline_two_quarter_ne_shifted_exponent` — **the index
  shift is real**.
* `existsUnique_fabiusUniformSpline_eq_quarterAnchor`,
  `eq_quarterQuantile_of_fabiusUniformSpline_eq`,
  `fabiusUniformSpline_quarterQuantile`,
  `fabiusUniformSpline_quarterQuantile_eq_fabiusReal_of_two_le`,
  `strictMonoOn_fabiusUniformSpline_quarterCell_of_two_le` — **the
  unconditional quantile statements**: the hypothesis carried by
  `UniformSplineStrictMono` is now discharged.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-! ### Small arithmetic inputs -/

/-- The Thue--Morse sign at the origin, as a real number. -/
private theorem thueMorseSign_zero_cast :
    (thueMorseSign 0 : ℝ) = 1 := by
  norm_num [thueMorseSign, binaryWeight]

/-- `2 · C(m+2, m) = (m+2)(m+1)`, by Pascal's rule. -/
private theorem two_mul_choose_add_two (m : ℕ) :
    2 * ((m + 2).choose m) = (m + 2) * (m + 1) := by
  induction m with
  | zero => decide
  | succ n ih =>
      have hp : (n + 3).choose (n + 1)
          = (n + 2).choose n + (n + 2).choose (n + 1) :=
        Nat.choose_succ_succ' (n + 2) n
      have hr : (n + 2).choose (n + 1) = n + 2 :=
        Nat.choose_succ_self_right (n + 1)
      show 2 * ((n + 3).choose (n + 1)) = (n + 3) * (n + 2)
      rw [hp, hr, Nat.mul_add, ih]
      ring

/-- The shift of `two_mul_choose_add_two` used at the next block. -/
private theorem two_mul_choose_add_three (m : ℕ) :
    2 * ((m + 3).choose (m + 1)) = (m + 3) * (m + 2) :=
  two_mul_choose_add_two (m + 1)

/-- `6 · C(m+3, m) = (m+3)(m+2)(m+1)`, by Pascal's rule. -/
private theorem six_mul_choose_add_three (m : ℕ) :
    6 * ((m + 3).choose m) = (m + 3) * ((m + 2) * (m + 1)) := by
  induction m with
  | zero => decide
  | succ n ih =>
      have hp : (n + 4).choose (n + 1)
          = (n + 3).choose n + (n + 3).choose (n + 1) :=
        Nat.choose_succ_succ' (n + 3) n
      have hr : 2 * ((n + 3).choose (n + 1)) = (n + 3) * (n + 2) :=
        two_mul_choose_add_three n
      have h6 : 6 * ((n + 3).choose (n + 1))
          = 3 * ((n + 3) * (n + 2)) := by
        calc 6 * ((n + 3).choose (n + 1))
            = 3 * (2 * ((n + 3).choose (n + 1))) := by ring
          _ = 3 * ((n + 3) * (n + 2)) := by rw [hr]
      show 6 * ((n + 4).choose (n + 1))
        = (n + 4) * ((n + 3) * (n + 2))
      rw [hp, Nat.mul_add, ih, h6]
      ring

private theorem cast_choose_add_two (m : ℕ) :
    ((m + 2).choose m : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 := by
  have h1 : (2 : ℝ) * ((m + 2).choose m : ℝ)
      = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    exact_mod_cast two_mul_choose_add_two m
  linarith

private theorem cast_choose_add_three (m : ℕ) :
    ((m + 3).choose m : ℝ)
      = ((m : ℝ) + 3) * (((m : ℝ) + 2) * ((m : ℝ) + 1)) / 6 := by
  have h1 : (6 : ℝ) * ((m + 3).choose m : ℝ)
      = ((m : ℝ) + 3) * (((m : ℝ) + 2) * ((m : ℝ) + 1)) := by
    exact_mod_cast six_mul_choose_add_three m
  linarith

private theorem cast_choose_add_three_succ (m : ℕ) :
    ((m + 3).choose (m + 1) : ℝ)
      = ((m : ℝ) + 3) * ((m : ℝ) + 2) / 2 := by
  have h1 : (2 : ℝ) * ((m + 3).choose (m + 1) : ℝ)
      = ((m : ℝ) + 3) * ((m : ℝ) + 2) := by
    exact_mod_cast two_mul_choose_add_three m
  linarith

/-- Peel the last three summands off a range sum. -/
private theorem sum_range_peel_three {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2 + 1), f i
      = ∑ i ∈ Finset.range n, f i + f n + f (n + 1) + f (n + 2) := by
  have h2 : ∑ i ∈ Finset.range (n + 2 + 1), f i
      = ∑ i ∈ Finset.range (n + 2), f i + f (n + 2) :=
    Finset.sum_range_succ f (n + 2)
  have h1 : ∑ i ∈ Finset.range (n + 2), f i
      = ∑ i ∈ Finset.range (n + 1), f i + f (n + 1) :=
    Finset.sum_range_succ f (n + 1)
  have h0 : ∑ i ∈ Finset.range (n + 1), f i
      = ∑ i ∈ Finset.range n, f i + f n :=
    Finset.sum_range_succ f n
  rw [h2, h1, h0]

/-- Peel the last four summands off a range sum. -/
private theorem sum_range_peel_four {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 3 + 1), f i
      = ∑ i ∈ Finset.range n, f i + f n + f (n + 1) + f (n + 2)
        + f (n + 3) := by
  have h3 : ∑ i ∈ Finset.range (n + 3 + 1), f i
      = ∑ i ∈ Finset.range (n + 2 + 1), f i + f (n + 3) :=
    Finset.sum_range_succ f (n + 3)
  rw [h3, sum_range_peel_three]

/-! ### The half-shifted Thue--Morse moments -/

/-- The half-shifted Thue--Morse moment of order `q` over the block of
order `m`: `∑_{k < 2^m} ε(k) (k + 1/2)^q`.  A private abbreviation for
the induction below; the public statements are the explicit sums. -/
private noncomputable def halfShiftMoment (m q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ m),
    (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ q

private theorem halfShiftMoment_eq_zero {m q : ℕ} (hq : q < m) :
    halfShiftMoment m q = 0 := by
  rw [halfShiftMoment]
  exact sum_thueMorseSign_mul_half_shift_pow_eq_zero m q hq

private theorem halfShiftMoment_self (m : ℕ) :
    halfShiftMoment m m
      = (-1 : ℝ) ^ m * (m.factorial : ℝ) * 2 ^ m.choose 2 := by
  rw [halfShiftMoment]
  exact sum_thueMorseSign_mul_half_shift_pow_self m

/-- **Binomial expansion of a shift.**  Translating the half-shifted
argument by `t` expands the moment of order `q` into the moments of all
orders `i ≤ q`, with the binomial weights `C(q,i) t^(q-i)`. -/
private theorem halfShiftMoment_shift (m q : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (2 ^ m),
        (thueMorseSign k : ℝ) * (((k : ℝ) + 1 / 2) + t) ^ q
      = ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) * t ^ (q - i) * halfShiftMoment m i := by
  have hexp : ∑ k ∈ Finset.range (2 ^ m),
      (thueMorseSign k : ℝ) * (((k : ℝ) + 1 / 2) + t) ^ q
      = ∑ k ∈ Finset.range (2 ^ m), ∑ i ∈ Finset.range (q + 1),
          ((q.choose i : ℝ) * t ^ (q - i)) *
            ((thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ i) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_pow ((k : ℝ) + 1 / 2) t q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [halfShiftMoment, Finset.mul_sum]

/-- **The doubling recursion.**  Splitting the block of order `m + 1`
into its two halves and flipping the sign on the upper half
(`thueMorseSign_add_pow_two`) writes the moment at level `m + 1` as the
moment at level `m` minus the moment of the translate. -/
private theorem halfShiftMoment_succ (m q : ℕ) :
    halfShiftMoment (m + 1) q
      = halfShiftMoment m q
        - ∑ k ∈ Finset.range (2 ^ m),
            (thueMorseSign k : ℝ) *
              (((k : ℝ) + 1 / 2) + (2 : ℝ) ^ m) ^ q := by
  have hsplit : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by
    rw [pow_succ, Nat.mul_two]
  have hsecond : ∑ k ∈ Finset.range (2 ^ m),
      (thueMorseSign (2 ^ m + k) : ℝ) *
          (((2 ^ m + k : ℕ) : ℝ) + 1 / 2) ^ q
      = -∑ k ∈ Finset.range (2 ^ m),
          (thueMorseSign k : ℝ) *
            (((k : ℝ) + 1 / 2) + (2 : ℝ) ^ m) ^ q := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < 2 ^ m := Finset.mem_range.mp hk
    have hbase : ((2 ^ m + k : ℕ) : ℝ) + 1 / 2
        = ((k : ℝ) + 1 / 2) + (2 : ℝ) ^ m := by
      push_cast
      ring
    rw [thueMorseSign_add_pow_two m k hklt, hbase, Int.cast_neg,
      neg_mul]
  rw [halfShiftMoment, halfShiftMoment, hsplit, Finset.sum_range_add,
    hsecond]
  ring

private theorem halfShiftMoment_succ_expand (m q : ℕ) :
    halfShiftMoment (m + 1) q
      = halfShiftMoment m q
        - ∑ i ∈ Finset.range (q + 1),
            (q.choose i : ℝ) * ((2 : ℝ) ^ m) ^ (q - i)
              * halfShiftMoment m i := by
  rw [halfShiftMoment_succ, halfShiftMoment_shift]

/-- The recursion one order above the block order.  The moment
`halfShiftMoment m (m + 2)` cancels between the two sides, so this is a
closed recursion in the sharp moment and the moment one order up. -/
private theorem halfShiftMoment_rec_one (m : ℕ) :
    halfShiftMoment (m + 1) (m + 2)
      = -(((m + 2).choose m : ℝ) * ((2 : ℝ) ^ m) ^ 2
            * halfShiftMoment m m
          + ((m : ℝ) + 2) * (2 : ℝ) ^ m
            * halfShiftMoment m (m + 1)) := by
  have hcs : (m + 2).choose (m + 1) = m + 2 :=
    Nat.choose_succ_self_right (m + 1)
  have hzero : ∑ i ∈ Finset.range m,
      ((m + 2).choose i : ℝ) * ((2 : ℝ) ^ m) ^ (m + 2 - i)
        * halfShiftMoment m i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [halfShiftMoment_eq_zero (Finset.mem_range.mp hi), mul_zero]
  rw [halfShiftMoment_succ_expand, sum_range_peel_three, hzero,
    show m + 2 - m = 2 by omega,
    show m + 2 - (m + 1) = 1 by omega,
    show m + 2 - (m + 2) = 0 by omega,
    hcs, Nat.choose_self, pow_one, pow_zero]
  push_cast
  ring

/-- The recursion two orders above the block order.  The moment
`halfShiftMoment m (m + 3)` cancels between the two sides. -/
private theorem halfShiftMoment_rec_two (m : ℕ) :
    halfShiftMoment (m + 1) (m + 3)
      = -(((m + 3).choose m : ℝ) * ((2 : ℝ) ^ m) ^ 3
            * halfShiftMoment m m
          + ((m + 3).choose (m + 1) : ℝ) * ((2 : ℝ) ^ m) ^ 2
            * halfShiftMoment m (m + 1)
          + ((m : ℝ) + 3) * (2 : ℝ) ^ m
            * halfShiftMoment m (m + 2)) := by
  have hcs : (m + 3).choose (m + 2) = m + 3 :=
    Nat.choose_succ_self_right (m + 2)
  have hzero : ∑ i ∈ Finset.range m,
      ((m + 3).choose i : ℝ) * ((2 : ℝ) ^ m) ^ (m + 3 - i)
        * halfShiftMoment m i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [halfShiftMoment_eq_zero (Finset.mem_range.mp hi), mul_zero]
  rw [halfShiftMoment_succ_expand, sum_range_peel_four, hzero,
    show m + 3 - m = 3 by omega,
    show m + 3 - (m + 1) = 2 by omega,
    show m + 3 - (m + 2) = 1 by omega,
    show m + 3 - (m + 3) = 0 by omega,
    hcs, Nat.choose_self, pow_one, pow_zero]
  push_cast
  ring

/-! ### The two closed forms -/

private theorem factorial_cast_succ (m : ℕ) :
    ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
  have h : ((m + 1).factorial : ℕ) = (m + 1) * m.factorial :=
    Nat.factorial_succ m
  rw [h, Nat.cast_mul]
  norm_num

private theorem factorial_cast_add_two (m : ℕ) :
    ((m + 2).factorial : ℝ)
      = ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
  have h : ((m + 2).factorial : ℕ) = (m + 2) * (m + 1).factorial :=
    Nat.factorial_succ (m + 1)
  rw [h, Nat.cast_mul]
  norm_num

private theorem factorial_cast_add_three (m : ℕ) :
    ((m + 3).factorial : ℝ)
      = ((m : ℝ) + 3) * ((m + 2).factorial : ℝ) := by
  have h : ((m + 3).factorial : ℕ) = (m + 3) * (m + 2).factorial :=
    Nat.factorial_succ (m + 2)
  rw [h, Nat.cast_mul]
  norm_num

private theorem two_pow_choose_succ (m : ℕ) :
    (2 : ℝ) ^ ((m + 1).choose 2)
      = 2 ^ m.choose 2 * (2 : ℝ) ^ m := by
  rw [choose_succ_two m, pow_add]

private theorem four_pow_eq_two_pow_sq (m : ℕ) :
    (4 : ℝ) ^ m = (2 : ℝ) ^ m * (2 : ℝ) ^ m := by
  rw [← mul_pow]
  norm_num

private theorem halfShiftMoment_order_succ (m : ℕ) :
    halfShiftMoment m (m + 1)
      = (-1 : ℝ) ^ m * ((m + 1).factorial : ℝ) * 2 ^ m.choose 2
          * 2 ^ m / 2 := by
  induction m with
  | zero =>
      have hc : Nat.choose 0 2 = 0 := by decide
      show halfShiftMoment 0 1
        = (-1 : ℝ) ^ 0 * ((1 : ℕ).factorial : ℝ)
            * 2 ^ (Nat.choose 0 2) * 2 ^ 0 / 2
      rw [halfShiftMoment, hc, pow_zero (2 : ℕ), Finset.sum_range_one,
        thueMorseSign_zero_cast]
      norm_num [Nat.factorial]
  | succ m ih =>
      show halfShiftMoment (m + 1) (m + 2)
        = (-1 : ℝ) ^ (m + 1) * ((m + 2).factorial : ℝ)
            * 2 ^ ((m + 1).choose 2) * 2 ^ (m + 1) / 2
      rw [halfShiftMoment_rec_one, halfShiftMoment_self, ih,
        cast_choose_add_two, factorial_cast_add_two,
        factorial_cast_succ, two_pow_choose_succ,
        pow_succ (-1 : ℝ) m, pow_succ (2 : ℝ) m]
      ring

private theorem halfShiftMoment_order_add_two (m : ℕ) :
    halfShiftMoment m (m + 2)
      = (-1 : ℝ) ^ m * ((m + 2).factorial : ℝ) * 2 ^ m.choose 2
          * (10 * 4 ^ m - 1) / 72 := by
  induction m with
  | zero =>
      have hc : Nat.choose 0 2 = 0 := by decide
      show halfShiftMoment 0 2
        = (-1 : ℝ) ^ 0 * ((2 : ℕ).factorial : ℝ)
            * 2 ^ (Nat.choose 0 2) * (10 * 4 ^ 0 - 1) / 72
      rw [halfShiftMoment, hc, pow_zero (2 : ℕ), Finset.sum_range_one,
        thueMorseSign_zero_cast]
      norm_num [Nat.factorial]
  | succ m ih =>
      show halfShiftMoment (m + 1) (m + 3)
        = (-1 : ℝ) ^ (m + 1) * ((m + 3).factorial : ℝ)
            * 2 ^ ((m + 1).choose 2) * (10 * 4 ^ (m + 1) - 1) / 72
      rw [halfShiftMoment_rec_two, halfShiftMoment_self,
        halfShiftMoment_order_succ, ih, cast_choose_add_three,
        cast_choose_add_three_succ, factorial_cast_add_three,
        factorial_cast_add_two, factorial_cast_succ,
        two_pow_choose_succ, pow_succ (-1 : ℝ) m, pow_succ (4 : ℝ) m,
        four_pow_eq_two_pow_sq]
      ring

/-- **The half-shifted moment one order above the block order.**

`∑_{k < 2^m} ε(k) (k + 1/2)^(m+1) = (-1)^m (m+1)! 2^C(m,2) 2^m / 2`.

Below the block order the sum vanishes
(`sum_thueMorseSign_mul_half_shift_pow_eq_zero`) and at the block order
it is the sharp Prouhet value
(`sum_thueMorseSign_mul_half_shift_pow_self`); this is the next moment
along. -/
theorem sum_thueMorseSign_mul_half_shift_pow_succ (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m),
        (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ (m + 1) =
      (-1 : ℝ) ^ m * ((m + 1).factorial : ℝ) * 2 ^ m.choose 2
        * 2 ^ m / 2 :=
  halfShiftMoment_order_succ m

/-- **The half-shifted moment two orders above the block order.**

`∑_{k < 2^m} ε(k) (k + 1/2)^(m+2)
    = (-1)^m (m+2)! 2^C(m,2) (10·4^m - 1) / 72`.

The corpus midpoint parity rule
`sum_thueMorseSign_mul_midpoint_pow_eq_zero` does not reach this value:
its hypothesis is `Odd (m + r)`, and here `r = m + 2`. -/
theorem sum_thueMorseSign_mul_half_shift_pow_add_two (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m),
        (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ (m + 2) =
      (-1 : ℝ) ^ m * ((m + 2).factorial : ℝ) * 2 ^ m.choose 2
        * (10 * 4 ^ m - 1) / 72 :=
  halfShiftMoment_order_add_two m

/-- **The moment one order up, read against the doubled block.**  The
order `m + 1` half-shifted moment over the block of order `m` is exactly
`-1/2` times the *sharp* moment of the same order over the block of
order `m + 1`. -/
theorem sum_thueMorseSign_mul_half_shift_pow_succ_eq_neg_half (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m),
        (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ (m + 1) =
      -(1 / 2) * ∑ k ∈ Finset.range (2 ^ (m + 1)),
        (thueMorseSign k : ℝ) * ((k : ℝ) + 1 / 2) ^ (m + 1) := by
  rw [sum_thueMorseSign_mul_half_shift_pow_succ,
    sum_thueMorseSign_mul_half_shift_pow_self (m + 1),
    two_pow_choose_succ, pow_succ (-1 : ℝ) m]
  ring

/-! ### The three coefficients at the quarter anchor -/

private theorem two_pow_choose_add_two (m : ℕ) :
    (2 : ℝ) ^ ((m + 2).choose 2)
      = 2 ^ m.choose 2 * (2 : ℝ) ^ m * (2 : ℝ) ^ m * 2 := by
  have h : (m + 2).choose 2 = m.choose 2 + m + m + 1 := by
    have h1 : (m + 1).choose 2 = m.choose 2 + m := choose_succ_two m
    have h2 : (m + 2).choose 2 = (m + 1).choose 2 + (m + 1) :=
      choose_succ_two (m + 1)
    omega
  rw [h, pow_add, pow_add, pow_add, pow_one]

private theorem quarter_den_ne_zero (m : ℕ) :
    (2 : ℝ) ^ ((m + 2).choose 2) * ((m + 2).factorial : ℝ) ≠ 0 := by
  have h1 : ((m + 2).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (by positivity) h1

private theorem neg_one_pow_add_two (m : ℕ) :
    (-1 : ℝ) ^ (m + 2) = (-1 : ℝ) ^ m := by
  rw [pow_add]
  norm_num

/-- **The quadratic coefficient at the quarter anchor.**  This is the
`r = 2` instance of the corpus plateau coefficient
`coeff_uniformSplineCellPolynomial_dyadic`, whose value
`2 ^ C(r+1,2) / r !` is `2 ^ 3 / 2 = 4`. -/
theorem coeff_uniformSplineCellPolynomial_quarter_two (m : ℕ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).coeff 2 = 4 := by
  have hm : m + 2 - 2 = m := by omega
  have hc : (2 + 1).choose 2 = 3 := by decide
  have hf : Nat.factorial 2 = 2 := by decide
  have h := coeff_uniformSplineCellPolynomial_dyadic
    (p := m + 2) (r := 2) (by omega)
  rw [hm] at h
  rw [h, hc, hf]
  norm_num

/-- **The linear coefficient at the quarter anchor.**  Here the moment
one order above the block order enters, and every power of two, sign
and factorial cancels: the coefficient is exactly `-1`, with no
dependence on `m`. -/
theorem coeff_uniformSplineCellPolynomial_quarter_one (m : ℕ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).coeff 1 = -1 := by
  have hsub : m + 2 - 1 = m + 1 := by omega
  have h2 : (2 : ℝ) ^ (m + 2) = (2 : ℝ) ^ m * 4 := by
    rw [pow_add]
    norm_num
  rw [coeff_uniformSplineCellPolynomial, hsub, Nat.choose_one_right,
    pow_one, div_mul_eq_mul_div, div_eq_iff (quarter_den_ne_zero m),
    sum_thueMorseSign_mul_half_shift_pow_succ, neg_one_pow_add_two,
    two_pow_choose_add_two, factorial_cast_add_two, h2]
  push_cast
  rcases Nat.even_or_odd m with hpar | hpar <;>
    rw [hpar.neg_one_pow] <;> ring

private theorem coeff_quarter_zero_mul (m : ℕ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).coeff 0
        * (144 * ((2 : ℝ) ^ m * (2 : ℝ) ^ m))
      = 10 * ((2 : ℝ) ^ m * (2 : ℝ) ^ m) - 1 := by
  rw [coeff_uniformSplineCellPolynomial, Nat.sub_zero,
    Nat.choose_zero_right, pow_zero, div_mul_eq_mul_div,
    div_mul_eq_mul_div, div_eq_iff (quarter_den_ne_zero m),
    sum_thueMorseSign_mul_half_shift_pow_add_two, neg_one_pow_add_two,
    two_pow_choose_add_two, four_pow_eq_two_pow_sq]
  push_cast
  rcases Nat.even_or_odd m with hpar | hpar <;>
    rw [hpar.neg_one_pow] <;> ring

/-- **The constant coefficient at the quarter anchor.**  This is where
the moment two orders above the block order enters, and it is the only
one of the three coefficients that still depends on the level:

`[X^0] uniformSplineCellPolynomial (m+2) (2^m) = 5/72 - (1/9) 4^-(m+2)`.

The constant `5/72` is the anchor value `F(1/4)` of the corpus
`fabiusReal_one_quarter`. -/
theorem coeff_uniformSplineCellPolynomial_quarter_zero (m : ℕ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).coeff 0
      = 5 / 72 - 1 / 9 * (1 / 4 : ℝ) ^ (m + 2) := by
  have hinv : (1 / 4 : ℝ) ^ m * ((2 : ℝ) ^ m * (2 : ℝ) ^ m) = 1 := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have h4 : (1 / 4 : ℝ) ^ (m + 2) = (1 / 4 : ℝ) ^ m * (1 / 16) := by
    rw [pow_add]
    norm_num
  have hU : (144 : ℝ) * ((2 : ℝ) ^ m * (2 : ℝ) ^ m) ≠ 0 := by
    positivity
  refine mul_right_cancel₀ hU ?_
  rw [coeff_quarter_zero_mul, h4]
  linear_combination hinv

/-! ### The cell polynomial at the quarter anchor -/

private theorem natDegree_quarter_le (m : ℕ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).natDegree ≤ 2 := by
  have hm : m + 2 - 2 = m := by omega
  have h := natDegree_uniformSplineCellPolynomial_dyadic_le
    (p := m + 2) (r := 2) (by omega)
  rwa [hm] at h

/-- **The quarter-anchor cell polynomial is a genuine quadratic**: its
degree is exactly `2`, the `r = 2` instance of the corpus sharpness
statement `natDegree_uniformSplineCellPolynomial_dyadic`. -/
theorem natDegree_uniformSplineCellPolynomial_quarter_eq (m : ℕ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).natDegree = 2 := by
  have hm : m + 2 - 2 = m := by omega
  have h := natDegree_uniformSplineCellPolynomial_dyadic
    (p := m + 2) (r := 2) (by omega)
  rwa [hm] at h

/-- **The closed form of the quarter-anchor cell polynomial.**  At every
real point,

`eval x (uniformSplineCellPolynomial (m+2) (2^m))
    = 4 x² - x + (5/72 - (1/9) 4^-(m+2))`.

The polynomial knows nothing about the cell; only inside the cell does
this say anything about the spline. -/
theorem eval_uniformSplineCellPolynomial_quarter (m : ℕ) (x : ℝ) :
    (uniformSplineCellPolynomial (m + 2) (2 ^ m)).eval x
      = 4 * x ^ 2 - x + (5 / 72 - 1 / 9 * (1 / 4 : ℝ) ^ (m + 2)) := by
  have hlt :
      (uniformSplineCellPolynomial (m + 2) (2 ^ m)).natDegree < 3 :=
    lt_of_le_of_lt (natDegree_quarter_le m) (by norm_num)
  have hsum : ∀ Q : Polynomial ℝ,
      ∑ i ∈ Finset.range 3, Q.coeff i * x ^ i
        = Q.coeff 0 * x ^ 0 + Q.coeff 1 * x ^ 1
          + Q.coeff 2 * x ^ 2 := by
    intro Q
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
  rw [Polynomial.eval_eq_sum_range' hlt x, hsum,
    coeff_uniformSplineCellPolynomial_quarter_zero,
    coeff_uniformSplineCellPolynomial_quarter_one,
    coeff_uniformSplineCellPolynomial_quarter_two]
  ring

/-! ### The exact local identity for the spline -/

/-- **The closed-form evaluation of the spline on the quarter cell.**
For `2 ≤ p` and `|z| ≤ 2^-(p+1)`,

`fabiusUniformSpline p (1/4 + z) = 5/72 + z + 4 z² - (4/9) 4^-(p+1)`.

The cell is the corpus localization cell
`fabiusUniformSpline_eqOn_cellPolynomial_dyadic` at `r = 2`, whose
`hrp : r ≤ p` is exactly the hypothesis `2 ≤ p`; the value is
`eval_uniformSplineCellPolynomial_quarter` re-centred at `1/4`. -/
theorem fabiusUniformSpline_quarter_cell {p : ℕ} (hp : 2 ≤ p) {z : ℝ}
    (hz : |z| ≤ (1 / 2 : ℝ) ^ (p + 1)) :
    fabiusUniformSpline p (1 / 4 + z)
      = 5 / 72 + z + 4 * z ^ 2 - 4 / 9 * (1 / 4 : ℝ) ^ (p + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have hm : m + 2 - 2 = m := by omega
  have hhalf : (1 / 2 : ℝ) ^ (m + 2 + 1)
      = 1 / (2 : ℝ) ^ (m + 2 + 1) := by
    rw [div_pow, one_pow]
  rw [hhalf] at hz
  have hbound := abs_le.mp hz
  have heq : fabiusUniformSpline (m + 2) (1 / 4 + z)
      = (uniformSplineCellPolynomial (m + 2) (2 ^ m)).eval
          (1 / 4 + z) := by
    have hE := fabiusUniformSpline_eqOn_cellPolynomial_dyadic
      (p := m + 2) (r := 2) (by omega) (by omega)
    rw [hm] at hE
    refine hE ?_
    have h4 : (1 : ℝ) / 2 ^ 2 = 1 / 4 := by norm_num
    rw [Set.mem_Icc, h4]
    exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩
  rw [heq, eval_uniformSplineCellPolynomial_quarter,
    pow_succ (1 / 4 : ℝ) (m + 2)]
  ring

/-- **The exact local identity, in the form the quantile chain wants.**
For `2 ≤ p` and every `x` of the level-`(p+1)` cell about `1/4`,

`fabiusUniformSpline p x = quarterLocalPoly (p + 1) (x - 1/4)`.

This is precisely the hypothesis `hlocal` carried unproved through
`UniformSplineStrictMono`. -/
theorem fabiusUniformSpline_eq_quarterLocalPoly {p : ℕ} (hp : 2 ≤ p)
    {x : ℝ} (hx : |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1)) :
    fabiusUniformSpline p x
      = quarterLocalPoly (p + 1) (x - 1 / 4) := by
  have h := fabiusUniformSpline_quarter_cell hp hx
  rw [show (1 : ℝ) / 4 + (x - 1 / 4) = x by ring] at h
  rw [h, quarterLocalPoly]
  ring

/-! ### The two hypotheses of the display are real -/

/-- At level `0` the spline still vanishes at the quarter point, by
`fabiusUniformSpline_eq_zero_of_lt_half`: `2^0 · (1/4) < 1/2`. -/
theorem fabiusUniformSpline_zero_quarter :
    fabiusUniformSpline 0 (1 / 4) = 0 :=
  fabiusUniformSpline_eq_zero_of_lt_half 0 (by norm_num)

/-- At level `1` the quarter point sits exactly on the boundary of the
empty-prefix half-cell, where `fabiusUniformSpline_eq_zero_of_le_half`
still gives the value zero. -/
theorem fabiusUniformSpline_one_quarter :
    fabiusUniformSpline 1 (1 / 4) = 0 :=
  fabiusUniformSpline_eq_zero_of_le_half 1 (by norm_num) (by norm_num)

/-- **The local identity fails below `p = 2`.**  For `p < 2` no such
identity holds, and it already fails at the centre of the cell, where
both `fabiusUniformSpline 0 (1/4)` and `fabiusUniformSpline 1 (1/4)`
are zero and the local polynomial is not.

So the hypothesis `2 ≤ p` of `fabiusUniformSpline_quarter_cell` is not
an artefact of the proof. -/
theorem not_forall_quarterLocalPoly_of_lt_two (p : ℕ) (hp : p < 2) :
    ¬ ∀ x : ℝ, |x - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) →
      fabiusUniformSpline p x
        = quarterLocalPoly (p + 1) (x - 1 / 4) := by
  intro h
  have hx : |(1 / 4 : ℝ) - 1 / 4| ≤ (1 / 2 : ℝ) ^ (p + 1) := by
    rw [sub_self, abs_zero]
    positivity
  have h1 := h (1 / 4) hx
  rw [show (1 : ℝ) / 4 - 1 / 4 = 0 by ring] at h1
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
  · rw [fabiusUniformSpline_zero_quarter, quarterLocalPoly] at h1
    norm_num at h1
  · rw [fabiusUniformSpline_one_quarter, quarterLocalPoly] at h1
    norm_num at h1

/-- The value at the smallest admissible level:
`fabiusUniformSpline 2 (1/4) = 1/16`. -/
theorem fabiusUniformSpline_two_quarter :
    fabiusUniformSpline 2 (1 / 4) = 1 / 16 := by
  have hz : |(0 : ℝ)| ≤ (1 / 2 : ℝ) ^ (2 + 1) := by
    rw [abs_zero]
    positivity
  have h := fabiusUniformSpline_quarter_cell (p := 2) le_rfl hz
  rw [show (1 : ℝ) / 4 + 0 = 1 / 4 by norm_num] at h
  rw [h]
  norm_num

/-- **The exponent in the display is `p + 1`, not `p`.**  At `p = 2` the
correct right-hand side at the cell centre is `5/72 - (4/9)4^-3 = 1/16`
(`fabiusUniformSpline_two_quarter`); the `4^-p` reading would give
`5/72 - (4/9)4^-2 = 1/24`, and the two differ. -/
theorem fabiusUniformSpline_two_quarter_ne_shifted_exponent :
    fabiusUniformSpline 2 (1 / 4)
      ≠ 5 / 72 - 4 / 9 * (1 / 4 : ℝ) ^ 2 := by
  rw [fabiusUniformSpline_two_quarter]
  norm_num

/-! ### The quantile statements, unconditionally -/

/-- **The quarter-quantile uniqueness statement, with no hypothesis
left.**  For `2 ≤ p` the centered spline takes the anchor value
`5 / 72 = F(1/4)` at exactly one point of `[0,1]`.  This is
`existsUnique_fabiusUniformSpline_quarterAnchor` with its local-identity
hypothesis discharged by `fabiusUniformSpline_eq_quarterLocalPoly`. -/
theorem existsUnique_fabiusUniformSpline_eq_quarterAnchor {p : ℕ}
    (hp : 2 ≤ p) :
    ∃! x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
      fabiusUniformSpline p x = 5 / 72 :=
  existsUnique_fabiusUniformSpline_quarterAnchor p hp
    (fun _ hy => fabiusUniformSpline_eq_quarterLocalPoly hp hy)

/-- **The exact quarter quantile.**  For `2 ≤ p`, the unique point of
`[0,1]` at which the level-`p` centered spline attains `5 / 72` is

`quarterQuantile (p+1) = 1/4 + (√(1 + (64/9)·4^-(p+1)) - 1)/8`

(`quarterQuantile_eq`). -/
theorem eq_quarterQuantile_of_fabiusUniformSpline_eq {p : ℕ}
    (hp : 2 ≤ p) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hval : fabiusUniformSpline p x = 5 / 72) :
    x = quarterQuantile (p + 1) :=
  eq_quarterQuantile_of_fabiusUniformSpline p hp
    (fun _ hy => fabiusUniformSpline_eq_quarterLocalPoly hp hy) hx hval

/-- The closed-form root is a root: `fabiusUniformSpline p` attains
`5 / 72` at `quarterQuantile (p + 1)`. -/
theorem fabiusUniformSpline_quarterQuantile {p : ℕ} (hp : 2 ≤ p) :
    fabiusUniformSpline p (quarterQuantile (p + 1)) = 5 / 72 :=
  fabiusUniformSpline_quarterQuantile_eq p
    (fun _ hy => fabiusUniformSpline_eq_quarterLocalPoly hp hy)

/-- The anchor value read as a value of the limit Fabius function: for
`2 ≤ p` the level-`p` spline meets `F(1/4)` at `quarterQuantile (p+1)`,
for every bounded Fabius function `F`. -/
theorem fabiusUniformSpline_quarterQuantile_eq_fabiusReal_of_two_le
    (F : BoundedFabius) (hF : IsFabius F) {p : ℕ} (hp : 2 ≤ p) :
    fabiusUniformSpline p (quarterQuantile (p + 1)) =
      fabiusReal F (1 / 4) :=
  fabiusUniformSpline_quarterQuantile_eq_fabiusReal F hF p
    (fun _ hy => fabiusUniformSpline_eq_quarterLocalPoly hp hy)

/-- **Strict monotonicity on the quarter cell**, unconditionally.  The
global strict form is false (`not_strictMonoOn_fabiusUniformSpline`),
but on the level-`(p+1)` cell about `1/4` the centered spline is
strictly increasing for every `2 ≤ p`. -/
theorem strictMonoOn_fabiusUniformSpline_quarterCell_of_two_le {p : ℕ}
    (hp : 2 ≤ p) :
    StrictMonoOn (fabiusUniformSpline p)
      (Set.Icc (1 / 4 - (1 / 2 : ℝ) ^ (p + 1))
        (1 / 4 + (1 / 2 : ℝ) ^ (p + 1))) :=
  strictMonoOn_fabiusUniformSpline_quarterCell p hp
    (fun _ hy => fabiusUniformSpline_eq_quarterLocalPoly hp hy)

end Fabius
