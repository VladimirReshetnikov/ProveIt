import FabiusFunction.ThueMorsePrefix
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Topology.Instances.Rat

/-!
# Thue--Morse generating series and shifted prefix grids

The signed Thue--Morse sequence is `t(n) = (-1)^w(n)`, with `w(n)` the binary
digit sum, and `S^k` is its `k`-fold *inclusive* prefix sum, defined in
`FabiusFunction.ThueMorsePrefix`.  This module is the generating-function
layer for those sequences, that is, equation (6) of the local draft *K-fold
summation over the signed Thue--Morse sequence*:

`sum_n t(n) X^n = prod_{j>=0} (1 - X^(2^j))`, and
`sum_n S^k_n X^n = (sum_n t(n) X^n) / (1 - X)^k`.

Both are proved as identities of formal power series over `ℤ`, so no complex
variable and no convergence hypothesis is involved.  The infinite product is
rendered coefficientwise, as a finite stabilization: the first `r` factors
already fix every coefficient of degree below `2^r`.  Division by `(1 - X)^k`
uses Mathlib's unit `PowerSeries.invOneSubPow`, and the denominator-cleared
identity `(1 - X)^k * sum_n S^k_n X^n = sum_n t(n) X^n` avoids inverses
altogether.

These identities exist as a separate layer because
`FabiusFunction.ThueMorseApproximation` needs them to identify `S^k_m`, for
`m < 2^k`, with a coefficient of the polynomial approximant of the Fabius
function, and `FabiusFunction.ThueMorseExponential` builds the exponential
generating series for centered and rationally translated Thue--Morse power
sums from the sharp affine coefficient formula on the same import.

The second half of the module studies the shifted grid
`S^(k+s)_j / 2^(C(k,2))` at abscissa `j / 2^k`.  Its discrete functional
equation is independent of the prefix-order shift `s`.  At `s=0` the grid is
exactly the draft's equation (1) and the recurrence becomes equation (2);
`s=1` gives the correction suggested by inclusive prefix sums.  The literal
specialization is then shown not to converge to the required right-endpoint
value: its value there is `-1 / 2^(C(k,2))`, hence stays negative rather than
tending to `F(1) = 1`.

## Main results

* `thueMorseBlockPolynomial_eq_product` and `coeff_finite_thueMorse_product`
  -- the dyadic block polynomial is `prod_{j<r} (1 - X^(2^j))`, and its
  coefficients below `2^r` are already the Thue--Morse signs.
* `iteratedPrefixSeries_eq`, `one_sub_X_pow_mul_iteratedPrefixSeries`, and
  `coeff_eq6_finite` -- the convolution half of equation (6) for every order
  `k`, including `k = 0`, in quotient, cleared, and coefficient form.
* `shiftedPrefixGridValue`, `shiftedPrefixGridValue_equation`, and
  `shiftedPrefixGridValue_equation_of_pos` -- the prefix-grid recurrence for
  every prefix-order shift, with the admissible index range made explicit;
  the paper and corrected grids are the shift-zero and shift-one cases.
* `paperPrefixGridValue_endpoint`, `one_lt_paperPrefixGridValue_endpoint_error`,
  `paperPrefixGridValue_endpoint_not_tendsto_one`, and
  `paperPrefixPolygonReal_endpoint_not_tendsto_one` -- the endpoint
  obstruction, for the grid and for the intended polygonal interpolation.
* The remaining declarations include the `correctedPrefixGridValue` counterparts
  of the grid statements, the rational companion `paperPrefixPolygon` of the
  real polygon, and `simp` coefficient lemmas for the two series.

## Conventions and caveats

`C(k,2)` is `k.choose 2`.  Prefix sums are inclusive, so `S^k_j` already
contains the term at index `j`; the recurrences are stated at level `q + 1`,
and the `_of_pos` variants restate them in the draft's own positive-level
indexing.  The shift changes only the prefix order: denominator and abscissa
remain at level `k`.  Endpoint and convergence statements are therefore not
shift-generic.  In particular, `correctedPrefixGridValue` is the one-index
shift `S^(k+1)` under the level-`k` normalization, recorded here only to show
it obeys the same recurrence -- the approximation that this shift actually
makes converge is proved in `FabiusFunction.ThueMorseApproximation`, over `ℝ`,
from a separate definition.  Both polygons take `⌊x * 2^k⌋₊` in `ℕ` and so
are meant for `x >= 0`; they are the interpolation the draft describes in
words, not the step function its printed floor formula defines.  The
nonconvergence results come in a rational and a real form, the first in the
order topology on `ℚ`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The signed Thue--Morse polynomial on the first dyadic block. -/
noncomputable def thueMorseBlockPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ n ∈ Finset.range (2 ^ r), Polynomial.monomial n (thueMorseSign n)

theorem thueMorseBlockPolynomial_succ (r : ℕ) :
    thueMorseBlockPolynomial (r + 1) =
      thueMorseBlockPolynomial r * (1 - Polynomial.X ^ (2 ^ r)) := by
  rw [thueMorseBlockPolynomial, show 2 ^ (r + 1) = 2 ^ r + 2 ^ r by
    rw [pow_succ]
    omega]
  rw [Finset.sum_range_add]
  rw [thueMorseBlockPolynomial]
  rw [mul_sub, mul_one, Finset.sum_mul]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < 2 ^ r := Finset.mem_range.mp hn
  rw [thueMorseSign_add_pow_two r n hnlt]
  rw [Polynomial.X_pow_eq_monomial, Polynomial.monomial_mul_monomial]
  simp [add_comm]

/-- Finite version of the first product in equation (6). -/
theorem thueMorseBlockPolynomial_eq_product (r : ℕ) :
    thueMorseBlockPolynomial r =
      ∏ j ∈ Finset.range r, (1 - Polynomial.X ^ (2 ^ j) : Polynomial ℤ) := by
  induction r with
  | zero =>
      norm_num [thueMorseBlockPolynomial, thueMorseSign, binaryWeight]
  | succ r ih =>
      rw [show r + 1 = r.succ by omega, thueMorseBlockPolynomial_succ, ih,
        Finset.prod_range_succ]

/-- The formal power series whose coefficients are the signed Thue--Morse sequence. -/
def thueMorseSeries : PowerSeries ℤ :=
  PowerSeries.mk thueMorseSign

@[simp] theorem coeff_thueMorseSeries (n : ℕ) :
    PowerSeries.coeff n thueMorseSeries = thueMorseSign n := by
  simp [thueMorseSeries]

theorem coeff_thueMorseBlockPolynomial (r n : ℕ) (hn : n < 2 ^ r) :
    (thueMorseBlockPolynomial r).coeff n = thueMorseSign n := by
  simp [thueMorseBlockPolynomial, Polynomial.coeff_monomial, hn]

/-- Precise coefficientwise meaning of the infinite product in equation (6):
once the finite product contains all `r` factors of degree below `2^r`, every
coefficient below `2^r` is already the corresponding Thue--Morse sign.  For
`r > 0`, its last factor has degree `2^(r-1)`; for `r = 0`, it is empty. -/
theorem coeff_finite_thueMorse_product (r n : ℕ) (hn : n < 2 ^ r) :
    PowerSeries.coeff n
        ((↑(∏ j ∈ Finset.range r,
          (1 - Polynomial.X ^ (2 ^ j) : Polynomial ℤ)) : PowerSeries ℤ)) =
      PowerSeries.coeff n thueMorseSeries := by
  rw [← thueMorseBlockPolynomial_eq_product]
  simp [Polynomial.coeff_coe, coeff_thueMorseBlockPolynomial r n hn]

/-- Formal generating series of the `k`-fold inclusive prefix sums. -/
def iteratedPrefixSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (iteratedPrefix k)

@[simp] theorem coeff_iteratedPrefixSeries (k n : ℕ) :
    PowerSeries.coeff n (iteratedPrefixSeries k) = iteratedPrefix k n := by
  simp [iteratedPrefixSeries]

/-- The convolution half of equation (6), stated as an identity of formal
power series. No analytic hypothesis on a complex variable is needed. -/
theorem iteratedPrefixSeries_succ_eq (k : ℕ) :
    iteratedPrefixSeries (k + 1) =
      thueMorseSeries * (PowerSeries.invOneSubPow ℤ (k + 1)).val := by
  ext n
  rw [coeff_iteratedPrefixSeries, iteratedPrefix_convolution]
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_thueMorseSeries]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by
    have : m < n + 1 := Finset.mem_range.mp hm
    omega
  rw [show k + (n - m) = n - m + k by omega]
  ring

/-- Equation (6)'s second series identity for every iteration order,
including order zero. -/
theorem iteratedPrefixSeries_eq (k : ℕ) :
    iteratedPrefixSeries k =
      thueMorseSeries * (PowerSeries.invOneSubPow ℤ k).val := by
  cases k with
  | zero =>
      ext n
      simp [iteratedPrefixSeries, thueMorseSeries,
        PowerSeries.invOneSubPow_zero]
  | succ k => simpa [Nat.succ_eq_add_one] using iteratedPrefixSeries_succ_eq k

/-- Denominator-cleared formal-series form of equation (6). -/
theorem one_sub_X_pow_mul_iteratedPrefixSeries (k : ℕ) :
    (1 - PowerSeries.X) ^ k * iteratedPrefixSeries k = thueMorseSeries := by
  rw [iteratedPrefixSeries_eq]
  calc
    (1 - PowerSeries.X) ^ k *
        (thueMorseSeries * (PowerSeries.invOneSubPow ℤ k).val) =
      thueMorseSeries *
        ((1 - PowerSeries.X) ^ k * (PowerSeries.invOneSubPow ℤ k).val) := by
          ring
    _ = thueMorseSeries := by
      have hunit :
          (1 - PowerSeries.X) ^ k * (PowerSeries.invOneSubPow ℤ k).val = 1 := by
        simpa [PowerSeries.invOneSubPow_zero] using
          (PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
            (S := ℤ) (d := 0) k)
      rw [hunit, mul_one]

/-- A finite, directly checkable coefficient form of both identities in (6). -/
theorem coeff_eq6_finite (k r n : ℕ) (hn : n < 2 ^ r) :
    PowerSeries.coeff n
        ((1 - PowerSeries.X) ^ k * iteratedPrefixSeries k) =
      PowerSeries.coeff n
        ((↑(∏ j ∈ Finset.range r,
          (1 - Polynomial.X ^ (2 ^ j) : Polynomial ℤ)) : PowerSeries ℤ)) := by
  rw [one_sub_X_pow_mul_iteratedPrefixSeries]
  exact (coeff_finite_thueMorse_product r n hn).symm

/-- The level-`k` prefix grid with its prefix order shifted by `s` while its
normalization remains `2^(k.choose 2)`. -/
def shiftedPrefixGridValue (s k j : ℕ) : ℚ :=
  (iteratedPrefix (k + s) j : ℚ) / (2 : ℚ) ^ k.choose 2

/-- Equation (1), interpreted literally at its dyadic grid points. -/
def paperPrefixGridValue (k j : ℕ) : ℚ :=
  (iteratedPrefix k j : ℚ) / (2 : ℚ) ^ k.choose 2

/-- The one-index-shift correction suggested by the inclusive-prefix
convention: use `S^(k+1)` with the normalization printed for level `k`. -/
def correctedPrefixGridValue (k j : ℕ) : ℚ :=
  (iteratedPrefix (k + 1) j : ℚ) / (2 : ℚ) ^ k.choose 2

/-- The generic shifted grid at shift zero is definitionally the literal grid. -/
@[simp] theorem shiftedPrefixGridValue_zero (k j : ℕ) :
    shiftedPrefixGridValue 0 k j = paperPrefixGridValue k j := by
  rfl

/-- The generic shifted grid at shift one is definitionally the corrected grid. -/
@[simp] theorem shiftedPrefixGridValue_one (k j : ℕ) :
    shiftedPrefixGridValue 1 k j = correctedPrefixGridValue k j := by
  rfl

/-- Dyadic abscissa belonging to a grid index. -/
def prefixGridPoint (k j : ℕ) : ℚ :=
  (j : ℚ) / (2 : ℚ) ^ k

/-- Unscaled forward difference for every prefix-order shift. -/
theorem shiftedPrefixGridValue_succ_sub (s q j : ℕ) :
    shiftedPrefixGridValue s (q + 1) (j + 1) -
        shiftedPrefixGridValue s (q + 1) j =
      shiftedPrefixGridValue s q (j + 1) / (2 : ℚ) ^ q := by
  rw [shiftedPrefixGridValue, shiftedPrefixGridValue,
    shiftedPrefixGridValue]
  have horder : q + 1 + s = q + s + 1 := by omega
  simp only [horder]
  rw [← sub_div, ← Int.cast_sub, iteratedPrefix_succ_sub]
  rw [choose_succ_two, pow_add, div_div]

/-- Unscaled forward difference for the literal normalization. -/
theorem paperPrefixGridValue_succ_sub (q j : ℕ) :
    paperPrefixGridValue (q + 1) (j + 1) - paperPrefixGridValue (q + 1) j =
      paperPrefixGridValue q (j + 1) / (2 : ℚ) ^ q := by
  simpa only [shiftedPrefixGridValue_zero] using
    shiftedPrefixGridValue_succ_sub 0 q j

/-- The corrected grid obeys the same normalization recurrence, with each
prefix order shifted up by one. -/
theorem correctedPrefixGridValue_succ_sub (q j : ℕ) :
    correctedPrefixGridValue (q + 1) (j + 1) -
        correctedPrefixGridValue (q + 1) j =
      correctedPrefixGridValue q (j + 1) / (2 : ℚ) ^ q := by
  simpa only [shiftedPrefixGridValue_one] using
    shiftedPrefixGridValue_succ_sub 1 q j

/-- The denominator-cleared forward-difference identity for every prefix-order
shift, before restricting the lower-level argument to `[0,1]`. -/
theorem shiftedPrefixGridValue_scaledDifference (s q j : ℕ) :
    (2 : ℚ) ^ (q + 1) *
        (shiftedPrefixGridValue s (q + 1) (j + 1) -
          shiftedPrefixGridValue s (q + 1) j) =
      2 * shiftedPrefixGridValue s q (j + 1) := by
  rw [shiftedPrefixGridValue_succ_sub, pow_succ]
  have hpow : (2 : ℚ) ^ q ≠ 0 := by positivity
  field_simp

/-- The exact forward-difference identity, before restricting the argument of
the lower-level grid value to `[0,1]`. -/
theorem paperPrefixGridValue_scaledDifference (q j : ℕ) :
    (2 : ℚ) ^ (q + 1) *
        (paperPrefixGridValue (q + 1) (j + 1) -
          paperPrefixGridValue (q + 1) j) =
      2 * paperPrefixGridValue q (j + 1) := by
  simpa only [shiftedPrefixGridValue_zero] using
    shiftedPrefixGridValue_scaledDifference 0 q j

/-- Corrected-grid version of the exact scaled forward difference. -/
theorem correctedPrefixGridValue_scaledDifference (q j : ℕ) :
    (2 : ℚ) ^ (q + 1) *
        (correctedPrefixGridValue (q + 1) (j + 1) -
          correctedPrefixGridValue (q + 1) j) =
      2 * correctedPrefixGridValue q (j + 1) := by
  simpa only [shiftedPrefixGridValue_one] using
    shiftedPrefixGridValue_scaledDifference 1 q j

/-- Arithmetic identification of the lower-level argument appearing in the
paper's equation (2). -/
theorem prefixGridPoint_lower_argument (q j : ℕ) :
    prefixGridPoint q (j + 1) =
      2 * prefixGridPoint (q + 1) j + 1 / (2 : ℚ) ^ q := by
  rw [prefixGridPoint, prefixGridPoint, pow_succ]
  have hpow : (2 : ℚ) ^ q ≠ 0 := by positivity
  field_simp
  norm_num

/-- The omitted domain condition in equation (2): `j < 2^q` is exactly what
keeps the argument of the level-`q` grid in the unit interval. -/
theorem prefixGridPoint_lower_argument_mem (q j : ℕ) (hj : j < 2 ^ q) :
    prefixGridPoint q (j + 1) ∈ Set.Icc (0 : ℚ) 1 := by
  constructor
  · unfold prefixGridPoint
    positivity
  · unfold prefixGridPoint
    rw [div_le_one (by positivity : (0 : ℚ) < (2 : ℚ) ^ q)]
    norm_cast

/-- The shifted prefix-grid equation with the exact condition placing its
lower-level argument in the unit interval. -/
theorem shiftedPrefixGridValue_equation (s q j : ℕ) (hj : j < 2 ^ q) :
    (2 : ℚ) ^ (q + 1) *
        (shiftedPrefixGridValue s (q + 1) (j + 1) -
          shiftedPrefixGridValue s (q + 1) j) =
      2 * shiftedPrefixGridValue s q (j + 1) ∧
    prefixGridPoint q (j + 1) ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨shiftedPrefixGridValue_scaledDifference s q j,
    prefixGridPoint_lower_argument_mem q j hj⟩

/-- Equation (2) for the literal grid, with the indexing and unit-interval
domain made explicit. Its level is `k=q+1`, and its admissible indices are
exactly `j < 2^q`. -/
theorem paperPrefixGridValue_equation (q j : ℕ) (hj : j < 2 ^ q) :
    (2 : ℚ) ^ (q + 1) *
        (paperPrefixGridValue (q + 1) (j + 1) -
          paperPrefixGridValue (q + 1) j) =
      2 * paperPrefixGridValue q (j + 1) ∧
    prefixGridPoint q (j + 1) ∈ Set.Icc (0 : ℚ) 1 := by
  simpa only [shiftedPrefixGridValue_zero] using
    shiftedPrefixGridValue_equation 0 q j hj

/-- The corresponding exact equation for the corrected grid. -/
theorem correctedPrefixGridValue_equation (q j : ℕ) (hj : j < 2 ^ q) :
    (2 : ℚ) ^ (q + 1) *
        (correctedPrefixGridValue (q + 1) (j + 1) -
          correctedPrefixGridValue (q + 1) j) =
      2 * correctedPrefixGridValue q (j + 1) ∧
    prefixGridPoint q (j + 1) ∈ Set.Icc (0 : ℚ) 1 := by
  simpa only [shiftedPrefixGridValue_one] using
    shiftedPrefixGridValue_equation 1 q j hj

/-- The shifted prefix-grid equation in positive-level indexing.  Positivity is
essential: at level zero, an arbitrary shift need not satisfy the equation. -/
theorem shiftedPrefixGridValue_equation_of_pos (s k j : ℕ) (hk : 0 < k)
    (hj : j < 2 ^ (k - 1)) :
    (2 : ℚ) ^ k *
        (shiftedPrefixGridValue s k (j + 1) - shiftedPrefixGridValue s k j) =
      2 * shiftedPrefixGridValue s (k - 1) (j + 1) ∧
    prefixGridPoint (k - 1) (j + 1) ∈ Set.Icc (0 : ℚ) 1 := by
  cases k with
  | zero => omega
  | succ q =>
      simpa [Nat.succ_eq_add_one] using
        shiftedPrefixGridValue_equation s q j hj

/-- Literal equation (2) in the paper's own positive-level indexing. -/
theorem paperPrefixGridValue_equation_of_pos (k j : ℕ) (hk : 0 < k)
    (hj : j < 2 ^ (k - 1)) :
    (2 : ℚ) ^ k *
        (paperPrefixGridValue k (j + 1) - paperPrefixGridValue k j) =
      2 * paperPrefixGridValue (k - 1) (j + 1) ∧
    prefixGridPoint (k - 1) (j + 1) ∈ Set.Icc (0 : ℚ) 1 := by
  simpa only [shiftedPrefixGridValue_zero] using
    shiftedPrefixGridValue_equation_of_pos 0 k j hk hj

/-- Corrected equation in the paper's own positive-level indexing. -/
theorem correctedPrefixGridValue_equation_of_pos (k j : ℕ) (hk : 0 < k)
    (hj : j < 2 ^ (k - 1)) :
    (2 : ℚ) ^ k *
        (correctedPrefixGridValue k (j + 1) - correctedPrefixGridValue k j) =
      2 * correctedPrefixGridValue (k - 1) (j + 1) ∧
    prefixGridPoint (k - 1) (j + 1) ∈ Set.Icc (0 : ℚ) 1 := by
  simpa only [shiftedPrefixGridValue_one] using
    shiftedPrefixGridValue_equation_of_pos 1 k j hk hj

/-- The literal endpoint has the wrong sign and scale: at `x=1` it is the
negative reciprocal of the printed normalization. -/
theorem paperPrefixGridValue_endpoint (k : ℕ) :
    paperPrefixGridValue k (2 ^ k) =
      -(1 / (2 : ℚ) ^ k.choose 2) := by
  rw [paperPrefixGridValue, iteratedPrefix_at_dyadic k k le_rfl]
  ring

/-- Consequently its endpoint error from the Fabius boundary value `F(1)=1`
is not small: it is strictly greater than one at every level. -/
theorem paperPrefixGridValue_endpoint_error (k : ℕ) :
    |paperPrefixGridValue k (2 ^ k) - 1| =
      1 + 1 / (2 : ℚ) ^ k.choose 2 := by
  rw [paperPrefixGridValue_endpoint]
  have hpow : 0 < (2 : ℚ) ^ k.choose 2 := by positivity
  have hrecip : 0 < 1 / (2 : ℚ) ^ k.choose 2 := one_div_pos.mpr hpow
  rw [abs_of_neg (by linarith)]
  ring

theorem one_lt_paperPrefixGridValue_endpoint_error (k : ℕ) :
    1 < |paperPrefixGridValue k (2 ^ k) - 1| := by
  rw [paperPrefixGridValue_endpoint_error]
  have hrecip : 0 < 1 / (2 : ℚ) ^ k.choose 2 := by positivity
  linarith

/-- Literal equation (1) cannot even converge pointwise at the endpoint to a
function with value one there. Hence its claimed uniform convergence to the
Fabius function is impossible. -/
theorem paperPrefixGridValue_endpoint_not_tendsto_one :
    ¬ Filter.Tendsto (fun k : ℕ => paperPrefixGridValue k (2 ^ k))
      Filter.atTop (nhds (1 : ℚ)) := by
  intro h
  have hnonpos : ∀ k : ℕ, paperPrefixGridValue k (2 ^ k) ≤ 0 := by
    intro k
    rw [paperPrefixGridValue_endpoint]
    have hrecip : 0 < 1 / (2 : ℚ) ^ k.choose 2 := by positivity
    linarith
  have hone : (1 : ℚ) ≤ 0 :=
    le_of_tendsto h (Filter.Eventually.of_forall hnonpos)
  norm_num at hone

/-- The piecewise-linear interpolation intended by equation (1), as opposed
to the step function obtained by reading its displayed `floor` literally. -/
def paperPrefixPolygon (k : ℕ) (x : ℚ) : ℚ :=
  let u := x * (2 : ℚ) ^ k
  let j := ⌊u⌋₊
  paperPrefixGridValue k j +
    (u - (j : ℚ)) *
      (paperPrefixGridValue k (j + 1) - paperPrefixGridValue k j)

/-- The polygonal interpolation agrees with every dyadic grid value. -/
theorem paperPrefixPolygon_grid (k j : ℕ) :
    paperPrefixPolygon k ((j : ℚ) / (2 : ℚ) ^ k) =
      paperPrefixGridValue k j := by
  unfold paperPrefixPolygon
  have hpow : (2 : ℚ) ^ k ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hpow]
  simp

/-- In particular, the polygon agrees with the literal grid at `x = 1`. -/
theorem paperPrefixPolygon_one (k : ℕ) :
    paperPrefixPolygon k 1 = paperPrefixGridValue k (2 ^ k) := by
  have h := paperPrefixPolygon_grid k (2 ^ k)
  norm_num at h ⊢
  exact h

/-- Passing from the contradictory floor wording to the intended polygonal
interpolation does not repair the endpoint obstruction. -/
theorem paperPrefixPolygon_endpoint_not_tendsto_one :
    ¬ Filter.Tendsto (fun k : ℕ => paperPrefixPolygon k 1)
      Filter.atTop (nhds (1 : ℚ)) := by
  rw [show (fun k : ℕ => paperPrefixPolygon k 1) =
      fun k : ℕ => paperPrefixGridValue k (2 ^ k) by
    funext k
    exact paperPrefixPolygon_one k]
  exact paperPrefixGridValue_endpoint_not_tendsto_one

/-- The source's intended real polygon obtained by joining consecutive
literal dyadic grid values. -/
noncomputable def paperPrefixPolygonReal (k : ℕ) (x : ℝ) : ℝ :=
  let u := x * (2 : ℝ) ^ k
  let j := ⌊u⌋₊
  (paperPrefixGridValue k j : ℝ) +
    (u - (j : ℝ)) *
      ((paperPrefixGridValue k (j + 1) : ℝ) - paperPrefixGridValue k j)

/-- The real polygon agrees with every dyadic grid value. -/
theorem paperPrefixPolygonReal_grid (k j : ℕ) :
    paperPrefixPolygonReal k ((j : ℝ) / (2 : ℝ) ^ k) =
      (paperPrefixGridValue k j : ℝ) := by
  unfold paperPrefixPolygonReal
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hpow]
  simp

/-- In particular, the real polygon agrees with the literal grid at `x = 1`. -/
theorem paperPrefixPolygonReal_one (k : ℕ) :
    paperPrefixPolygonReal k 1 = (paperPrefixGridValue k (2 ^ k) : ℝ) := by
  have h := paperPrefixPolygonReal_grid k (2 ^ k)
  norm_num at h ⊢
  exact h

/-- The intended real polygon has the same endpoint obstruction as the
rational grid and therefore cannot converge pointwise to a function with
value one at the right endpoint. -/
theorem paperPrefixPolygonReal_endpoint_not_tendsto_one :
    ¬ Filter.Tendsto (fun k : ℕ => paperPrefixPolygonReal k 1)
      Filter.atTop (nhds (1 : ℝ)) := by
  rw [show (fun k : ℕ => paperPrefixPolygonReal k 1) =
      fun k : ℕ => (paperPrefixGridValue k (2 ^ k) : ℝ) by
    funext k
    exact paperPrefixPolygonReal_one k]
  intro h
  have hnonpos : ∀ k : ℕ, (paperPrefixGridValue k (2 ^ k) : ℝ) ≤ 0 := by
    intro k
    rw [paperPrefixGridValue_endpoint]
    norm_num
  have hone : (1 : ℝ) ≤ 0 :=
    le_of_tendsto h (Filter.Eventually.of_forall hnonpos)
  norm_num at hone

end Fabius
