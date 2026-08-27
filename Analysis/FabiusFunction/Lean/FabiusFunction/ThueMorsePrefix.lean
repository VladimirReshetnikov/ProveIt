import FabiusFunction.DyadicClosedForm
import FabiusFunction.FinitePolynomialFunctional
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Iterated prefix sums of the signed Thue--Morse sequence

Write `t_n = (-1)^(binaryWeight n)` for the signed Thue--Morse sequence of
`FabiusFunction.DyadicClosedForm`.  This module develops the discrete side of
the local K-fold Thue--Morse draft: the `k`-fold *inclusive* prefix sums
`S^0(n) = t_n`, `S^(k+1)(n) = sum_{j <= n} S^k(j)`, their closed form as the
binomial convolution

`S^(k+1)(n) = sum_{m <= n} C(n - m + k, k) * t_m`

-- the draft's equation (5), with discrete B-spline kernel
`B_k(n) = C(n + k - 1, k - 1)` -- and the exact run of zeros that `S^k` has
at the right end of every dyadic block.  Those zero runs come from Prouhet
cancellation, so the module also gives the block power sums
`sum_{h < 2^r} t_h * h^d` a public name, `thueMorsePowerSum`
(`DyadicClosedForm` proves the monomial statements only for a private copy),
and upgrades them from monomials to arbitrary polynomials and to affine
substitutions.

The block power sums have integer values, so the whole power-sum layer lives
over an arbitrary commutative ring: `thueMorsePowerSumRing R` is the same sum
computed in `R`, every identity is proved once over `ℤ` and transported along
the unique ring map `ℤ → R`, and the rational and real statements are the
instances `R = ℚ` and `R = ℝ`.

It is a separate module because it is the base of the draft's whole discrete
chain.  `FabiusFunction.ThueMorseGenerating` turns `iteratedPrefix` into a
power series satisfying `(1 - X)^k * S_k = thueMorseSeries` (equation (6))
and defines the normalized grid `S^k(j) / 2^C(k,2)`;
`FabiusFunction.ThueMorseApproximation` identifies the prefixes with the
coefficients of the Fabius approximation polynomials;
`FabiusFunction.DraftCounterexamples` refutes the draft's literal error
claims; and `FabiusFunction.ThueMorseExponential` uses the affine power sum
to evaluate centered and translated exponential generating series.

## Main results

* `iteratedPrefix`, `iteratedPrefix_succ_sub` -- the `k`-fold inclusive
  prefix sums and their forward difference.
* `iteratedPrefix_convolution`, `iteratedPrefixKernel`,
  `iteratedPrefix_eq_sum_kernel` -- equation (5), in a predecessor-free
  indexing and in the source's kernel form.
* `thueMorsePowerSum_eq_zero_of_lt`, `thueMorsePowerSum_self` -- Prouhet
  cancellation for `d < r`, and the sharp boundary value
  `(-1)^r * 2^C(r,2) * r!` at `d = r`.
* `thueMorsePowerSumRing`, `thueMorsePowerSumRing_intCast` -- the same block
  power sum with values in an arbitrary commutative ring `R`, and its
  identification with the image of the integer instance `R = ℤ` under the
  unique ring map `ℤ → R`.
* `thueMorsePowerSumRing_succ`, `thueMorsePowerSumRing_eq_zero_of_lt`,
  `thueMorsePowerSumRing_self` -- the half-block recurrence, Prouhet
  cancellation and the sharp boundary value over `R`.
* `thueMorse_polynomial_sum_eq_coeff_ring_of_degree_le`,
  `thueMorse_polynomial_sum_eq_zero_ring_of_degree_lt` -- the degree-valued
  coefficient extractor and strict cancellation theorem, including the zero
  polynomial at the boundary `r = 0`.
* `thueMorse_polynomial_sum_eq_coeff_ring`,
  `thueMorse_polynomial_sum_eq_zero_ring`,
  `thueMorse_affine_power_sum_eq_zero_ring`,
  `thueMorse_affine_power_sum_self_ring`,
  `thueMorse_affine_power_sum_of_le_ring` -- coefficient extraction against a
  polynomial of degree at most `r`, and the affine Prouhet formulas, over an
  arbitrary commutative ring.
* `thueMorse_polynomial_sum_eq_coeff`, `thueMorse_polynomial_sum_eq_zero`,
  `thueMorse_affine_power_sum_self`, and `thueMorse_affine_power_sum_of_le` --
  the rational instances: a block sum against a rational polynomial of degree
  at most `r` returns its degree-`r` coefficient times that factor; affine
  powers have a single formula covering both the vanishing range and the
  sharp degree.
* `thueMorse_affine_power_sum_eq_zero_real` and
  `thueMorse_affine_power_sum_self_real` -- the real instances of the same
  affine cancellation and sharp-degree formula, for direct use by the
  analytic spline development.
* `iteratedPrefix_dyadic_reverse_window`,
  `iteratedPrefix_dyadic_reverse_window_eq_zero_iff`, and the endpoint
  theorems -- on the `2^r-k` entries preceding the final `k` zeros of a
  dyadic block, the order-`k` prefix row is reciprocal up to the sign
  `(-1)^(r-k)`; the zero locus is reflected with it, the boundary value is
  `(-1)^(r-k)`, and `S^k(2^r) = -1`.

The remaining public declarations are the definitional unfolding
`iteratedPrefix_succ`, the half-block recurrence `thueMorsePowerSum_succ`,
the bridge `thueMorsePowerSum_eq_ring` between the rational power sum and the
ring-valued one, the `simp` normal forms (`iteratedPrefix_zero`,
`iteratedPrefix_at_zero`, `iteratedPrefix_one_two_mul_add_one`,
`thueMorseSign_two_pow_sub_one`), and the endpoint and reverse-indexed forms
of the zero run (`iteratedPrefix_dyadic_endpoint`,
`iteratedPrefix_dyadic_zero_reverse`).

Conventions and caveats.  Prefix sums are inclusive, so `S^(k+1)(n)` ranges
over `j <= n`; `iteratedPrefix` is `ℤ`-valued, and the named monomial and
polynomial power-sum API comes in a ring-valued form `thueMorsePowerSumRing`
together with its rational specialization `thueMorsePowerSum`.  The `_real`
affine theorems are now one-line instances of the ring-valued ones, not
separate proofs.  `iteratedPrefix_eq_sum_kernel` assumes `1 <= k`, matching
the source's positive indexing of `B_k`.  Every zero-run statement assumes
`k <= r`, that is, a block long enough to absorb `k` cancellations, and says
nothing for shorter blocks.  The sharp affine power-sum formulas do not
depend on the translation, but carry a factor `y^r` and so vanish for `y = 0`
when `r > 0`; at `r = 0`, Lean's `0^0 = 1` convention gives the correct
one-term sum.  The draft's grid normalization `2^C(k,2)` is applied
downstream in `FabiusFunction.ThueMorseGenerating`, not here.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The iterated inclusive prefix sums from the Thue--Morse paper. -/
def iteratedPrefix : ℕ → ℕ → ℤ
  | 0, n => thueMorseSign n
  | k + 1, n => ∑ j ∈ Finset.range (n + 1), iteratedPrefix k j

/-- At order zero, the iterated prefix is the signed Thue--Morse sequence. -/
@[simp] theorem iteratedPrefix_zero (n : ℕ) :
    iteratedPrefix 0 n = thueMorseSign n := rfl

/-- One further inclusive prefix iteration sums the preceding row through the
current index. -/
theorem iteratedPrefix_succ (k n : ℕ) :
    iteratedPrefix (k + 1) n =
      ∑ j ∈ Finset.range (n + 1), iteratedPrefix k j := rfl

/-- Every iterated inclusive-prefix row starts with value one. -/
@[simp] theorem iteratedPrefix_at_zero (k : ℕ) :
    iteratedPrefix k 0 = 1 := by
  induction k with
  | zero => norm_num [iteratedPrefix, thueMorseSign, binaryWeight]
  | succ k ih => simp [iteratedPrefix, ih]

/-- Forward grid increment; the prefix summand is evaluated at the new grid point. -/
theorem iteratedPrefix_succ_sub (k n : ℕ) :
    iteratedPrefix (k + 1) (n + 1) - iteratedPrefix (k + 1) n =
      iteratedPrefix k (n + 1) := by
  simp only [iteratedPrefix_succ]
  rw [Finset.sum_range_succ]
  ring

/-- The first prefix sum vanishes at every odd index. -/
@[simp] theorem iteratedPrefix_one_two_mul_add_one (m : ℕ) :
    iteratedPrefix 1 (2 * m + 1) = 0 := by
  rw [iteratedPrefix_succ]
  have h := thueMorse_sum_two_mul (m + 1) (fun _ => (1 : ℚ))
  simp only [mul_one, sub_self, mul_zero, Finset.sum_const_zero] at h
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [iteratedPrefix_zero]
  exact_mod_cast h

/-- The binomial convolution formula, indexed without a predecessor operation on `k`. -/
theorem iteratedPrefix_convolution (k n : ℕ) :
    iteratedPrefix (k + 1) n =
      ∑ m ∈ Finset.range (n + 1),
        (Nat.choose (n - m + k) k : ℤ) * thueMorseSign m := by
  induction k generalizing n with
  | zero => simp [iteratedPrefix_succ]
  | succ k ih =>
      induction n with
      | zero => norm_num [iteratedPrefix_succ, thueMorseSign, binaryWeight]
      | succ n hn =>
          rw [show iteratedPrefix (k + 2) (n + 1) =
              iteratedPrefix (k + 2) n + iteratedPrefix (k + 1) (n + 1) by
                linarith [iteratedPrefix_succ_sub (k + 1) n],
            hn, ih]
          conv_rhs => rw [Finset.sum_range_succ]
          conv_lhs =>
            rhs
            rw [Finset.sum_range_succ]
          simp only [Nat.sub_self, zero_add, Nat.choose_self]
          rw [← add_assoc]
          rw [add_right_cancel_iff]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro m hm
          have hmlt : m < n + 1 := Finset.mem_range.mp hm
          have hmn : m ≤ n := by omega
          rw [← add_mul]
          congr 1
          norm_cast
          rw [show n - m + (k + 1) = n - m + k + 1 by omega,
            show n + 1 - m + k = n - m + k + 1 by omega,
            show n + 1 - m + (k + 1) = (n - m + k + 1) + 1 by omega]
          conv_rhs => rw [Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one]
          omega

/-- The discrete B-spline kernel `B_k` displayed in equation (5) of the
K-fold draft.  Its argument is nonnegative, so the source's indicator is
implicit in the natural-number type. -/
def iteratedPrefixKernel (k n : ℕ) : ℕ :=
  Nat.choose (n + k - 1) (k - 1)

/-- Equation (5) with the source's positive indexing of the number of prefix
summations. -/
theorem iteratedPrefix_eq_sum_kernel (k n : ℕ) (hk : 1 ≤ k) :
    iteratedPrefix k n =
      ∑ m ∈ Finset.range (n + 1),
        (iteratedPrefixKernel k (n - m) : ℤ) * thueMorseSign m := by
  rw [show k = (k - 1) + 1 by omega, iteratedPrefix_convolution]
  apply Finset.sum_congr rfl
  intro m hm
  unfold iteratedPrefixKernel
  congr 1

/-- The signed power sum over a complete dyadic Thue--Morse block. -/
def thueMorsePowerSum (r d : ℕ) : ℚ :=
  ∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) * (h.val : ℚ) ^ d

/-- Splitting a dyadic block in half gives a recurrence in lower power
sums. -/
theorem thueMorsePowerSum_succ (r d : ℕ) :
    thueMorsePowerSum (r + 1) d =
      -(∑ k ∈ Finset.range d,
        (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * thueMorsePowerSum r k) := by
  have h := thuePowerSum_succ r d
  change thueMorsePowerSum (r + 1) d =
    -(∑ k ∈ Finset.range d,
      (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * thueMorsePowerSum r k) at h
  exact h

/-- Prouhet cancellation for monomials below the block exponent. -/
theorem thueMorsePowerSum_eq_zero_of_lt (r d : ℕ) (hd : d < r) :
    thueMorsePowerSum r d = 0 := by
  have h := thuePowerSum_eq_zero_of_lt r d hd
  change thueMorsePowerSum r d = 0 at h
  exact h

/-- The first power not annihilated by a dyadic Thue--Morse block has an
explicit value.  This is the sharp boundary case of Prouhet cancellation. -/
theorem thueMorsePowerSum_self (r : ℕ) :
    thueMorsePowerSum r r =
      (-1 : ℚ) ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial := by
  induction r with
  | zero =>
      norm_num [thueMorsePowerSum, thueMorseSign, binaryWeight]
  | succ r ih =>
      rw [show r + 1 = r.succ by omega,
        show r.succ = r + 1 by omega,
        thueMorsePowerSum_succ, Finset.sum_range_succ]
      have hzero :
          (∑ k ∈ Finset.range r,
            (Nat.choose (r + 1) k : ℚ) * (2 : ℚ) ^ k *
              thueMorsePowerSum r k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [thueMorsePowerSum_eq_zero_of_lt r k (Finset.mem_range.mp hk), mul_zero]
      rw [hzero, zero_add, ih]
      rw [show (r + 1).choose 2 = r.choose 2 + r by
        rw [Nat.choose_succ_succ]
        simp [Nat.choose_one_right, Nat.add_comm],
        pow_add, Nat.factorial_succ, pow_succ]
      rw [Nat.choose_succ_self_right]
      push_cast
      ring

/-! ### The block power sum over an arbitrary commutative ring

The summand `thueMorseSign h * h ^ d` is an integer, so the whole power-sum
layer is the image of one integer identity under the unique ring map
`ℤ → R`.  The definition below records that sum in `R`; the rational
`thueMorsePowerSum` is its instance at `R = ℚ`. -/

/-- The signed power sum over a complete dyadic Thue--Morse block, computed in
an arbitrary commutative ring `R`.  At `R = ℚ` this is `thueMorsePowerSum`,
and `thueMorsePowerSumRing_intCast` identifies the general value as the image
of the integer one. -/
def thueMorsePowerSumRing (R : Type*) [CommRing R] (r d : ℕ) : R :=
  ∑ h : Fin (2 ^ r), (thueMorseSign h.val : R) * (h.val : R) ^ d

/-- The rational block power sum is the instance `R = ℚ` of the ring-valued
one. -/
theorem thueMorsePowerSum_eq_ring (r d : ℕ) :
    thueMorsePowerSum r d = thueMorsePowerSumRing ℚ r d := rfl

section Ring

variable {R : Type*} [CommRing R]

/-- The ring-valued block power sum is the image of the integer block power
sum under the unique ring map `ℤ → R`.  Every identity in this section is
proved once over `ℤ` and transported along this equation. -/
theorem thueMorsePowerSumRing_intCast (r d : ℕ) :
    ((thueMorsePowerSumRing ℤ r d : ℤ) : R) =
      thueMorsePowerSumRing R r d := by
  simp only [thueMorsePowerSumRing]
  push_cast
  rfl

/-- The rational block power sum written as the cast of the integer one; this
is the shape `exact_mod_cast` needs when descending from `ℚ` to `ℤ`. -/
private theorem thueMorsePowerSum_eq_intCast (r d : ℕ) :
    thueMorsePowerSum r d = ((thueMorsePowerSumRing ℤ r d : ℤ) : ℚ) := by
  rw [thueMorsePowerSum_eq_ring, thueMorsePowerSumRing_intCast]

/-- Splitting a dyadic block in half gives a recurrence in lower power sums,
over an arbitrary commutative ring. -/
theorem thueMorsePowerSumRing_succ (r d : ℕ) :
    thueMorsePowerSumRing R (r + 1) d =
      -(∑ k ∈ Finset.range d,
        (Nat.choose d k : R) * (2 : R) ^ k *
          thueMorsePowerSumRing R r k) := by
  have hZ : thueMorsePowerSumRing ℤ (r + 1) d =
      -(∑ k ∈ Finset.range d,
        (Nat.choose d k : ℤ) * (2 : ℤ) ^ k *
          thueMorsePowerSumRing ℤ r k) := by
    have hQ : ((thueMorsePowerSumRing ℤ (r + 1) d : ℤ) : ℚ) =
        ((-(∑ k ∈ Finset.range d,
            (Nat.choose d k : ℤ) * (2 : ℤ) ^ k *
              thueMorsePowerSumRing ℤ r k) : ℤ) : ℚ) := by
      rw [thueMorsePowerSumRing_intCast, ← thueMorsePowerSum_eq_ring,
        thueMorsePowerSum_succ, Int.cast_neg, Int.cast_sum, neg_inj]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [thueMorsePowerSum_eq_intCast]
      push_cast
      rfl
    exact_mod_cast hQ
  rw [← thueMorsePowerSumRing_intCast, hZ, Int.cast_neg, Int.cast_sum,
    neg_inj]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast [thueMorsePowerSumRing_intCast]
  rfl

/-- Prouhet cancellation for monomials below the block exponent, over an
arbitrary commutative ring. -/
theorem thueMorsePowerSumRing_eq_zero_of_lt (r d : ℕ) (hd : d < r) :
    thueMorsePowerSumRing R r d = 0 := by
  have hZ : thueMorsePowerSumRing ℤ r d = 0 := by
    have hQ : ((thueMorsePowerSumRing ℤ r d : ℤ) : ℚ) = 0 := by
      rw [thueMorsePowerSumRing_intCast, ← thueMorsePowerSum_eq_ring]
      exact thueMorsePowerSum_eq_zero_of_lt r d hd
    exact_mod_cast hQ
  rw [← thueMorsePowerSumRing_intCast, hZ, Int.cast_zero]

/-- The sharp boundary case of Prouhet cancellation, over an arbitrary
commutative ring: the first power a dyadic block does not annihilate has the
explicit value `(-1)^r * 2^C(r,2) * r!`. -/
theorem thueMorsePowerSumRing_self (r : ℕ) :
    thueMorsePowerSumRing R r r =
      (-1 : R) ^ r * (2 : R) ^ r.choose 2 * r.factorial := by
  have hZ : thueMorsePowerSumRing ℤ r r =
      (-1 : ℤ) ^ r * (2 : ℤ) ^ r.choose 2 * r.factorial := by
    have hQ : ((thueMorsePowerSumRing ℤ r r : ℤ) : ℚ) =
        (((-1 : ℤ) ^ r * (2 : ℤ) ^ r.choose 2 *
          r.factorial : ℤ) : ℚ) := by
      rw [thueMorsePowerSumRing_intCast, ← thueMorsePowerSum_eq_ring,
        thueMorsePowerSum_self]
      push_cast
      rfl
    exact_mod_cast hQ
  rw [← thueMorsePowerSumRing_intCast, hZ]
  push_cast
  rfl

/-- **Degree-valued polynomial Prouhet extractor.**  On polynomials of degree
at most `r`, summation against a dyadic Thue--Morse block extracts the
degree-`r` coefficient, up to the explicit Prouhet factor.  The coefficients
may lie in any commutative ring.

The hypothesis uses `Polynomial.degree`, so it includes the zero polynomial
uniformly and gives the correct total statement at `r = 0`. -/
theorem thueMorse_polynomial_sum_eq_coeff_ring_of_degree_le
    (r : ℕ) (p : Polynomial R) (hp : p.degree ≤ (r : WithBot ℕ)) :
    (∑ h : Fin (2 ^ r),
        (thueMorseSign h.val : R) * p.eval (h.val : R)) =
      p.coeff r *
        ((-1 : R) ^ r * (2 : R) ^ r.choose 2 * r.factorial) := by
  refine sum_weight_mul_eval_eq_coeff_mul_of_moments
    (Finset.univ : Finset (Fin (2 ^ r)))
    (fun h => (thueMorseSign h.val : R))
    (fun h => (h.val : R))
    r
    ((-1 : R) ^ r * (2 : R) ^ r.choose 2 * r.factorial)
    ?_ ?_ p hp
  · intro d hd
    change thueMorsePowerSumRing R r d = 0
    exact thueMorsePowerSumRing_eq_zero_of_lt (R := R) r d hd
  · change thueMorsePowerSumRing R r r =
      (-1 : R) ^ r * (2 : R) ^ r.choose 2 * r.factorial
    exact thueMorsePowerSumRing_self (R := R) r

/-- Compatibility form of the polynomial Prouhet extractor using
`Polynomial.natDegree`.  The degree-valued theorem above is stronger exactly
at the zero-polynomial boundary. -/
theorem thueMorse_polynomial_sum_eq_coeff_ring (r : ℕ) (p : Polynomial R)
    (hp : p.natDegree ≤ r) :
    (∑ h : Fin (2 ^ r),
        (thueMorseSign h.val : R) * p.eval (h.val : R)) =
      p.coeff r *
        ((-1 : R) ^ r * (2 : R) ^ r.choose 2 * r.factorial) := by
  exact thueMorse_polynomial_sum_eq_coeff_ring_of_degree_le
    (R := R) r p (Polynomial.degree_le_of_natDegree_le hp)

/-- **Degree-valued polynomial Prouhet cancellation.**  A dyadic
Thue--Morse block annihilates every polynomial of degree strictly below its
block exponent.  At `r = 0`, the degree condition admits exactly the zero
polynomial, so no exceptional case is needed. -/
theorem thueMorse_polynomial_sum_eq_zero_ring_of_degree_lt
    (r : ℕ) (p : Polynomial R) (hp : p.degree < (r : WithBot ℕ)) :
    (∑ h : Fin (2 ^ r),
      (thueMorseSign h.val : R) * p.eval (h.val : R)) = 0 := by
  rw [thueMorse_polynomial_sum_eq_coeff_ring_of_degree_le r p hp.le,
    Polynomial.coeff_eq_zero_of_degree_lt hp, zero_mul]

/-- Thue--Morse signs annihilate every polynomial of degree below the dyadic
block exponent, over an arbitrary commutative ring. -/
theorem thueMorse_polynomial_sum_eq_zero_ring (r : ℕ) (p : Polynomial R)
    (hp : p.natDegree < r) :
    (∑ h : Fin (2 ^ r),
      (thueMorseSign h.val : R) * p.eval (h.val : R)) = 0 := by
  rw [thueMorse_polynomial_sum_eq_coeff_ring r p hp.le,
    Polynomial.coeff_eq_zero_of_natDegree_lt hp, zero_mul]

/-- Affine Prouhet cancellation below the block exponent, over an arbitrary
commutative ring.  The translation and scale are arbitrary: after the
binomial expansion, every remaining monomial has degree strictly below
`r`. -/
theorem thueMorse_affine_power_sum_eq_zero_ring
    (r d : ℕ) (hd : d < r) (x y : R) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : R) *
      (x + y * (h.val : R)) ^ d) = 0 := by
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hdegree : d - k < r := (Nat.sub_le d k).trans_lt hd
  have hinner :
      (∑ h : Fin (2 ^ r),
        (thueMorseSign h.val : R) *
          (x ^ k * (y * (h.val : R)) ^ (d - k) * (Nat.choose d k : R))) =
        (x ^ k * y ^ (d - k) * (Nat.choose d k : R)) *
          thueMorsePowerSumRing R r (d - k) := by
    rw [thueMorsePowerSumRing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [mul_pow]
    ring
  rw [hinner, thueMorsePowerSumRing_eq_zero_of_lt r (d - k) hdegree, mul_zero]

/-- At the sharp Prouhet degree, an affine change of variable contributes only
the `r`th power of its scale, over an arbitrary commutative ring.  Thus the
sum is independent of the translation `x`.  For `r > 0` it vanishes at
`y = 0`; for `r = 0`, including `y = 0`, Lean's `0 ^ 0 = 1` convention gives
the correct one-term sum. -/
theorem thueMorse_affine_power_sum_self_ring (r : ℕ) (x y : R) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : R) *
      (x + y * (h.val : R)) ^ r) =
      (-1 : R) ^ r * y ^ r * (2 : R) ^ r.choose 2 * r.factorial := by
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single 0]
  · norm_num only [pow_zero, Nat.choose_zero_right, Nat.cast_one,
      one_mul, mul_one, Nat.zero_le, Nat.sub_zero]
    calc
      (∑ h : Fin (2 ^ r),
          (thueMorseSign h.val : R) * (y * (h.val : R)) ^ r) =
          y ^ r * thueMorsePowerSumRing R r r := by
        rw [thueMorsePowerSumRing, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        rw [mul_pow]
        ring
      _ = y ^ r *
          ((-1 : R) ^ r * (2 : R) ^ r.choose 2 * r.factorial) := by
        rw [thueMorsePowerSumRing_self]
      _ = _ := by ring
  · intro k hk hk0
    have hkle : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hdegree : r - k < r := Nat.sub_lt (by omega) (by omega)
    calc
      (∑ h : Fin (2 ^ r),
          (thueMorseSign h.val : R) *
            (x ^ k * (y * (h.val : R)) ^ (r - k) *
              (Nat.choose r k : R))) =
          (x ^ k * y ^ (r - k) * (Nat.choose r k : R)) *
            thueMorsePowerSumRing R r (r - k) := by
        rw [thueMorsePowerSumRing, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        rw [mul_pow]
        ring
      _ = 0 := by
        rw [thueMorsePowerSumRing_eq_zero_of_lt r (r - k) hdegree, mul_zero]
  · simp

/-- Unified Prouhet formula for affine powers through the sharp degree, over
an arbitrary commutative ring.  Below degree `r` the block sum vanishes; at
degree `r` it is the sharp value from
`thueMorse_affine_power_sum_self_ring`.  The formula includes `r = d = 0`,
where Lean's power convention makes `y ^ 0 = 1` even when `y = 0`. -/
theorem thueMorse_affine_power_sum_of_le_ring
    (r d : ℕ) (hd : d ≤ r) (x y : R) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : R) *
      (x + y * (h.val : R)) ^ d) =
      if d = r then
        (-1 : R) ^ r * y ^ r * (2 : R) ^ r.choose 2 * r.factorial
      else 0 := by
  rcases eq_or_lt_of_le hd with h | h
  · subst d
    rw [thueMorse_affine_power_sum_self_ring, if_pos rfl]
  · rw [thueMorse_affine_power_sum_eq_zero_ring r d h x y, if_neg h.ne]

end Ring

/-- On polynomials of degree at most `r`, summation against a dyadic
Thue--Morse block extracts the degree-`r` coefficient, up to the explicit
nonzero Prouhet factor.  Rational instance of
`thueMorse_polynomial_sum_eq_coeff_ring`. -/
theorem thueMorse_polynomial_sum_eq_coeff (r : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree ≤ r) :
    (∑ h : Fin (2 ^ r),
        (thueMorseSign h.val : ℚ) * p.eval (h.val : ℚ)) =
      p.coeff r *
        ((-1 : ℚ) ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial) :=
  thueMorse_polynomial_sum_eq_coeff_ring r p hp

/-- At the sharp Prouhet degree, an affine change of variable contributes only
the expected power of its linear coefficient.  In particular, the sum is
independent of the translation `x`; for positive `r` it vanishes when that
coefficient is zero.  Rational instance of
`thueMorse_affine_power_sum_self_ring`. -/
theorem thueMorse_affine_power_sum_self (r : ℕ) (x y : ℚ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) *
      (x + y * (h.val : ℚ)) ^ r) =
      (-1 : ℚ) ^ r * y ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial :=
  thueMorse_affine_power_sum_self_ring r x y

/-- Unified Prouhet formula for affine powers through the sharp degree.  Below
degree `r` the block sum vanishes; at degree `r` it is the sharp value from
`thueMorse_affine_power_sum_self`.  The formula includes `r = d = 0`, where
Lean's power convention makes `y ^ 0 = 1` even when `y = 0`.  Rational
instance of `thueMorse_affine_power_sum_of_le_ring`. -/
theorem thueMorse_affine_power_sum_of_le
    (r d : ℕ) (hd : d ≤ r) (x y : ℚ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) *
      (x + y * (h.val : ℚ)) ^ d) =
      if d = r then
        (-1 : ℚ) ^ r * y ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial
      else 0 :=
  thueMorse_affine_power_sum_of_le_ring r d hd x y

/-- Real affine Prouhet cancellation below the block exponent.  The
translation and scale are arbitrary: after the binomial expansion, every
remaining monomial has degree strictly below `r`.  Real instance of
`thueMorse_affine_power_sum_eq_zero_ring`. -/
theorem thueMorse_affine_power_sum_eq_zero_real
    (r d : ℕ) (hd : d < r) (x y : ℝ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℝ) *
      (x + y * (h.val : ℝ)) ^ d) = 0 :=
  thueMorse_affine_power_sum_eq_zero_ring r d hd x y

/-- At the sharp Prouhet degree, a real affine change of variable contributes
only the `r`th power of its scale.  Thus the sum is independent of the
translation `x`.  For `r > 0` it vanishes at `y = 0`; for `r = 0`, including
`y = 0`, Lean's `0 ^ 0 = 1` convention gives the correct one-term sum.  Real
instance of `thueMorse_affine_power_sum_self_ring`. -/
theorem thueMorse_affine_power_sum_self_real (r : ℕ) (x y : ℝ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℝ) *
      (x + y * (h.val : ℝ)) ^ r) =
      (-1 : ℝ) ^ r * y ^ r * (2 : ℝ) ^ r.choose 2 * r.factorial :=
  thueMorse_affine_power_sum_self_ring r x y

/-- Thue--Morse signs annihilate every rational polynomial of degree below the
dyadic block exponent.  Rational instance of
`thueMorse_polynomial_sum_eq_zero_ring`. -/
lemma thueMorse_polynomial_sum_eq_zero (r : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree < r) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) * p.eval (h.val : ℚ)) = 0 :=
  thueMorse_polynomial_sum_eq_zero_ring r p hp

private noncomputable def prefixEndpointPolynomial (N k : ℕ) : Polynomial ℚ :=
  (ascPochhammer ℚ k).comp (Polynomial.C (N : ℚ) - Polynomial.X)

private lemma prefixEndpointPolynomial_natDegree_le (N k : ℕ) :
    (prefixEndpointPolynomial N k).natDegree ≤ k := by
  rw [prefixEndpointPolynomial]
  calc
    ((ascPochhammer ℚ k).comp
        (Polynomial.C (N : ℚ) - Polynomial.X)).natDegree ≤
        (ascPochhammer ℚ k).natDegree *
          (Polynomial.C (N : ℚ) - Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ k * 1 := by
      gcongr
      · rw [ascPochhammer_natDegree]
      · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = k := by omega

private lemma prefixEndpointPolynomial_eval (N k m : ℕ) (hm : m < N) :
    (prefixEndpointPolynomial N k).eval (m : ℚ) =
      (k.factorial : ℚ) * (Nat.choose (N - 1 - m + k) k : ℚ) := by
  rw [prefixEndpointPolynomial, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [show (N : ℚ) - (m : ℚ) = ((N - m : ℕ) : ℚ) by
    rw [Nat.cast_sub (Nat.le_of_lt hm)]]
  rw [ascPochhammer_nat_eq_natCast_descFactorial]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  congr 2
  congr 1
  omega

/-- Every positive iterated prefix sum vanishes at the last index of a
sufficiently large dyadic block. -/
theorem iteratedPrefix_dyadic_endpoint (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    iteratedPrefix k (2 ^ r - 1) = 0 := by
  let q := k - 1
  let N := 2 ^ r
  have hkq : k = q + 1 := by dsimp [q]; omega
  have hqr : q < r := by dsimp [q]; omega
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hdegree : (prefixEndpointPolynomial N q).natDegree < r :=
    (prefixEndpointPolynomial_natDegree_le N q).trans_lt hqr
  have hcancel := thueMorse_polynomial_sum_eq_zero r
    (prefixEndpointPolynomial N q) hdegree
  have hNpow : N = 2 ^ r := rfl
  rw [← hNpow] at hcancel
  change (∑ h : Fin N, (thueMorseSign h.val : ℚ) *
    (prefixEndpointPolynomial N q).eval (h.val : ℚ)) = 0 at hcancel
  rw [Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (thueMorseSign m : ℚ) *
      (prefixEndpointPolynomial N q).eval (m : ℚ)) N] at hcancel
  have hfactor :
      (q.factorial : ℚ) * (iteratedPrefix k (N - 1) : ℚ) =
        ∑ m ∈ Finset.range N,
          (thueMorseSign m : ℚ) * (prefixEndpointPolynomial N q).eval (m : ℚ) := by
    rw [hkq, iteratedPrefix_convolution]
    push_cast
    rw [show N - 1 + 1 = N by omega, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmN : m < N := Finset.mem_range.mp hm
    rw [prefixEndpointPolynomial_eval N q m hmN]
    ring
  have hzero : (q.factorial : ℚ) * (iteratedPrefix k (N - 1) : ℚ) = 0 := by
    rw [hfactor, hcancel]
  have hcast : (iteratedPrefix k (N - 1) : ℚ) = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left (by positivity)
  exact_mod_cast hcast

/-- Reverse-indexed form of the full dyadic zero run. -/
theorem iteratedPrefix_dyadic_zero_reverse (k r d : ℕ)
    (hk : 1 ≤ k) (hkr : k ≤ r) (hd : d < k) :
    iteratedPrefix k (2 ^ r - 1 - d) = 0 := by
  induction d generalizing k r with
  | zero => simpa using iteratedPrefix_dyadic_endpoint k r hk hkr
  | succ d ih =>
      have hkTwo : 2 ≤ k := by omega
      have hkPred : 1 ≤ k - 1 := by omega
      have hkPredR : k - 1 ≤ r := by omega
      have hdK : d < k := by omega
      have hdPred : d < k - 1 := by omega
      have hsame := ih k r hk hkr hdK
      have hlower := ih (k - 1) r hkPred hkPredR hdPred
      have hrPow : r ≤ 2 ^ r := (Nat.lt_two_pow_self (n := r)).le
      have hkPow : k ≤ 2 ^ r := hkr.trans hrPow
      let n := 2 ^ r - 1 - (d + 1)
      have hnSucc : n + 1 = 2 ^ r - 1 - d := by
        dsimp [n]
        omega
      have hdelta := iteratedPrefix_succ_sub (k - 1) n
      rw [show k - 1 + 1 = k by omega, hnSucc, hsame, hlower] at hdelta
      linarith

/-- The paper's indexing: the final `k` entries before `2^r` vanish. -/
theorem iteratedPrefix_dyadic_zero_run (k r i : ℕ)
    (hk : 1 ≤ k) (hkr : k ≤ r) (hi : i < k) :
    iteratedPrefix k (2 ^ r - k + i) = 0 := by
  have hrPow : r ≤ 2 ^ r := (Nat.lt_two_pow_self (n := r)).le
  have hkPow : k ≤ 2 ^ r := hkr.trans hrPow
  have hzero := iteratedPrefix_dyadic_zero_reverse k r (k - 1 - i) hk hkr (by omega)
  have hindex : 2 ^ r - k + i = 2 ^ r - 1 - (k - 1 - i) := by omega
  rw [hindex]
  exact hzero

/-- The sign immediately before a dyadic endpoint has one binary `1` in every
position below the endpoint. -/
@[simp] theorem thueMorseSign_two_pow_sub_one (r : ℕ) :
    thueMorseSign (2 ^ r - 1) = (-1 : ℤ) ^ r := by
  induction r with
  | zero => norm_num [thueMorseSign, binaryWeight]
  | succ r ih =>
      have hpos : 0 < 2 ^ r := by positivity
      have hlt : 2 ^ r - 1 < 2 ^ r := by omega
      rw [show 2 ^ (r + 1) - 1 = 2 ^ r + (2 ^ r - 1) by
        rw [pow_succ]
        omega]
      rw [thueMorseSign_add_pow_two r (2 ^ r - 1) hlt, ih, pow_succ]
      ring

/-- Sharp left boundary of the run. For `k = 0` this is the last Thue--Morse
sign in the block; for positive `k` it proves that the displayed run has
exactly `k` zeros. -/
theorem iteratedPrefix_before_dyadic_run (k r : ℕ) (hkr : k ≤ r) :
    iteratedPrefix k (2 ^ r - k - 1) = (-1 : ℤ) ^ (r - k) := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      have hkPos : 1 ≤ k + 1 := by omega
      have hrPow : r ≤ 2 ^ r := (Nat.lt_two_pow_self (n := r)).le
      have hkPow : k + 1 ≤ 2 ^ r := hkr.trans hrPow
      have hrPowStrict : r < 2 ^ r := Nat.lt_two_pow_self (n := r)
      have hkPowStrict : k + 1 < 2 ^ r := hkr.trans_lt hrPowStrict
      have hzero := iteratedPrefix_dyadic_zero_run (k + 1) r 0 hkPos hkr (by omega)
      have hlower := ih (r := r) (by omega)
      let n := 2 ^ r - (k + 1) - 1
      have hnSucc : n + 1 = 2 ^ r - (k + 1) := by
        dsimp [n]
        omega
      have hzeroIndex : 2 ^ r - (k + 1) + 0 = n + 1 := by omega
      have hlowerIndex : 2 ^ r - k - 1 = n + 1 := by omega
      rw [hzeroIndex] at hzero
      rw [hlowerIndex] at hlower
      have hdelta := iteratedPrefix_succ_sub k n
      rw [hzero, hlower] at hdelta
      have hvalue : iteratedPrefix (k + 1) n = -((-1 : ℤ) ^ (r - k)) := by
        linarith
      rw [hvalue, show r - k = (r - (k + 1)) + 1 by omega, pow_succ]
      ring

/-- On the entries preceding its final `k` zeros, the order-`k` prefix row of
a dyadic block is reciprocal up to the sign `(-1)^(r-k)`. -/
theorem iteratedPrefix_dyadic_reverse_window
    (k r d : ℕ) (hkr : k ≤ r) (hkd : k + d < 2 ^ r) :
    iteratedPrefix k (2 ^ r - k - 1 - d) =
      (-1 : ℤ) ^ (r - k) * iteratedPrefix k d := by
  induction k generalizing r d with
  | zero =>
      have hd : d < 2 ^ r := by omega
      simpa only [Nat.sub_zero, iteratedPrefix_zero] using
        thueMorseSign_dyadic_complement r d hd
  | succ k ih =>
      induction d generalizing r with
      | zero =>
          simpa only [Nat.succ_eq_add_one, Nat.sub_zero,
            iteratedPrefix_at_zero, mul_one] using
            iteratedPrefix_before_dyadic_run (k + 1) r hkr
      | succ d ihd =>
          have hsame :
              iteratedPrefix (k + 1)
                  (2 ^ r - (k + 1) - 1 - d) =
                (-1 : ℤ) ^ (r - (k + 1)) *
                  iteratedPrefix (k + 1) d := by
            simpa only [Nat.succ_eq_add_one] using
              ihd (r := r) hkr (by omega)
          have hlower :=
            ih (r := r) (d := d + 1) (by omega) (by omega)
          let n := 2 ^ r - (k + 1) - 1 - (d + 1)
          have hnSucc :
              n + 1 = 2 ^ r - (k + 1) - 1 - d := by
            dsimp [n]
            omega
          have hlowerIndex :
              2 ^ r - k - 1 - (d + 1) =
                2 ^ r - (k + 1) - 1 - d := by
            omega
          rw [hlowerIndex] at hlower
          have hleft :
              iteratedPrefix (k + 1) n =
                iteratedPrefix (k + 1) (n + 1) -
                  iteratedPrefix k (n + 1) := by
            have hdelta := iteratedPrefix_succ_sub k n
            linarith only [hdelta]
          rw [hnSucc, hsame, hlower] at hleft
          rw [show r - k = (r - (k + 1)) + 1 by omega, pow_succ] at hleft
          have hright := iteratedPrefix_succ_sub k d
          change
            iteratedPrefix (k + 1) n =
              (-1 : ℤ) ^ (r - (k + 1)) *
                iteratedPrefix (k + 1) (d + 1)
          rw [hleft, ← hright]
          ring

/-- Dyadic reversal preserves the zero locus inside the pre-run window of an
iterated prefix row. -/
theorem iteratedPrefix_dyadic_reverse_window_eq_zero_iff
    (k r d : ℕ) (hkr : k ≤ r) (hkd : k + d < 2 ^ r) :
    iteratedPrefix k (2 ^ r - k - 1 - d) = 0 ↔
      iteratedPrefix k d = 0 := by
  have hreflect :=
    iteratedPrefix_dyadic_reverse_window k r d hkr hkd
  have hsign : (-1 : ℤ) ^ (r - k) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  constructor
  · intro hzero
    rw [hreflect] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hsign
  · intro hzero
    rw [hreflect, hzero, mul_zero]

/-- Every iterated prefix sum through the admissible order has value `-1` at
the first index after its dyadic zero run. -/
theorem iteratedPrefix_at_dyadic (k r : ℕ) (hkr : k ≤ r) :
    iteratedPrefix k (2 ^ r) = -1 := by
  induction k with
  | zero =>
      have hsign := thueMorseSign_add_pow_two r 0 (by positivity : 0 < 2 ^ r)
      norm_num [iteratedPrefix, thueMorseSign, binaryWeight] at hsign ⊢
      exact hsign
  | succ k ih =>
      have hkPos : 1 ≤ k + 1 := by omega
      have hendpoint := iteratedPrefix_dyadic_endpoint (k + 1) r hkPos hkr
      have hlower := ih (by omega)
      have hpos : 0 < 2 ^ r := by positivity
      have hdelta := iteratedPrefix_succ_sub k (2 ^ r - 1)
      rw [show 2 ^ r - 1 + 1 = 2 ^ r by omega, hendpoint, hlower] at hdelta
      linarith

end Fabius
