import FabiusFunction.DyadicClosedForm
import Mathlib.Data.Nat.Choose.Sum
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
and upgrades them from monomials to arbitrary rational polynomials and to
affine substitutions.

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
* `thueMorse_polynomial_sum_eq_coeff`, `thueMorse_polynomial_sum_eq_zero`,
  `thueMorse_affine_power_sum_self` -- a block sum against a rational
  polynomial of degree at most `r` returns its degree-`r` coefficient times
  that factor, and vanishes when the degree is below `r`.
* `iteratedPrefix_dyadic_zero_run`, `iteratedPrefix_before_dyadic_run`,
  `iteratedPrefix_at_dyadic` -- for `1 <= k <= r` the `k` values
  `S^k(2^r - k + i)`, `i < k`, all vanish, and the run is exactly that long:
  the entry just before it is `(-1)^(r - k)` and `S^k(2^r) = -1`.

The remaining public declarations are the definitional unfolding
`iteratedPrefix_succ` and the half-block recurrence
`thueMorsePowerSum_succ`, the `simp` normal forms (`iteratedPrefix_zero`,
`iteratedPrefix_at_zero`, `iteratedPrefix_one_two_mul_add_one`,
`thueMorseSign_two_pow_sub_one`), and the endpoint and reverse-indexed forms
of the zero run (`iteratedPrefix_dyadic_endpoint`,
`iteratedPrefix_dyadic_zero_reverse`).

Conventions and caveats.  Prefix sums are inclusive, so `S^(k+1)(n)` ranges
over `j <= n`; `iteratedPrefix` is `ℤ`-valued while the power sums are
`ℚ`-valued.  `iteratedPrefix_eq_sum_kernel` assumes `1 <= k`, matching the
source's positive indexing of `B_k`.  Every zero-run statement assumes
`k <= r`, that is, a block long enough to absorb `k` cancellations, and says
nothing for shorter blocks.  `thueMorse_affine_power_sum_self` does not
depend on the translation, but it carries a factor `y^r` and so degenerates
when the linear coefficient `y` is zero.  The draft's grid normalization
`2^C(k,2)` is applied downstream in `FabiusFunction.ThueMorseGenerating`, not
here.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The iterated inclusive prefix sums from the Thue--Morse paper. -/
def iteratedPrefix : ℕ → ℕ → ℤ
  | 0, n => thueMorseSign n
  | k + 1, n => ∑ j ∈ Finset.range (n + 1), iteratedPrefix k j

@[simp] theorem iteratedPrefix_zero (n : ℕ) :
    iteratedPrefix 0 n = thueMorseSign n := rfl

theorem iteratedPrefix_succ (k n : ℕ) :
    iteratedPrefix (k + 1) n =
      ∑ j ∈ Finset.range (n + 1), iteratedPrefix k j := rfl

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

/-- On polynomials of degree at most `r`, summation against a dyadic
Thue--Morse block extracts the degree-`r` coefficient, up to the explicit
nonzero Prouhet factor. -/
theorem thueMorse_polynomial_sum_eq_coeff (r : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree ≤ r) :
    (∑ h : Fin (2 ^ r),
        (thueMorseSign h.val : ℚ) * p.eval (h.val : ℚ)) =
      p.coeff r *
        ((-1 : ℚ) ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hexpand :
      (∑ d ∈ p.support, ∑ h : Fin (2 ^ r),
          (thueMorseSign h.val : ℚ) *
            (p.coeff d * (h.val : ℚ) ^ d)) =
        ∑ d ∈ p.support, p.coeff d * thueMorsePowerSum r d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [thueMorsePowerSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [hexpand]
  classical
  by_cases hr : r ∈ p.support
  · rw [Finset.sum_eq_single r]
    · rw [thueMorsePowerSum_self]
    · intro d hd hdr
      have hdr' : d < r :=
        lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp d hd |>.trans hp) hdr
      rw [thueMorsePowerSum_eq_zero_of_lt r d hdr', mul_zero]
    · exact fun h => (h hr).elim
  · have hcoeff : p.coeff r = 0 := by
      simpa only [Polynomial.mem_support_iff, not_ne_iff] using hr
    rw [hcoeff, zero_mul]
    apply Finset.sum_eq_zero
    intro d hd
    have hdr : d ≠ r := fun h => hr (h ▸ hd)
    have hdr' : d < r :=
      lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp d hd |>.trans hp) hdr
    rw [thueMorsePowerSum_eq_zero_of_lt r d hdr', mul_zero]

/-- At the sharp Prouhet degree, an affine change of variable contributes only
the expected power of its linear coefficient.  In particular, the sum is
independent of the translation `x`; it may still vanish when that coefficient
is zero. -/
theorem thueMorse_affine_power_sum_self (r : ℕ) (x y : ℚ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) *
      (x + y * (h.val : ℚ)) ^ r) =
      (-1 : ℚ) ^ r * y ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial := by
  let p : Polynomial ℚ :=
    (Polynomial.C x + Polynomial.C y * Polynomial.X) ^ r
  have hlinear :
      (Polynomial.C x + Polynomial.C y * Polynomial.X).natDegree ≤ 1 := by
    calc
      (Polynomial.C x + Polynomial.C y * Polynomial.X).natDegree ≤
          max (Polynomial.C x).natDegree
            (Polynomial.C y * Polynomial.X).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · simp
        · simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le y 1
  have hp : p.natDegree ≤ r := by
    dsimp [p]
    simpa only [Nat.mul_one] using
      Polynomial.natDegree_pow_le_of_le r hlinear
  have hsum := thueMorse_polynomial_sum_eq_coeff r p hp
  have hcoeff : p.coeff r = y ^ r := by
    dsimp [p]
    simpa using
      (Polynomial.coeff_pow_of_natDegree_le
        (p := Polynomial.C x + Polynomial.C y * Polynomial.X)
        (m := r) (n := 1) hlinear)
  calc
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) *
        (x + y * (h.val : ℚ)) ^ r) =
        p.coeff r *
          ((-1 : ℚ) ^ r * (2 : ℚ) ^ r.choose 2 * r.factorial) := by
      simpa [p] using hsum
    _ = _ := by rw [hcoeff]; ring

/-- Thue--Morse signs annihilate every rational polynomial of degree below the
dyadic block exponent. -/
lemma thueMorse_polynomial_sum_eq_zero (r : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree < r) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) * p.eval (h.val : ℚ)) = 0 := by
  rw [thueMorse_polynomial_sum_eq_coeff r p hp.le,
    Polynomial.coeff_eq_zero_of_natDegree_lt hp, zero_mul]

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

private lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

private lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

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
      have hrPow : r ≤ 2 ^ r := self_le_two_pow r
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
  have hrPow : r ≤ 2 ^ r := self_le_two_pow r
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
      have hrPow : r ≤ 2 ^ r := self_le_two_pow r
      have hkPow : k + 1 ≤ 2 ^ r := hkr.trans hrPow
      have hrPowStrict : r < 2 ^ r := by
        have := succ_le_two_pow r
        omega
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
