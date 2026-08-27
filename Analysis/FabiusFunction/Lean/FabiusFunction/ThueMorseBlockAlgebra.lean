import FabiusFunction.DyadicClosedForm
import FabiusFunction.ThueMorseBooleanCube
import FabiusFunction.ThueMorseGenerating
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Algebra of the Thue–Morse block polynomial

The signed block polynomial `P_m = ∑_{n<2^m} ε(n) X^n = ∏_{j<m} (1 - X^(2^j))`
(`thueMorseBlockPolynomial`) is the finite carrier of every generating-function
statement in the formula atlas.  This module proves its basic algebra:

* `one_sub_mul_prod_one_add_two_pow` — the **telescope**
  `(1 - z) · ∏_{i<j} (1 + z^(2^i)) = 1 - z^(2^j)` in any commutative ring:
  each doubling factor extends the geometric truncation.
* `prod_one_sub_two_pow_eq_ladder` — the **multiplicity ladder**
  `∏_{j<m} (1 - z^(2^j)) = (1-z)^m · ∏_{i<m} (1 + z^(2^i))^(m-1-i)`:
  expanding every factor through the telescope makes the zero at `z = 1`
  of order at least `m` visible, and re-proves Prouhet's theorem by pure
  factorization (`one_sub_X_pow_dvd_thueMorseBlockPolynomial`).  The matching
  nondivisibility theorem
  `one_sub_X_pow_succ_not_dvd_thueMorseBlockPolynomial` proves that the order
  is exactly `m`: after the forced factor is removed, the geometric cofactor
  has nonzero value `2^(C(m,2))` at `X = 1`.
* degree data: `natDegree_thueMorseBlockPolynomial` (`= 2^m - 1`),
  `coeff_thueMorseBlockPolynomial_top`, `leadingCoeff_thueMorseBlockPolynomial`
  (`= (-1)^m`), `thueMorseBlockPolynomial_ne_zero`, resting on the sign
  `thueMorseSign_two_pow_sub_one` of the all-ones word (from
  `ThueMorsePrefix`).
* `reverse_thueMorseBlockPolynomial` — **reciprocity**: reversing the
  coefficient word multiplies `P_m` by `(-1)^m`, the polynomial form of the
  complement symmetry `ε(2^m-1-n) = (-1)^m ε(n)`; and its evaluation form
  `sum_thueMorseSign_mul_pow_reflect` over any commutative ring.
* `thueMorseBlockPolynomial_eq_cyclotomic_prod` — the **cyclotomic
  multiplicity table** `P_m = (-1)^m · ∏_{q<m} Φ_{2^q}^(m-q)` over `ℤ`: a
  primitive `2^q`-th root of unity is a zero of `P_m` of multiplicity
  `m - q`, which simultaneously explains Prouhet cancellation at `z = 1`
  and the systematic zeros of the dyadic discrete Fourier transform.
* the **binomial-basis moments**: substituting `z ↦ 1 + X` in the master
  product turns each factor into `-X` times a geometric sum
  (`sum_thueMorseSign_mul_one_add_X_pow`), so the signed binomial sums
  `∑_{n<2^m} ε(n) · C(n,r)` vanish for all `r < m`
  (`sum_thueMorseSign_mul_choose_eq_zero`) and equal `(-1)^m 2^(C(m,2))` at
  `r = m` (`sum_thueMorseSign_mul_choose_self`) — the Prouhet annihilation
  in the basis where the sharp value needs no factorial.  Evaluating iterated
  derivatives at one recovers the same moments with the expected `r!` factor.

Everything is exact algebra over an arbitrary commutative ring; no analysis
and no rational denominators appear anywhere.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The telescope and the multiplicity ladder -/

/-- **Telescope.**  In any commutative ring,
`(1 - z) · ∏_{i<j} (1 + z^(2^i)) = 1 - z^(2^j)`: multiplying by the next
doubling factor squares the truncation level.  This is the finite algebraic
core of the classical factorization `1 - z^(2^j) = (1-z)(1+z)(1+z²)(1+z⁴)⋯`. -/
theorem one_sub_mul_prod_one_add_two_pow {R : Type*} [CommRing R]
    (z : R) (j : ℕ) :
    (1 - z) * ∏ i ∈ range j, (1 + z ^ 2 ^ i) = 1 - z ^ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih]
      have h : z ^ 2 ^ (j + 1) = z ^ 2 ^ j * z ^ 2 ^ j := by
        rw [pow_succ, mul_two, pow_add]
      rw [h]
      ring

/-- **Multiplicity ladder.**  Over any commutative ring,
`∏_{j<m} (1 - z^(2^j)) = (1-z)^m · ∏_{i<m} (1 + z^(2^i))^(m-1-i)`.
The factor `1 + z^(2^i)` divides `1 - z^(2^j)` once for every `j` with
`i < j < m`, hence appears with multiplicity `m - 1 - i`; the factor `1 - z`
divides every term, hence appears with multiplicity `m`. -/
theorem prod_one_sub_two_pow_eq_ladder {R : Type*} [CommRing R]
    (z : R) (m : ℕ) :
    ∏ j ∈ range m, (1 - z ^ 2 ^ j) =
      (1 - z) ^ m * ∏ i ∈ range m, (1 + z ^ 2 ^ i) ^ (m - 1 - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih, ← one_sub_mul_prod_one_add_two_pow z m]
      have hexp : ∏ i ∈ range (m + 1), (1 + z ^ 2 ^ i) ^ (m + 1 - 1 - i) =
          (∏ i ∈ range m, (1 + z ^ 2 ^ i) ^ (m - 1 - i)) *
            ∏ i ∈ range m, (1 + z ^ 2 ^ i) := by
        rw [Finset.prod_range_succ, Nat.add_sub_cancel, Nat.sub_self,
          pow_zero, mul_one, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i hi => ?_
        have him : i < m := Finset.mem_range.mp hi
        rw [← pow_succ]
        congr 1
        omega
      rw [hexp]
      ring

/-- The block polynomial with its `(1 - X)^m` factor made explicit. -/
theorem thueMorseBlockPolynomial_eq_ladder (m : ℕ) :
    thueMorseBlockPolynomial m =
      (1 - Polynomial.X) ^ m *
        ∏ i ∈ range m,
          ((1 : Polynomial ℤ) + Polynomial.X ^ 2 ^ i) ^ (m - 1 - i) := by
  rw [thueMorseBlockPolynomial_eq_product]
  exact prod_one_sub_two_pow_eq_ladder Polynomial.X m

/-- **Prouhet divisibility.**  `(1 - X)^m` divides the block polynomial: the
Thue–Morse signs annihilate all polynomials of degree below `m` because the
generating polynomial has a zero of order `m` at `X = 1`. -/
theorem one_sub_X_pow_dvd_thueMorseBlockPolynomial (m : ℕ) :
    (1 - Polynomial.X : Polynomial ℤ) ^ m ∣ thueMorseBlockPolynomial m :=
  ⟨_, thueMorseBlockPolynomial_eq_ladder m⟩

/-! ### Degree data and reciprocity -/

/-- Vanishing above the block: the block polynomial has no coefficients at or
beyond `2^r`. -/
theorem coeff_thueMorseBlockPolynomial_of_le (r n : ℕ) (hn : 2 ^ r ≤ n) :
    (thueMorseBlockPolynomial r).coeff n = 0 := by
  rw [thueMorseBlockPolynomial, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkr : k < 2 ^ r := Finset.mem_range.mp hk
  rw [Polynomial.coeff_monomial, if_neg (by omega)]

/-- The top coefficient of the block polynomial is `(-1)^m`. -/
theorem coeff_thueMorseBlockPolynomial_top (m : ℕ) :
    (thueMorseBlockPolynomial m).coeff (2 ^ m - 1) = (-1) ^ m := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  rw [coeff_thueMorseBlockPolynomial m (2 ^ m - 1) (by omega)]
  exact thueMorseSign_two_pow_sub_one m

/-- The block polynomial has degree exactly `2^m - 1`. -/
theorem natDegree_thueMorseBlockPolynomial (m : ℕ) :
    (thueMorseBlockPolynomial m).natDegree = 2 ^ m - 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_thueMorseBlockPolynomial_of_le m N (by omega)
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_thueMorseBlockPolynomial_top]
    exact pow_ne_zero m (by norm_num)

/-- The block polynomial is nonzero. -/
theorem thueMorseBlockPolynomial_ne_zero (m : ℕ) :
    thueMorseBlockPolynomial m ≠ 0 := fun h => by
  have h2 := coeff_thueMorseBlockPolynomial_top m
  rw [h, Polynomial.coeff_zero] at h2
  exact absurd h2.symm (pow_ne_zero m (by norm_num))

/-- The leading coefficient of the block polynomial is `(-1)^m`. -/
theorem leadingCoeff_thueMorseBlockPolynomial (m : ℕ) :
    (thueMorseBlockPolynomial m).leadingCoeff = (-1) ^ m := by
  have h : (thueMorseBlockPolynomial m).leadingCoeff =
      (thueMorseBlockPolynomial m).coeff
        ((thueMorseBlockPolynomial m).natDegree) := rfl
  rw [h, natDegree_thueMorseBlockPolynomial, coeff_thueMorseBlockPolynomial_top]

/-- **Reciprocity.**  Reversing the coefficient word of the block polynomial
multiplies it by `(-1)^m`: as a Laurent identity,
`z^(2^m-1) · P_m(1/z) = (-1)^m · P_m(z)`.  This is the polynomial form of the
dyadic complement symmetry `ε(2^m - 1 - n) = (-1)^m · ε(n)`. -/
theorem reverse_thueMorseBlockPolynomial (m : ℕ) :
    (thueMorseBlockPolynomial m).reverse = (-1) ^ m * thueMorseBlockPolynomial m := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hC : ((-1 : Polynomial ℤ)) ^ m = Polynomial.C ((-1 : ℤ) ^ m) := by
    rw [map_pow, map_neg, map_one]
  ext n
  rw [Polynomial.coeff_reverse, natDegree_thueMorseBlockPolynomial, hC,
    Polynomial.coeff_C_mul]
  by_cases hn : n < 2 ^ m
  · have hle : n ≤ 2 ^ m - 1 := by omega
    have hlt2 : 2 ^ m - 1 - n < 2 ^ m := by omega
    rw [Polynomial.revAt_le hle,
      coeff_thueMorseBlockPolynomial m (2 ^ m - 1 - n) hlt2,
      coeff_thueMorseBlockPolynomial m n hn,
      thueMorseSign_dyadic_complement m n hn]
  · have hge : 2 ^ m ≤ n := by omega
    rw [Polynomial.revAt_eq_self_of_lt (by omega : 2 ^ m - 1 < n),
      coeff_thueMorseBlockPolynomial_of_le m n hge, mul_zero]

/-- Evaluation form of reciprocity over any commutative ring:
`∑_{n<2^m} ε(n) z^(2^m-1-n) = (-1)^m · ∑_{n<2^m} ε(n) z^n`. -/
theorem sum_thueMorseSign_mul_pow_reflect {R : Type*} [CommRing R]
    (z : R) (m : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ (2 ^ m - 1 - n) =
      (-1) ^ m * ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * z ^ n := by
  have h := Finset.sum_range_reflect
    (fun n => ((thueMorseSign n : ℤ) : R) * z ^ (2 ^ m - 1 - n)) (2 ^ m)
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n < 2 ^ m := Finset.mem_range.mp hn
  have h1 : 2 ^ m - 1 - (2 ^ m - 1 - n) = n := by omega
  rw [h1, thueMorseSign_dyadic_complement m n hn']
  push_cast
  ring

/-! ### Binomial-basis moments -/

/-- Substituting `z ↦ 1 + X` in the master product: every factor
`1 - (1+X)^(2^j)` is `-X` times the geometric sum `∑_{i<2^j} (1+X)^i`, so the
signed binomial generating polynomial carries an explicit factor `X^m`. -/
theorem sum_thueMorseSign_mul_one_add_X_pow {R : Type*} [CommRing R] (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : Polynomial R) * (1 + Polynomial.X) ^ n =
      (-1) ^ m * Polynomial.X ^ m *
        ∏ j ∈ range m, ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i := by
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign (1 + Polynomial.X : Polynomial R) m]
  have hfac : ∀ j ∈ range m, (1 : Polynomial R) - (1 + Polynomial.X) ^ 2 ^ j =
      -1 * Polynomial.X * ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i := by
    intro j _
    have h := geom_sum_mul (1 + Polynomial.X : Polynomial R) (2 ^ j)
    have h2 : (1 + Polynomial.X : Polynomial R) - 1 = Polynomial.X := by ring
    rw [h2] at h
    linear_combination h
  calc ∏ j ∈ range m, ((1 : Polynomial R) - (1 + Polynomial.X) ^ 2 ^ j)
      = ∏ j ∈ range m,
          (-1 * Polynomial.X * ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i) :=
        Finset.prod_congr rfl hfac
    _ = (∏ _j ∈ range m, (-1 * Polynomial.X : Polynomial R)) *
          ∏ j ∈ range m, ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i :=
        Finset.prod_mul_distrib
    _ = (-1) ^ m * Polynomial.X ^ m *
          ∏ j ∈ range m, ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i := by
        rw [Finset.prod_const, Finset.card_range, mul_pow]

/-- Coefficient dictionary: the `k`-th coefficient of the signed binomial
generating polynomial is the signed binomial moment `∑_{n<2^m} ε(n)·C(n,k)`. -/
theorem coeff_sum_thueMorseSign_mul_one_add_X_pow {R : Type*} [CommRing R]
    (m k : ℕ) :
    (∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : Polynomial R) * (1 + Polynomial.X) ^ n).coeff k =
      ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * (n.choose k : R) := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul,
    Polynomial.coeff_one_add_X_pow]

/-- **Binomial Prouhet annihilation.**  For every `r < m`, the Thue–Morse
signs kill the binomial coefficients of order `r` on the dyadic block:
`∑_{n<2^m} ε(n) · C(n,r) = 0`, over any commutative ring. -/
theorem sum_thueMorseSign_mul_choose_eq_zero {R : Type*} [CommRing R]
    (m r : ℕ) (hr : r < m) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * (n.choose r : R) = 0 := by
  have h := congrArg (fun p : Polynomial R => p.coeff r)
    (sum_thueMorseSign_mul_one_add_X_pow (R := R) m)
  simp only [coeff_sum_thueMorseSign_mul_one_add_X_pow] at h
  rw [h]
  have hdvd : (Polynomial.X : Polynomial R) ^ m ∣
      (-1) ^ m * Polynomial.X ^ m *
        ∏ j ∈ range m, ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i :=
    ⟨(-1) ^ m * ∏ j ∈ range m, ∑ i ∈ range (2 ^ j), (1 + Polynomial.X) ^ i,
      by ring⟩
  exact Polynomial.X_pow_dvd_iff.mp hdvd r hr

/-- **The first surviving binomial moment.**  At `r = m` the signed binomial
moment is `(-1)^m · 2^(C(m,2))`, over any commutative ring: in the binomial
basis the sharp Prouhet value carries no factorial, only the dyadic constant. -/
theorem sum_thueMorseSign_mul_choose_self {R : Type*} [CommRing R] (m : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * (n.choose m : R) =
      (-1) ^ m * 2 ^ m.choose 2 := by
  have h := congrArg (fun p : Polynomial R => p.coeff m)
    (sum_thueMorseSign_mul_one_add_X_pow (R := R) m)
  simp only [coeff_sum_thueMorseSign_mul_one_add_X_pow] at h
  rw [h]
  have hC : ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1 : R) ^ m) := by
    rw [map_pow, map_neg, map_one]
  rw [mul_assoc, hC, Polynomial.coeff_C_mul]
  congr 1
  have hXm := Polynomial.coeff_X_pow_mul
    (∏ j ∈ range m, ∑ i ∈ range (2 ^ j), (1 + Polynomial.X : Polynomial R) ^ i)
    m 0
  rw [zero_add] at hXm
  rw [hXm, ← Polynomial.constantCoeff_apply, map_prod]
  have hG : ∀ j ∈ range m,
      Polynomial.constantCoeff
          (∑ i ∈ range (2 ^ j), (1 + Polynomial.X : Polynomial R) ^ i) =
        (2 : R) ^ j := by
    intro j _
    rw [map_sum]
    have hone : ∀ i ∈ range (2 ^ j),
        Polynomial.constantCoeff ((1 + Polynomial.X : Polynomial R) ^ i) =
          (1 : R) := by
      intro i _
      rw [Polynomial.constantCoeff_apply, Polynomial.coeff_one_add_X_pow]
      simp
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [Finset.prod_congr rfl hG, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Nat.choose_two_right]

/-- Integer form of the binomial Prouhet annihilation. -/
theorem sum_thueMorseSign_mul_choose_eq_zero_int (m r : ℕ) (hr : r < m) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * (n.choose r : ℤ) = 0 := by
  simpa using sum_thueMorseSign_mul_choose_eq_zero (R := ℤ) m r hr

/-- Integer form of the first surviving binomial moment. -/
theorem sum_thueMorseSign_mul_choose_self_int (m : ℕ) :
    ∑ n ∈ range (2 ^ m), thueMorseSign n * (n.choose m : ℤ) =
      (-1) ^ m * 2 ^ m.choose 2 := by
  simpa using sum_thueMorseSign_mul_choose_self (R := ℤ) m

/-! ### Derivatives at one -/

/-- Evaluating the `r`-th derivative of the Thue--Morse block polynomial at
one gives `r!` times its signed binomial moment. -/
theorem iterate_derivative_thueMorseBlockPolynomial_eval_one
    (m r : ℕ) :
    (Polynomial.derivative^[r] (thueMorseBlockPolynomial m)).eval (1 : ℤ) =
      (r.factorial : ℤ) *
        ∑ n ∈ range (2 ^ m),
          thueMorseSign n * (n.choose r : ℤ) := by
  unfold thueMorseBlockPolynomial
  rw [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp only [Polynomial.eval_C_mul, Polynomial.eval_X_pow, one_pow, mul_one]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  ring

/-- Every derivative below the order of the zero at one vanishes. -/
theorem iterate_derivative_thueMorseBlockPolynomial_eval_one_of_lt
    (m r : ℕ) (hr : r < m) :
    (Polynomial.derivative^[r] (thueMorseBlockPolynomial m)).eval (1 : ℤ) =
      0 := by
  rw [iterate_derivative_thueMorseBlockPolynomial_eval_one m r,
    sum_thueMorseSign_mul_choose_eq_zero_int m r hr, mul_zero]

/-- The first nonzero derivative of the Thue--Morse block polynomial at one
has the sharp Prouhet value. -/
theorem iterate_derivative_thueMorseBlockPolynomial_eval_one_self
    (m : ℕ) :
    (Polynomial.derivative^[m] (thueMorseBlockPolynomial m)).eval (1 : ℤ) =
      (-1 : ℤ) ^ m * (m.factorial : ℤ) * (2 : ℤ) ^ m.choose 2 := by
  rw [iterate_derivative_thueMorseBlockPolynomial_eval_one m m,
    sum_thueMorseSign_mul_choose_self_int m]
  ring

/-! ### Geometric-sum factorization and exact multiplicity -/

/-- Geometric form of the ladder: over any commutative ring,
`∏_{j<r} (1 - z^(2^j)) = (1-z)^r · ∏_{j<r} (1 + z + ⋯ + z^(2^j - 1))`.
Dividing the block polynomial by `(1-z)^k` for `k ≤ r` therefore leaves a
polynomial of degree `2^r - k - 1` — the algebra behind the terminal zero
runs of the iterated prefix sums. -/
theorem prod_one_sub_two_pow_eq_geom {R : Type*} [CommRing R]
    (z : R) (r : ℕ) :
    ∏ j ∈ range r, (1 - z ^ 2 ^ j) =
      (1 - z) ^ r * ∏ j ∈ range r, ∑ i ∈ range (2 ^ j), z ^ i := by
  calc ∏ j ∈ range r, (1 - z ^ 2 ^ j)
      = ∏ j ∈ range r, ((1 - z) * ∑ i ∈ range (2 ^ j), z ^ i) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [mul_comm, geom_sum_mul_neg]
    _ = (1 - z) ^ r * ∏ j ∈ range r, ∑ i ∈ range (2 ^ j), z ^ i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- The block polynomial in geometric-product form:
`P_r = (1-X)^r · ∏_{j<r} (1 + X + ⋯ + X^(2^j-1))`. -/
theorem thueMorseBlockPolynomial_eq_geom_prod (r : ℕ) :
    thueMorseBlockPolynomial r =
      (1 - Polynomial.X) ^ r *
        ∏ j ∈ range r, ∑ i ∈ range (2 ^ j), (Polynomial.X : Polynomial ℤ) ^ i := by
  rw [thueMorseBlockPolynomial_eq_product]
  exact prod_one_sub_two_pow_eq_geom Polynomial.X r

/-- **The zero at one has exact order `m`.**  The next power
`(1-X)^(m+1)` does not divide the Thue–Morse block polynomial `P_m`.
Together with `one_sub_X_pow_dvd_thueMorseBlockPolynomial`, this says that
the multiplicity is exactly `m`.

The proof exposes the obstruction rather than appealing to an abstract
multiplicity API.  After cancelling the known factor `(1-X)^m`, an extra
factor would force the geometric cofactor
`∏_{j<m} (1 + X + ⋯ + X^(2^j-1))` to vanish at `X=1`; its value there is
the nonzero product `∏_{j<m} 2^j = 2^(C(m,2))`. -/
theorem one_sub_X_pow_succ_not_dvd_thueMorseBlockPolynomial (m : ℕ) :
    ¬ (1 - Polynomial.X : Polynomial ℤ) ^ (m + 1) ∣
      thueMorseBlockPolynomial m := by
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  let Q : Polynomial ℤ :=
    ∏ j ∈ range m,
      ∑ i ∈ range (2 ^ j), (Polynomial.X : Polynomial ℤ) ^ i
  have hfactor : thueMorseBlockPolynomial m =
      (1 - Polynomial.X) ^ m * Q := by
    dsimp only [Q]
    exact thueMorseBlockPolynomial_eq_geom_prod m
  have hbase : (1 - Polynomial.X : Polynomial ℤ) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℤ => p.coeff 1) hzero
    norm_num at hcoeff
  have hcancel :
      (1 - Polynomial.X : Polynomial ℤ) ^ m * Q =
        (1 - Polynomial.X) ^ m * ((1 - Polynomial.X) * q) := by
    calc
      (1 - Polynomial.X : Polynomial ℤ) ^ m * Q =
          thueMorseBlockPolynomial m := hfactor.symm
      _ = (1 - Polynomial.X) ^ (m + 1) * q := hq
      _ = (1 - Polynomial.X) ^ m * ((1 - Polynomial.X) * q) := by
        rw [pow_succ]
        ring
  have hcofactor : Q = (1 - Polynomial.X) * q :=
    mul_left_cancel₀ (pow_ne_zero m hbase) hcancel
  have hQeval : Polynomial.eval (1 : ℤ) Q = (2 : ℤ) ^ m.choose 2 := by
    dsimp only [Q]
    rw [Polynomial.eval_prod]
    have hterm : ∀ j ∈ range m,
        Polynomial.eval (1 : ℤ)
            (∑ i ∈ range (2 ^ j), (Polynomial.X : Polynomial ℤ) ^ i) =
          (2 : ℤ) ^ j := by
      intro j _
      rw [Polynomial.eval_finsetSum]
      simp
    rw [Finset.prod_congr rfl hterm, Finset.prod_pow_eq_pow_sum,
      Finset.sum_range_id, Nat.choose_two_right]
  have hQzero : Polynomial.eval (1 : ℤ) Q = 0 := by
    rw [hcofactor]
    simp
  rw [hQeval] at hQzero
  exact (pow_ne_zero (m.choose 2) (by norm_num : (2 : ℤ) ≠ 0)) hQzero

/-! ### Cyclotomic factorization -/

/-- The `2^(q+1)`-st cyclotomic polynomial is `1 + X^(2^q)`. -/
theorem cyclotomic_two_pow_succ (R : Type*) [CommRing R] (q : ℕ) :
    Polynomial.cyclotomic (2 ^ (q + 1)) R = 1 + Polynomial.X ^ 2 ^ q := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ]

/-- **Cyclotomic multiplicity table.**  Over `ℤ`,
`P_m = (-1)^m · ∏_{q<m} Φ_{2^q}^(m-q)`: the block polynomial is, up to sign,
a product of `2`-power cyclotomic polynomials, a primitive `2^q`-th root of
unity being a zero of multiplicity exactly `m - q` for `0 ≤ q < m`. -/
theorem thueMorseBlockPolynomial_eq_cyclotomic_prod (m : ℕ) :
    thueMorseBlockPolynomial m =
      (-1) ^ m *
        ∏ q ∈ range m, Polynomial.cyclotomic (2 ^ q) ℤ ^ (m - q) := by
  cases m with
  | zero => norm_num [thueMorseBlockPolynomial, thueMorseSign, binaryWeight]
  | succ k =>
      have hL : thueMorseBlockPolynomial (k + 1) =
          (1 - Polynomial.X) ^ (k + 1) *
            ∏ i ∈ range k,
              ((1 : Polynomial ℤ) + Polynomial.X ^ 2 ^ i) ^ (k - i) := by
        rw [thueMorseBlockPolynomial_eq_ladder, Finset.prod_range_succ]
        simp only [Nat.add_sub_cancel]
        rw [Nat.sub_self, pow_zero, mul_one]
      have hR : ∏ q ∈ range (k + 1),
            Polynomial.cyclotomic (2 ^ q) ℤ ^ (k + 1 - q) =
          (Polynomial.X - 1) ^ (k + 1) *
            ∏ i ∈ range k,
              ((1 : Polynomial ℤ) + Polynomial.X ^ 2 ^ i) ^ (k - i) := by
        rw [Finset.prod_range_succ']
        simp only [pow_zero, Polynomial.cyclotomic_one, Nat.sub_zero,
          Nat.add_sub_add_right]
        rw [mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [cyclotomic_two_pow_succ]
      rw [hL, hR, ← neg_sub Polynomial.X 1, neg_pow]
      ring

end Fabius
