import FabiusFunction.Basic
import FabiusFunction.ThueMorseBooleanCube
import FabiusFunction.ThueMorseWalsh

/-!
# Total complex finite-product bridges for Thue--Morse blocks

The finite Thue--Morse product is valid in every commutative ring.  Over
`ℂ`, factoring its exponential specializations through sine and through the
removable exponential quotient gives two exact analytic normalizations:

* `sum_thueMorseSign_cexp_eq_sin_prod` is the complex half-angle formula;
* `thueMorseBlock_cexp_eq_sincPrefix` is the total finite sinc bridge;
* `thueMorseBlock_exp_neg_eq_laplacePrefix` is the total finite Laplace
  bridge.
* `complexLaplacePrefix_eq_exp_mul_shiftedComplexSincPrefix` is the exact
  finite Fourier--Laplace rotation.

The primary equalities never divide by the free variable.  Consequently they
include the origin without a side condition: the order-`m` zero is displayed
as the factor `t ^ m` or `s ^ m`, while each removable quotient is normalized
to one.  Quotient forms are supplied only as corollaries away from zero.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Dyadic bookkeeping

Two finite-product facts recur in every dyadic bridge: the geometric
exponent sum `∑_{j<K} j = K choose 2` and its shifted form
`∑_{k<m} (k+1) = (m+1) choose 2`, and the reflection
`2^j · x / 2^m = x / 2^((m-1-j)+1)` that reads a dyadic chain from the
top scale down.  They are stated once here, in any commutative monoid
where they make sense. -/

/-- `∏_{j<K} z^j = z^(K choose 2)` in any commutative monoid. -/
theorem prod_range_pow_eq_pow_choose_two {M : Type*} [CommMonoid M]
    (z : M) (K : ℕ) :
    ∏ j ∈ range K, z ^ j = z ^ K.choose 2 := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    Nat.choose_two_right]

/-- The shifted exponent sum: `∏_{k<m} z^(k+1) = z^((m+1) choose 2)`. -/
theorem prod_range_pow_succ_eq_pow_choose_two {M : Type*} [CommMonoid M]
    (z : M) (m : ℕ) :
    ∏ k ∈ range m, z ^ (k + 1) = z ^ (m + 1).choose 2 := by
  rw [← prod_range_pow_eq_pow_choose_two, Finset.prod_range_succ',
    pow_zero, mul_one]

/-- Reading a dyadic chain from the top: for `j < m`,
`2^j · x / 2^m = x / 2^((m-1-j)+1)`. -/
theorem two_pow_mul_div_two_pow_eq_div_reflect {j m : ℕ} (hj : j < m)
    (x : ℂ) :
    (2 : ℂ) ^ j * x / (2 : ℂ) ^ m =
      x / (2 : ℂ) ^ ((m - 1 - j) + 1) := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have he : j + ((m - 1 - j) + 1) = m := by omega
  rw [div_eq_div_iff (pow_ne_zero _ htwo) (pow_ne_zero _ htwo),
    mul_comm ((2 : ℂ) ^ j) x, mul_assoc, ← pow_add, he]

/-- A product over the dyadic chain `2^j · x / 2^m`, `j < m`, is the
product over the shifted scales `x / 2^(k+1)`, `k < m`, in reverse
order. -/
theorem prod_range_reflect_dyadic {M : Type*} [CommMonoid M] (F : ℂ → M)
    (x : ℂ) (m : ℕ) :
    ∏ j ∈ range m, F ((2 : ℂ) ^ j * x / (2 : ℂ) ^ m) =
      ∏ k ∈ range m, F (x / (2 : ℂ) ^ (k + 1)) := by
  calc
    ∏ j ∈ range m, F ((2 : ℂ) ^ j * x / (2 : ℂ) ^ m) =
        ∏ j ∈ range m, F (x / (2 : ℂ) ^ ((m - 1 - j) + 1)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [two_pow_mul_div_two_pow_eq_div_reflect
        (Finset.mem_range.mp hj) x]
    _ = ∏ k ∈ range m, F (x / (2 : ℂ) ^ (k + 1)) :=
      Finset.prod_range_reflect (fun k => F (x / (2 : ℂ) ^ (k + 1))) m

/-- At a positive level the block step `2 t / 2^m` is the atlas step
`t / 2^(m-1)`. -/
private theorem two_mul_div_two_pow {m : ℕ} (hm : 1 ≤ m) (t : ℂ) :
    2 * t / (2 : ℂ) ^ m = t / (2 : ℂ) ^ (m - 1) := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hm' : m - 1 + 1 = m := by omega
  have hpow : (2 : ℂ) ^ m = (2 : ℂ) ^ (m - 1) * 2 := by
    calc
      _ = (2 : ℂ) ^ ((m - 1) + 1) := by rw [hm']
      _ = _ := pow_succ _ _
  rw [div_eq_div_iff (pow_ne_zero _ htwo) (pow_ne_zero _ htwo), hpow]
  ring

/-! ## The complex half-angle identity -/

/-- The complex half-angle factorization
`1 - exp (i z) = -2i * exp (i z / 2) * sin (z / 2)`. -/
theorem one_sub_cexp_mul_I (z : ℂ) :
    1 - Complex.exp (z * Complex.I) =
      -2 * Complex.I * Complex.exp ((z / 2) * Complex.I) *
        Complex.sin (z / 2) := by
  have h2sin := Complex.two_sin (z / 2)
  have hI := Complex.I_sq
  have hprod :
      Complex.exp ((z / 2) * Complex.I) *
          Complex.exp (-(z / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← add_mul,
      show z / 2 + -(z / 2) = 0 by ring,
      zero_mul, Complex.exp_zero]
  have hsq :
      Complex.exp ((z / 2) * Complex.I) *
          Complex.exp ((z / 2) * Complex.I) =
        Complex.exp (z * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination
    (Complex.I * Complex.exp ((z / 2) * Complex.I)) * h2sin +
    (Complex.exp ((z / 2) * Complex.I) *
        Complex.exp (-(z / 2) * Complex.I) -
      Complex.exp ((z / 2) * Complex.I) *
        Complex.exp ((z / 2) * Complex.I)) * hI -
    hprod + hsq

/-- The defining denominator of `complexSinc` can be cleared at every
complex argument, including zero. -/
theorem mul_complexSinc (z : ℂ) : z * complexSinc z = Complex.sin z := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · rw [complexSinc, if_neg hz]
    field_simp

/-- The complex sine-product form of a finite Thue--Morse block:
`sum ε(n) exp(iz)^n` is one phase times the product of the dyadic sines.
There is no reality or nonvanishing hypothesis. -/
theorem sum_thueMorseSign_cexp_eq_sin_prod (z : ℂ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
        Complex.exp (z * Complex.I) ^ n =
      (-2 * Complex.I) ^ m *
        Complex.exp ((((2 ^ m - 1 : ℕ) : ℂ) * z / 2) * Complex.I) *
        ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * z) / 2) := by
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign
    (Complex.exp (z * Complex.I)) m]
  calc
    ∏ j ∈ range m, (1 - Complex.exp (z * Complex.I) ^ 2 ^ j) =
        ∏ j ∈ range m,
          (-2 * Complex.I *
            Complex.exp ((((2 : ℂ) ^ j * z) / 2) * Complex.I) *
            Complex.sin (((2 : ℂ) ^ j * z) / 2)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      have hz : Complex.exp (z * Complex.I) ^ 2 ^ j =
          Complex.exp (((2 : ℂ) ^ j * z) * Complex.I) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hz, one_sub_cexp_mul_I]
    _ = (-2 * Complex.I) ^ m *
          (∏ j ∈ range m,
            Complex.exp ((((2 : ℂ) ^ j * z) / 2) * Complex.I)) *
          ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * z) / 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range]
    _ = (-2 * Complex.I) ^ m *
          Complex.exp ((((2 ^ m - 1 : ℕ) : ℂ) * z / 2) * Complex.I) *
          ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * z) / 2) := by
      congr 2
      rw [← Complex.exp_sum]
      congr 1
      rw [← Finset.sum_mul]
      congr 1
      have hgeom : ∑ j ∈ range m, ((2 : ℂ) ^ j) =
          ((2 ^ m - 1 : ℕ) : ℂ) := by
        have h := sum_range_two_pow m
        rw [← h]
        push_cast
        ring
      rw [← Finset.sum_div, ← Finset.sum_mul, hgeom]

/-! ## Total sinc normalization -/

/-- The first `m` dyadic sinc factors, in the finite-block normalization. -/
noncomputable def shiftedComplexSincPrefix (m : ℕ) (t : ℂ) : ℂ :=
  ∏ k ∈ range m, complexSinc (t / (2 : ℂ) ^ (k + 1))

/-- The empty sinc prefix is one. -/
@[simp]
theorem shiftedComplexSincPrefix_zero (t : ℂ) :
    shiftedComplexSincPrefix 0 t = 1 := by
  simp [shiftedComplexSincPrefix]

/-- Every finite sinc prefix takes the normalized value one at the origin. -/
@[simp]
theorem shiftedComplexSincPrefix_apply_zero (m : ℕ) :
    shiftedComplexSincPrefix m 0 = 1 := by
  simp [shiftedComplexSincPrefix, complexSinc]

/-- Appending one scale appends the next dyadic sinc factor. -/
theorem shiftedComplexSincPrefix_succ (m : ℕ) (t : ℂ) :
    shiftedComplexSincPrefix (m + 1) t =
      shiftedComplexSincPrefix m t *
        complexSinc (t / (2 : ℂ) ^ (m + 1)) := by
  simp [shiftedComplexSincPrefix, Finset.prod_range_succ]

/-- The exact oscillatory finite-block identity in its total sinc form.  The
factor `t ^ m` records the removable order-`m` zero at the origin. -/
theorem thueMorseBlock_cexp_eq_sincPrefix (m : ℕ) (t : ℂ) :
    ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
        Complex.exp (((2 * t / (2 : ℂ) ^ m)) * Complex.I) ^ n =
      (-Complex.I) ^ m * t ^ m / (2 : ℂ) ^ (Nat.choose m 2) *
        Complex.exp (Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) *
        shiftedComplexSincPrefix m t := by
  rw [sum_thueMorseSign_cexp_eq_sin_prod]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hsine :
      (∏ j ∈ range m,
          Complex.sin (((2 : ℂ) ^ j *
            (2 * t / (2 : ℂ) ^ m)) / 2)) =
        (∏ k ∈ range m, t / (2 : ℂ) ^ (k + 1)) *
          shiftedComplexSincPrefix m t := by
    calc
      (∏ j ∈ range m,
          Complex.sin (((2 : ℂ) ^ j *
            (2 * t / (2 : ℂ) ^ m)) / 2)) =
          ∏ j ∈ range m,
            Complex.sin ((2 : ℂ) ^ j * t / (2 : ℂ) ^ m) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show ((2 : ℂ) ^ j * (2 * t / (2 : ℂ) ^ m)) / 2 =
            (2 : ℂ) ^ j * t / (2 : ℂ) ^ m by
          field_simp [pow_ne_zero _ htwo]]
      _ = ∏ k ∈ range m,
            Complex.sin (t / (2 : ℂ) ^ (k + 1)) :=
        prod_range_reflect_dyadic Complex.sin t m
      _ = ∏ k ∈ range m,
            ((t / (2 : ℂ) ^ (k + 1)) *
              complexSinc (t / (2 : ℂ) ^ (k + 1))) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [mul_complexSinc]
      _ = (∏ k ∈ range m, t / (2 : ℂ) ^ (k + 1)) *
            shiftedComplexSincPrefix m t := by
        rw [Finset.prod_mul_distrib]
        rfl
  have hscale :
      ∏ k ∈ range m, t / (2 : ℂ) ^ (k + 1) =
        t ^ m / (2 : ℂ) ^ (Nat.choose (m + 1) 2) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
      prod_range_pow_succ_eq_pow_choose_two]
  have hphase :
      Complex.exp
          ((((2 ^ m - 1 : ℕ) : ℂ) *
            (2 * t / (2 : ℂ) ^ m) / 2) * Complex.I) =
        Complex.exp (Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) := by
    congr 1
    have hcast : (((2 ^ m - 1 : ℕ) : ℂ)) = (2 : ℂ) ^ m - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
      norm_num
    rw [hcast]
    field_simp [pow_ne_zero _ htwo]
  rw [hsine, hscale, hphase]
  have hchoose := Fabius.choose_succ_two m
  have hcoeff : (-2 * Complex.I) ^ m =
      (2 : ℂ) ^ m * (-Complex.I) ^ m := by
    rw [show -2 * Complex.I = (2 : ℂ) * (-Complex.I) by ring, mul_pow]
  rw [hcoeff, hchoose, pow_add]
  field_simp [pow_ne_zero _ htwo]

/-- At a positive level, the total sinc bridge has the atlas normalization
with step `t / 2 ^ (m - 1)`. -/
theorem thueMorseBlock_cexp_eq_sincPrefix_of_pos {m : ℕ} (hm : 1 ≤ m)
    (t : ℂ) :
    ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
        Complex.exp ((t / (2 : ℂ) ^ (m - 1)) * Complex.I) ^ n =
      (-Complex.I) ^ m * t ^ m / (2 : ℂ) ^ (Nat.choose m 2) *
        Complex.exp (Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) *
        shiftedComplexSincPrefix m t := by
  simpa only [two_mul_div_two_pow hm t] using
    thueMorseBlock_cexp_eq_sincPrefix m t

/-- Away from the origin, the total sinc identity can be solved for the
finite prefix.  This is the quotient normalization printed in the atlas. -/
theorem shiftedComplexSincPrefix_eq_thueMorseBlock_cexp {m : ℕ}
    {t : ℂ} (ht : t ≠ 0) :
    shiftedComplexSincPrefix m t =
      Complex.I ^ m * (2 : ℂ) ^ (Nat.choose m 2) / t ^ m *
        Complex.exp (-Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) *
        (∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
          Complex.exp (((2 * t / (2 : ℂ) ^ m)) * Complex.I) ^ n) := by
  have h := thueMorseBlock_cexp_eq_sincPrefix m t
  have ht_pow : t ^ m ≠ 0 := pow_ne_zero _ ht
  have htwo : (2 : ℂ) ^ (Nat.choose m 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hI : Complex.I ^ m * (-Complex.I) ^ m = 1 := by
    rw [← mul_pow]
    have hmul : Complex.I * -Complex.I = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      ring
    rw [hmul, one_pow]
  have hscalar :
      (Complex.I ^ m * (2 : ℂ) ^ (Nat.choose m 2) / t ^ m) *
          ((-Complex.I) ^ m * t ^ m / (2 : ℂ) ^ (Nat.choose m 2)) = 1 := by
    calc
      _ = (Complex.I ^ m * (-Complex.I) ^ m) *
          ((2 : ℂ) ^ (Nat.choose m 2) /
            (2 : ℂ) ^ (Nat.choose m 2)) *
          (t ^ m / t ^ m) := by ring
      _ = 1 := by
        rw [hI, div_self htwo, div_self ht_pow]
        ring
  have hexp :
      Complex.exp (-Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) *
          Complex.exp (Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) = 1 := by
    calc
      _ = Complex.exp
          ((-Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) +
            Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) :=
        (Complex.exp_add _ _).symm
      _ = 1 := by
        rw [show (-Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) +
          Complex.I * t * (1 - 1 / (2 : ℂ) ^ m) = 0 by ring,
          Complex.exp_zero]
  rw [h]
  calc
    shiftedComplexSincPrefix m t =
        1 * 1 * shiftedComplexSincPrefix m t := by ring
    _ =
        ((Complex.I ^ m * (2 : ℂ) ^ (Nat.choose m 2) / t ^ m) *
          ((-Complex.I) ^ m * t ^ m / (2 : ℂ) ^ (Nat.choose m 2))) *
        (Complex.exp (-Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) *
          Complex.exp (Complex.I * t * (1 - 1 / (2 : ℂ) ^ m))) *
        shiftedComplexSincPrefix m t := by rw [hscalar, hexp]
    _ = _ := by ring

/-- The positive-level quotient normalization in the atlas scaling. -/
theorem shiftedComplexSincPrefix_eq_thueMorseBlock_cexp_of_pos {m : ℕ}
    (hm : 1 ≤ m) {t : ℂ} (ht : t ≠ 0) :
    shiftedComplexSincPrefix m t =
      Complex.I ^ m * (2 : ℂ) ^ (Nat.choose m 2) / t ^ m *
        Complex.exp (-Complex.I * t * (1 - 1 / (2 : ℂ) ^ m)) *
        (∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
          Complex.exp ((t / (2 : ℂ) ^ (m - 1)) * Complex.I) ^ n) := by
  simpa only [two_mul_div_two_pow hm t] using
    shiftedComplexSincPrefix_eq_thueMorseBlock_cexp (m := m) ht

/-! ## Total Laplace normalization -/

/-- The finite product of the removable exponential quotients appearing in
the negative-Laplace specialization. -/
noncomputable def complexLaplacePrefix (m : ℕ) (s : ℂ) : ℂ :=
  ∏ k ∈ range m,
    complexExpm1Div (-(s / (2 : ℂ) ^ (k + 1)))

/-- The empty Laplace prefix is one. -/
@[simp]
theorem complexLaplacePrefix_zero (s : ℂ) : complexLaplacePrefix 0 s = 1 := by
  simp [complexLaplacePrefix]

/-- Every finite Laplace prefix takes the normalized value one at the
removable point. -/
@[simp]
theorem complexLaplacePrefix_apply_zero (m : ℕ) :
    complexLaplacePrefix m 0 = 1 := by
  simp [complexLaplacePrefix]

/-- Appending one scale appends its removable exponential quotient. -/
theorem complexLaplacePrefix_succ (m : ℕ) (s : ℂ) :
    complexLaplacePrefix (m + 1) s =
      complexLaplacePrefix m s *
        complexExpm1Div (-(s / (2 : ℂ) ^ (m + 1))) := by
  simp [complexLaplacePrefix, Finset.prod_range_succ]

/-- Clearing the removable denominator of `complexExpm1Div (-z)` gives
`1 - exp (-z)` at every complex `z`. -/
theorem mul_complexExpm1Div_neg (z : ℂ) :
    z * complexExpm1Div (-z) = 1 - Complex.exp (-z) := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [complexExpm1Div_of_ne (neg_ne_zero.mpr hz)]
    field_simp
    ring

/-- The negative exponential quotient is a centered exponential times sinc,
including at the removable point. -/
theorem complexExpm1Div_neg_eq_exp_mul_complexSinc (z : ℂ) :
    complexExpm1Div (-z) =
      Complex.exp (-z / 2) * complexSinc (Complex.I * z / 2) := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · apply mul_left_cancel₀ hz
    rw [mul_complexExpm1Div_neg]
    have harg1 : (Complex.I * z) * Complex.I = -z := by
      calc
        _ = (Complex.I * Complex.I) * z := by ring
        _ = -z := by rw [Complex.I_mul_I]; ring
    have harg2 : ((Complex.I * z) / 2) * Complex.I = -z / 2 := by
      calc
        _ = (Complex.I * Complex.I) * z / 2 := by ring
        _ = -z / 2 := by rw [Complex.I_mul_I]; ring
    have hhalf :
        1 - Complex.exp (-z) =
          -2 * Complex.I * Complex.exp (-z / 2) *
            Complex.sin (Complex.I * z / 2) := by
      simpa only [harg1, harg2] using
        one_sub_cexp_mul_I (Complex.I * z)
    calc
      1 - Complex.exp (-z) =
          -2 * Complex.I * Complex.exp (-z / 2) *
            Complex.sin (Complex.I * z / 2) := hhalf
      _ = z *
          (Complex.exp (-z / 2) *
            complexSinc (Complex.I * z / 2)) := by
        rw [← mul_complexSinc (Complex.I * z / 2)]
        calc
          -2 * Complex.I * Complex.exp (-z / 2) *
                ((Complex.I * z / 2) *
                  complexSinc (Complex.I * z / 2)) =
              (-(Complex.I * Complex.I)) * z *
                (Complex.exp (-z / 2) *
                  complexSinc (Complex.I * z / 2)) := by
            ring
          _ = z *
                (Complex.exp (-z / 2) *
                  complexSinc (Complex.I * z / 2)) := by
            rw [Complex.I_mul_I]
            ring

/-- The finite negative-Laplace prefix is the centered sinc prefix after the
Fourier--Laplace rotation `t = i s / 2`. This is total at `s = 0`. -/
theorem complexLaplacePrefix_eq_exp_mul_shiftedComplexSincPrefix
    (m : ℕ) (s : ℂ) :
    complexLaplacePrefix m s =
      Complex.exp (-(s / 2) * (1 - 1 / (2 : ℂ) ^ m)) *
        shiftedComplexSincPrefix m (Complex.I * s / 2) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have htwo : (2 : ℂ) ≠ 0 := by norm_num
      have harg :
          Complex.I * (s / (2 : ℂ) ^ (m + 1)) / 2 =
            (Complex.I * s / 2) / (2 : ℂ) ^ (m + 1) := by
        ring
      have hphase :
          -(s / 2) * (1 - 1 / (2 : ℂ) ^ m) +
              (-(s / (2 : ℂ) ^ (m + 1)) / 2) =
            -(s / 2) * (1 - 1 / (2 : ℂ) ^ (m + 1)) := by
        simp only [pow_succ]
        field_simp [pow_ne_zero _ htwo]
        ring
      rw [complexLaplacePrefix_succ m s, ih,
        complexExpm1Div_neg_eq_exp_mul_complexSinc
          (s / (2 : ℂ) ^ (m + 1)),
        shiftedComplexSincPrefix_succ m (Complex.I * s / 2), harg]
      calc
        (Complex.exp (-(s / 2) * (1 - 1 / (2 : ℂ) ^ m)) *
              shiftedComplexSincPrefix m (Complex.I * s / 2)) *
            (Complex.exp (-(s / (2 : ℂ) ^ (m + 1)) / 2) *
              complexSinc
                ((Complex.I * s / 2) / (2 : ℂ) ^ (m + 1))) =
            Complex.exp
                (-(s / 2) * (1 - 1 / (2 : ℂ) ^ m) +
                  (-(s / (2 : ℂ) ^ (m + 1)) / 2)) *
              (shiftedComplexSincPrefix m (Complex.I * s / 2) *
                complexSinc
                  ((Complex.I * s / 2) / (2 : ℂ) ^ (m + 1))) := by
          rw [Complex.exp_add]
          ring
        _ = _ := by rw [hphase]

/-- The exact decaying finite-block identity in total Laplace form.  It is
valid for every level, including `m = 0`, and every complex `s`, including
the removable point `s = 0`. -/
theorem thueMorseBlock_exp_neg_eq_laplacePrefix (m : ℕ) (s : ℂ) :
    ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
        Complex.exp (-((n : ℂ) * s) / (2 : ℂ) ^ m) =
      s ^ m / (2 : ℂ) ^ (Nat.choose (m + 1) 2) *
        complexLaplacePrefix m s := by
  have hbase (n : ℕ) :
      Complex.exp (-s / (2 : ℂ) ^ m) ^ n =
        Complex.exp (-((n : ℂ) * s) / (2 : ℂ) ^ m) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hsum :
      (∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
          Complex.exp (-((n : ℂ) * s) / (2 : ℂ) ^ m)) =
        (∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
          Complex.exp (-s / (2 : ℂ) ^ m) ^ n) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hbase n]
  rw [hsum, ← prod_one_sub_pow_eq_sum_thueMorseSign]
  have hpow (j : ℕ) :
      Complex.exp (-s / (2 : ℂ) ^ m) ^ 2 ^ j =
        Complex.exp (-((2 : ℂ) ^ j * s / (2 : ℂ) ^ m)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    ∏ j ∈ range m,
        (1 - Complex.exp (-s / (2 : ℂ) ^ m) ^ 2 ^ j) =
        ∏ j ∈ range m,
          (1 - Complex.exp (-((2 : ℂ) ^ j * s / (2 : ℂ) ^ m))) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hpow j]
    _ = ∏ k ∈ range m,
          (1 - Complex.exp (-(s / (2 : ℂ) ^ (k + 1)))) :=
      prod_range_reflect_dyadic (fun x => 1 - Complex.exp (-x)) s m
    _ = ∏ k ∈ range m,
          ((s / (2 : ℂ) ^ (k + 1)) *
            complexExpm1Div (-(s / (2 : ℂ) ^ (k + 1)))) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [mul_complexExpm1Div_neg]
    _ = (∏ k ∈ range m, s / (2 : ℂ) ^ (k + 1)) *
          complexLaplacePrefix m s := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = s ^ m / (2 : ℂ) ^ (Nat.choose (m + 1) 2) *
          complexLaplacePrefix m s := by
      congr 1
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
        prod_range_pow_succ_eq_pow_choose_two]

/-- Away from zero, the total Laplace bridge can be solved for its removable
prefix. -/
theorem complexLaplacePrefix_eq_thueMorseBlock_exp_neg {m : ℕ} {s : ℂ}
    (hs : s ≠ 0) :
    complexLaplacePrefix m s =
      (2 : ℂ) ^ (Nat.choose (m + 1) 2) / s ^ m *
        (∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
          Complex.exp (-((n : ℂ) * s) / (2 : ℂ) ^ m)) := by
  rw [thueMorseBlock_exp_neg_eq_laplacePrefix]
  have hs_pow : s ^ m ≠ 0 := pow_ne_zero _ hs
  have htwo : (2 : ℂ) ^ (Nat.choose (m + 1) 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  field_simp

end Fabius
