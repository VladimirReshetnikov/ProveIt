import FabiusFunction.DyadicClosedForm
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer

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

/-- Thue--Morse signs annihilate every rational polynomial of degree below the
dyadic block exponent. -/
lemma thueMorse_polynomial_sum_eq_zero (r : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree < r) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) * p.eval (h.val : ℚ)) = 0 := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro d hd
  have hdle : d ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp d hd
  have hdr : d < r := hdle.trans_lt hp
  have hzero := thueMorse_affine_power_sum_eq_zero r d hdr (0 : ℚ) 1
  simp only [zero_add, one_mul] at hzero
  calc
    (∑ h : Fin (2 ^ r),
        (thueMorseSign h.val : ℚ) * (p.coeff d * (h.val : ℚ) ^ d)) =
        p.coeff d *
          ∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℚ) * (h.val : ℚ) ^ d := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro h hh
            ring
    _ = 0 := by rw [hzero, mul_zero]

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
