import FabiusFunction.QBinomialCauchy
import FabiusFunction.GaussianBinomialInteger

/-!
# The `q`-Pfaff–Saalschütz summation

The terminating balanced `₃φ₂` sum

`∑_{k=0}^{n} (a;q)_k (b;q)_k (q^{-n};q)_k / ((q;q)_k (c;q)_k (abq^{1-n}/c;q)_k) q^k
  = (c/a;q)_n (c/b;q)_n / ((c;q)_n (c/(ab);q)_n)`

is a purely algebraic consequence of the second finite Cauchy identity
`(ac;q)_n (bc;q)_n = ∑_k [n,k]_q (a;q)_k (b;q)_k c^k (c;q)_{n-k} (abcq^k;q)_{n-k}` at
`c ↦ c/(ab)`: after dividing by `(c;q)_n (c/(ab);q)_n`, the `k`-th summand is identified with
the `k`-th term of the `₃φ₂` by the tail identities `(c;q)_n = (c;q)_k (cq^k;q)_{n-k}`,
`(c/(ab);q)_n = (c/(ab);q)_{n-k} (cq^{n-k}/(ab);q)_k`, the terminating numerator
`q^{nk} (q^{-n};q)_k = (-1)^k q^{C(k,2)} (q^{n-k+1};q)_k`, and base reversal of
`(abq^{1-n}/c;q)_k`.  No convergence or limiting argument enters, so the identity holds in
every field, at every `q ≠ 0`, whenever the displayed denominators are nonzero.

Here `q^{-n}` is written `(q^n)⁻¹` and `abq^{1-n}/c` is written `abq/(cq^n)`.

## Main declarations

* `finiteQPochhammerIn_ne_zero_of_le`: nonvanishing passes to shorter symbols.
* `q_pfaff_saalschutz`: the summation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

variable {K : Type*} [Field K] {q : K}

/-- If `(a;q)_n ≠ 0` then `(a;q)_m ≠ 0` for every `m ≤ n`. -/
theorem finiteQPochhammerIn_ne_zero_of_le (a : K) {m n : ℕ} (h : m ≤ n)
    (hn : finiteQPochhammerIn a q n ≠ 0) : finiteQPochhammerIn a q m ≠ 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [finiteQPochhammerIn_add] at hn
  exact left_ne_zero_of_mul hn

/-- The `k`-th term of the balanced terminating `₃φ₂`, identified with the `k`-th summand of the
second finite Cauchy identity at `c ↦ c/(ab)`, divided by `(c;q)_n (c/(ab);q)_n`. -/
theorem q_pfaff_saalschutz_term (hq0 : q ≠ 0) {n : ℕ} {a b c : K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) (hqn : finiteQPochhammerIn q q n ≠ 0) (hc : finiteQPochhammerIn c q n ≠ 0)
    (hd : finiteQPochhammerIn (a * b * q / (c * q ^ n)) q n ≠ 0)
    (hcab : finiteQPochhammerIn (c / (a * b)) q n ≠ 0) {k : ℕ} (hk : k ≤ n) :
    finiteQPochhammerIn a q k * finiteQPochhammerIn b q k * finiteQPochhammerIn (q ^ n)⁻¹ q k /
        (finiteQPochhammerIn q q k * finiteQPochhammerIn c q k *
          finiteQPochhammerIn (a * b * q / (c * q ^ n)) q k) * q ^ k =
      gaussianBinomial q n k * finiteQPochhammerIn a q k * finiteQPochhammerIn b q k *
          (c / (a * b)) ^ k * finiteQPochhammerIn (c / (a * b)) q (n - k) *
          finiteQPochhammerIn (c * q ^ k) q (n - k) /
        (finiteQPochhammerIn c q n * finiteQPochhammerIn (c / (a * b)) q n) := by
  have hcsplit : finiteQPochhammerIn c q n =
      finiteQPochhammerIn c q k * finiteQPochhammerIn (c * q ^ k) q (n - k) := by
    rw [← finiteQPochhammerIn_add, Nat.add_sub_cancel' hk]
  have hesplit : finiteQPochhammerIn (c / (a * b)) q n =
      finiteQPochhammerIn (c / (a * b)) q (n - k) *
        finiteQPochhammerIn (c / (a * b) * q ^ (n - k)) q k := by
    rw [← finiteQPochhammerIn_add, Nat.sub_add_cancel hk]
  have hqk : finiteQPochhammerIn q q k ≠ 0 := finiteQPochhammerIn_ne_zero_of_le q hk hqn
  have hck : finiteQPochhammerIn c q k ≠ 0 := finiteQPochhammerIn_ne_zero_of_le c hk hc
  have hdk : finiteQPochhammerIn (a * b * q / (c * q ^ n)) q k ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_le _ hk hd
  have hck' : finiteQPochhammerIn (c * q ^ k) q (n - k) ≠ 0 := by
    rw [hcsplit] at hc; exact right_ne_zero_of_mul hc
  have hek : finiteQPochhammerIn (c / (a * b)) q (n - k) ≠ 0 := by
    rw [hesplit] at hcab; exact left_ne_zero_of_mul hcab
  have hek' : finiteQPochhammerIn (c / (a * b) * q ^ (n - k)) q k ≠ 0 := by
    rw [hesplit] at hcab; exact right_ne_zero_of_mul hcab
  have he0 : c / (a * b) ≠ 0 := div_ne_zero hc0 (mul_ne_zero ha0 hb0)
  have hd0 : a * b * q / (c * q ^ n) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hq0) (mul_ne_zero hc0 (pow_ne_zero _ hq0))
  have hG : gaussianBinomial q n k =
      finiteQPochhammerIn (q ^ (n - k + 1)) q k / finiteQPochhammerIn q q k := by
    rw [eq_div_iff hqk, mul_comm, finiteQPochhammerIn_self_mul_gaussianBinomial q hk]
  have hnum : finiteQPochhammerIn (q ^ n)⁻¹ q k =
      (-1) ^ k * q ^ k.choose 2 * finiteQPochhammerIn (q ^ (n - k + 1)) q k / q ^ (n * k) := by
    rw [eq_div_iff (pow_ne_zero _ hq0), mul_comm, pow_mul_finiteQPochhammerIn_inv_pow_eq q hq0 hk]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [finiteQPochhammerIn_zero, gaussianBinomial_zero_right, pow_zero, one_mul, mul_one,
      div_one, Nat.sub_zero]
    rw [mul_comm (finiteQPochhammerIn (c / (a * b)) q n), div_self (mul_ne_zero hc hcab)]
  have h1 : q ^ n = q ^ (n - k) * (q * q ^ (k - 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel hkpos, ← pow_add, Nat.sub_add_cancel hk]
  have hdinv : (a * b * q / (c * q ^ n))⁻¹ * q⁻¹ ^ (k - 1) = c / (a * b) * q ^ (n - k) := by
    rw [inv_div, inv_pow, h1]
    field_simp
    all_goals ring
  have hdpow : (a * b * q / (c * q ^ n)) ^ k = q ^ k / (q ^ (n * k) * (c / (a * b)) ^ k) := by
    rw [show a * b * q / (c * q ^ n) = q / (q ^ n * (c / (a * b))) by
        field_simp
        all_goals ring,
      div_pow, mul_pow, ← pow_mul]
  rw [finiteQPochhammerIn_base_reversal _ q hd0 hq0 k, finiteQPochhammerIn_inv_base_eq hq0, hdinv,
    hcsplit, hesplit, hG, hnum, neg_pow (a * b * q / (c * q ^ n)) k, hdpow]
  set Ek := finiteQPochhammerIn (c / (a * b) * q ^ (n - k)) q k with hEk
  set E := finiteQPochhammerIn (c / (a * b)) q (n - k) with hE
  set N := finiteQPochhammerIn (q ^ (n - k + 1)) q k with hN
  set Ck := finiteQPochhammerIn (c * q ^ k) q (n - k) with hCk
  set ek := (c / (a * b)) ^ k with hek_def
  set s := (-1 : K) ^ k with hs
  set qC := q ^ k.choose 2 with hqC
  set qn := q ^ (n * k) with hqn
  set qk := q ^ k with hqk_def
  have hs0 : s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hqC0 : qC ≠ 0 := pow_ne_zero _ hq0
  have hqk0 : qk ≠ 0 := pow_ne_zero _ hq0
  have hqn0 : qn ≠ 0 := pow_ne_zero _ hq0
  have hek0 : ek ≠ 0 := pow_ne_zero _ he0
  field_simp
  all_goals ring

/-- **The `q`-Pfaff–Saalschütz summation**: for `q ≠ 0` and nonzero `a, b, c` with
`(q;q)_n`, `(c;q)_n`, `(abq^{1-n}/c;q)_n`, `(c/(ab);q)_n` nonzero,

`∑_{k≤n} (a;q)_k (b;q)_k (q^{-n};q)_k / ((q;q)_k (c;q)_k (abq^{1-n}/c;q)_k) q^k
  = (c/a;q)_n (c/b;q)_n / ((c;q)_n (c/(ab);q)_n)`. -/
theorem q_pfaff_saalschutz (hq0 : q ≠ 0) (n : ℕ) {a b c : K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) (hqn : finiteQPochhammerIn q q n ≠ 0) (hc : finiteQPochhammerIn c q n ≠ 0)
    (hd : finiteQPochhammerIn (a * b * q / (c * q ^ n)) q n ≠ 0)
    (hcab : finiteQPochhammerIn (c / (a * b)) q n ≠ 0) :
    ∑ k ∈ range (n + 1),
        finiteQPochhammerIn a q k * finiteQPochhammerIn b q k *
            finiteQPochhammerIn (q ^ n)⁻¹ q k /
          (finiteQPochhammerIn q q k * finiteQPochhammerIn c q k *
            finiteQPochhammerIn (a * b * q / (c * q ^ n)) q k) * q ^ k =
      finiteQPochhammerIn (c / a) q n * finiteQPochhammerIn (c / b) q n /
        (finiteQPochhammerIn c q n * finiteQPochhammerIn (c / (a * b)) q n) := by
  have hC := finite_qCauchy_second_identity q a b (c / (a * b)) n
  rw [show a * (c / (a * b)) = c / b by rw [mul_div_assoc', mul_div_mul_left c b ha0],
    show b * (c / (a * b)) = c / a by rw [mul_div_assoc', mul_comm a b, mul_div_mul_left c a hb0],
    show a * b * (c / (a * b)) = c by
      rw [mul_div_assoc', mul_div_cancel_left₀ c (mul_ne_zero ha0 hb0)]] at hC
  rw [sum_congr rfl fun k hk =>
      q_pfaff_saalschutz_term hq0 ha0 hb0 hc0 hqn hc hd hcab (Nat.lt_succ_iff.mp (mem_range.mp hk)),
    ← sum_div, ← hC, mul_comm (finiteQPochhammerIn (c / b) q n)]

end Fabius
