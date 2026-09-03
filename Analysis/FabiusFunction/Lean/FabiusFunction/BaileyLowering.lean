import FabiusFunction.BaileyPairs

/-!
# The parameter-lowering shift of Bailey pairs

If `(α, β)` is a Bailey pair relative to `a` (with `(a;q)_m ≠ 0` for all `m`), then

  `α^{BL}_0 = α_0`,  `α^{BL}_n = (1 - a) (α_n/(1 - aq^{2n}) - aq^{2n-2} α_{n-1}/(1 - aq^{2n-2}))`
  (`n ≥ 1`),  `β^{BL}_n = β_n`

is a Bailey pair relative to `a/q` (`isBaileyPair_baileyLowered`, qg:lem-bailey-lowering).
The kernel relative to `a/q` is `1/((q;q)_{n-j} (a;q)_{n+j})`; substituting and collecting the
coefficient of `α_r` gives
`(1-a)/(1-aq^{2r}) · [1/((q;q)_{n-r}(a;q)_{n+r}) - aq^{2r}/((q;q)_{n-r-1}(a;q)_{n+r+1})]`
(second term absent for `r = n`), whose numerator over the common denominator
`(q;q)_{n-r}(a;q)_{n+r+1}(1-aq^{2r})` is `(1-a)[(1-aq^{n+r}) - aq^{2r}(1-q^{n-r})] = (1-a)(1-aq^{2r})`;
after cancellation this is the original kernel `1/((q;q)_{n-r}(aq;q)_{n+r})`
(`baileyLowered_coeff_lt`, `baileyLowered_coeff_eq`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {K : Type*} [Field K]

/-- The lowered `α`-sequence. -/
def baileyLowered (a q : K) (α : ℕ → K) : ℕ → K
  | 0 => α 0
  | n + 1 => (1 - a) * (α (n + 1) / (1 - a * q ^ (2 * (n + 1))) -
      a * q ^ (2 * n) * α n / (1 - a * q ^ (2 * n)))

/-- `(1 - a) (aq;q)_m = (a;q)_{m+1}`. -/
theorem finiteQPochhammerIn_shift_mul (a q : K) (m : ℕ) :
    (1 - a) * finiteQPochhammerIn (a * q) q m = finiteQPochhammerIn a q (m + 1) :=
  (finiteQPochhammerIn_succ_shift a q m).symm

/-- The coefficient identity for `r < n`. -/
theorem baileyLowered_coeff_lt {a q : K} (hq : ∀ m, finiteQPochhammerIn q q m ≠ 0)
    (ha : ∀ m, finiteQPochhammerIn a q m ≠ 0) {n r : ℕ} (hr : r < n) :
    (1 - a) / (1 - a * q ^ (2 * r)) /
        (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn a q (n + r)) -
      (1 - a) * (a * q ^ (2 * r)) / (1 - a * q ^ (2 * r)) /
        (finiteQPochhammerIn q q (n - (r + 1)) * finiteQPochhammerIn a q (n + (r + 1))) =
      1 / (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (a * q) q (n + r)) := by
  have h2r : (1 : K) - a * q ^ (2 * r) ≠ 0 := by
    intro h0
    apply ha (2 * r + 1)
    rw [finiteQPochhammerIn_succ, h0, mul_zero]
  have h1a : (1 : K) - a ≠ 0 := by
    intro h0
    apply ha 1
    rw [finiteQPochhammerIn_succ, pow_zero, mul_one, h0, mul_zero]
  have hnr : n - r = (n - (r + 1)) + 1 := by omega
  have hqq : finiteQPochhammerIn q q (n - r) =
      finiteQPochhammerIn q q (n - (r + 1)) * (1 - q ^ (n - r)) := by
    rw [hnr, finiteQPochhammerIn_succ, ← pow_succ']
  have haa : finiteQPochhammerIn a q (n + (r + 1)) =
      finiteQPochhammerIn a q (n + r) * (1 - a * q ^ (n + r)) := by
    rw [show n + (r + 1) = (n + r) + 1 by ring, finiteQPochhammerIn_succ]
  have hshift : (1 - a) * finiteQPochhammerIn (a * q) q (n + r) =
      finiteQPochhammerIn a q (n + r) * (1 - a * q ^ (n + r)) := by
    rw [finiteQPochhammerIn_shift_mul, finiteQPochhammerIn_succ]
  have hpow : q ^ (2 * r) * q ^ (n - r) = q ^ (n + r) := by
    rw [← pow_add]
    congr 1
    omega
  have hA := hq (n - (r + 1))
  have hB := ha (n + r)
  have hC : (1 : K) - a * q ^ (n + r) ≠ 0 := by
    intro h0
    apply ha (n + r + 1)
    rw [finiteQPochhammerIn_succ, h0, mul_zero]
  have hD : (1 : K) - q ^ (n - r) ≠ 0 := by
    intro h0
    apply hq (n - r)
    rw [hqq, h0, mul_zero]
  have hE : finiteQPochhammerIn (a * q) q (n + r) ≠ 0 := by
    intro h0
    apply ha (n + r + 1)
    rw [← finiteQPochhammerIn_shift_mul, h0, mul_zero]
  have hinv : (1 - a * q ^ (2 * r))⁻¹ * (1 - a * q ^ (2 * r)) = 1 := inv_mul_cancel₀ h2r
  rw [hqq, haa, div_sub_div _ _ (mul_ne_zero (mul_ne_zero hA hD) hB) (mul_ne_zero hA (mul_ne_zero hB hC)),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hD) hB) (mul_ne_zero hA (mul_ne_zero hB hC)))
      (mul_ne_zero (mul_ne_zero hA hD) hE)]
  linear_combination
    (finiteQPochhammerIn q q (n - (r + 1)) * finiteQPochhammerIn q q (n - (r + 1)) *
      finiteQPochhammerIn a q (n + r) * (1 - q ^ (n - r))) * hshift +
    ((1 - a) * finiteQPochhammerIn q q (n - (r + 1)) * finiteQPochhammerIn a q (n + r) *
      (finiteQPochhammerIn q q (n - (r + 1)) * (1 - q ^ (n - r)) *
        finiteQPochhammerIn (a * q) q (n + r))) * hinv +
    ((1 - a * q ^ (2 * r))⁻¹ * (1 - a) * finiteQPochhammerIn q q (n - (r + 1)) *
      finiteQPochhammerIn a q (n + r) * a *
      (finiteQPochhammerIn q q (n - (r + 1)) * (1 - q ^ (n - r)) *
        finiteQPochhammerIn (a * q) q (n + r))) * hpow

/-- The coefficient identity for `r = n`. -/
theorem baileyLowered_coeff_eq {a q : K} (ha : ∀ m, finiteQPochhammerIn a q m ≠ 0) (n : ℕ) :
    (1 - a) / (1 - a * q ^ (2 * n)) /
        (finiteQPochhammerIn q q (n - n) * finiteQPochhammerIn a q (n + n)) =
      1 / (finiteQPochhammerIn q q (n - n) * finiteQPochhammerIn (a * q) q (n + n)) := by
  have h2n : (1 : K) - a * q ^ (2 * n) ≠ 0 := by
    intro h0
    apply ha (2 * n + 1)
    rw [finiteQPochhammerIn_succ, h0, mul_zero]
  have hE : finiteQPochhammerIn (a * q) q (n + n) ≠ 0 := by
    intro h0
    apply ha (n + n + 1)
    rw [← finiteQPochhammerIn_shift_mul, h0, mul_zero]
  have hkey : (1 - a) * finiteQPochhammerIn (a * q) q (n + n) =
      finiteQPochhammerIn a q (n + n) * (1 - a * q ^ (2 * n)) := by
    rw [finiteQPochhammerIn_shift_mul, finiteQPochhammerIn_succ, ← two_mul]
  have h0 : finiteQPochhammerIn q q 0 = 1 := by simp [finiteQPochhammerIn]
  rw [Nat.sub_self, h0, one_mul, one_mul, div_div,
    div_eq_div_iff (mul_ne_zero h2n (ha (n + n))) hE]
  linear_combination hkey

/-- **The parameter-lowering shift** (qg:lem-bailey-lowering): if `(α, β)` is a Bailey pair
relative to `a`, then `(baileyLowered a q α, β)` is a Bailey pair relative to `a/q`. -/
theorem isBaileyPair_baileyLowered {a q : K} {α β : ℕ → K} (h : IsBaileyPair a q α β)
    (hq0 : q ≠ 0) (hq : ∀ m, finiteQPochhammerIn q q m ≠ 0)
    (ha : ∀ m, finiteQPochhammerIn a q m ≠ 0) :
    IsBaileyPair (a / q) q (baileyLowered a q α) β := by
  intro n
  simp only [div_mul_cancel₀ a hq0]
  rw [h n]
  cases n with
  | zero => simp [baileyLowered, finiteQPochhammerIn]
  | succ m =>
      have h1a : (1 : K) - a ≠ 0 := by
        intro h0
        apply ha 1
        rw [finiteQPochhammerIn_succ, pow_zero, mul_one, h0, mul_zero]
      -- the right side: `j = 0` and `j = i + 1`, the latter split into its two terms
      rw [sum_range_succ' (fun j => baileyLowered a q α j /
        (finiteQPochhammerIn q q (m + 1 - j) * finiteQPochhammerIn a q (m + 1 + j)))]
      simp only [baileyLowered]
      rw [sum_congr rfl (fun i _ => show (1 - a) * (α (i + 1) / (1 - a * q ^ (2 * (i + 1))) -
            a * q ^ (2 * i) * α i / (1 - a * q ^ (2 * i))) /
          (finiteQPochhammerIn q q (m + 1 - (i + 1)) * finiteQPochhammerIn a q (m + 1 + (i + 1))) =
          (1 - a) / (1 - a * q ^ (2 * (i + 1))) /
              (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
                finiteQPochhammerIn a q (m + 1 + (i + 1))) * α (i + 1) -
            (1 - a) * (a * q ^ (2 * i)) / (1 - a * q ^ (2 * i)) /
              (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
                finiteQPochhammerIn a q (m + 1 + (i + 1))) * α i by ring),
        sum_sub_distrib, sum_range_succ (fun i => (1 - a) / (1 - a * q ^ (2 * (i + 1))) /
          (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
            finiteQPochhammerIn a q (m + 1 + (i + 1))) * α (i + 1)),
        sum_range_succ' (fun i => (1 - a) * (a * q ^ (2 * i)) / (1 - a * q ^ (2 * i)) /
          (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
            finiteQPochhammerIn a q (m + 1 + (i + 1))) * α i)]
      -- the left side: `r = 0`, `r = i + 1 < m + 1`, `r = m + 1`
      rw [sum_range_succ' (fun r => α r /
        (finiteQPochhammerIn q q (m + 1 - r) * finiteQPochhammerIn (a * q) q (m + 1 + r))),
        sum_range_succ (fun i => α (i + 1) /
          (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
            finiteQPochhammerIn (a * q) q (m + 1 + (i + 1))))]
      have hsum : ∑ i ∈ range m, (1 - a) / (1 - a * q ^ (2 * (i + 1))) /
            (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
              finiteQPochhammerIn a q (m + 1 + (i + 1))) * α (i + 1) -
          ∑ i ∈ range m, (1 - a) * (a * q ^ (2 * (i + 1))) / (1 - a * q ^ (2 * (i + 1))) /
            (finiteQPochhammerIn q q (m + 1 - (i + 1 + 1)) *
              finiteQPochhammerIn a q (m + 1 + (i + 1 + 1))) * α (i + 1) =
          ∑ i ∈ range m, α (i + 1) /
            (finiteQPochhammerIn q q (m + 1 - (i + 1)) *
              finiteQPochhammerIn (a * q) q (m + 1 + (i + 1))) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun i hi => ?_
        have hL := baileyLowered_coeff_lt hq ha (show i + 1 < m + 1 by
          have := mem_range.mp hi; omega)
        linear_combination (α (i + 1)) * hL
      have hm : (1 - a) / (1 - a * q ^ (2 * (m + 1))) /
            (finiteQPochhammerIn q q (m + 1 - (m + 1)) *
              finiteQPochhammerIn a q (m + 1 + (m + 1))) * α (m + 1) =
          α (m + 1) / (finiteQPochhammerIn q q (m + 1 - (m + 1)) *
            finiteQPochhammerIn (a * q) q (m + 1 + (m + 1))) := by
        linear_combination (α (m + 1)) * baileyLowered_coeff_eq ha (m + 1)
      have hzero : α 0 / (finiteQPochhammerIn q q (m + 1 - 0) * finiteQPochhammerIn a q (m + 1 + 0)) -
          (1 - a) * (a * q ^ (2 * 0)) / (1 - a * q ^ (2 * 0)) /
            (finiteQPochhammerIn q q (m + 1 - (0 + 1)) * finiteQPochhammerIn a q (m + 1 + (0 + 1))) *
              α 0 =
          α 0 / (finiteQPochhammerIn q q (m + 1 - 0) * finiteQPochhammerIn (a * q) q (m + 1 + 0)) := by
        have hL := baileyLowered_coeff_lt hq ha (show 0 < m + 1 by omega) (a := a) (q := q)
        have hone : (1 - a) / (1 - a * q ^ (2 * 0)) = 1 := by
          rw [mul_zero, pow_zero, mul_one, div_self h1a]
        linear_combination (α 0) * hL - (α 0 /
          (finiteQPochhammerIn q q (m + 1 - 0) * finiteQPochhammerIn a q (m + 1 + 0))) * hone
      linear_combination -hsum - hm - hzero

end Fabius
