import FabiusFunction.ThueMorsePrefix
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The finite Wolfram-language `QPochhammer[a,q,n]`, over `ℚ`. -/
noncomputable def finiteQPochhammer (a q : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, (1 - a * q ^ j)

@[simp] theorem finiteQPochhammer_zero (a q : ℚ) :
    finiteQPochhammer a q 0 = 1 := by
  simp [finiteQPochhammer]

theorem finiteQPochhammer_succ (a q : ℚ) (n : ℕ) :
    finiteQPochhammer a q (n + 1) =
      finiteQPochhammer a q n * (1 - a * q ^ n) := by
  simp [finiteQPochhammer, Finset.prod_range_succ]

/-- Public notation-faithful alias for Wolfram Language's finite
`QPochhammer[a,q,n]`. -/
noncomputable abbrev qPochhammer := finiteQPochhammer

@[simp] theorem qPochhammer_zero (a q : ℚ) : qPochhammer a q 0 = 1 := by
  exact finiteQPochhammer_zero a q

theorem qPochhammer_succ (a q : ℚ) (n : ℕ) :
    qPochhammer a q (n + 1) =
      qPochhammer a q n * (1 - a * q ^ n) :=
  finiteQPochhammer_succ a q n

/-- The specialization `QPochhammer[1/2,1/2,n]`. -/
noncomputable def halfQPochhammer (n : ℕ) : ℚ :=
  finiteQPochhammer (1 / 2) (1 / 2) n

@[simp] theorem qPochhammer_half_eq (n : ℕ) :
    qPochhammer (1 / 2) (1 / 2) n = halfQPochhammer n := by
  rfl

@[simp] theorem halfQPochhammer_zero : halfQPochhammer 0 = 1 := by
  simp [halfQPochhammer]

theorem halfQPochhammer_succ (n : ℕ) :
    halfQPochhammer (n + 1) =
      halfQPochhammer n * (1 - (1 / 2 : ℚ) ^ (n + 1)) := by
  rw [halfQPochhammer, finiteQPochhammer_succ]
  congr 2
  rw [pow_succ]
  ring

theorem halfQPochhammer_pos (n : ℕ) : 0 < halfQPochhammer n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [halfQPochhammer_succ]
      apply mul_pos ih
      have hpow : (1 / 2 : ℚ) ^ (n + 1) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith

theorem halfQPochhammer_ne_zero (n : ℕ) : halfQPochhammer n ≠ 0 :=
  (halfQPochhammer_pos n).ne'

/-- Product of the Mersenne factors `2^j - 1`, for `1 ≤ j ≤ n`. -/
noncomputable def halfMersenneProduct (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, ((2 : ℚ) ^ (j + 1) - 1)

@[simp] theorem halfMersenneProduct_zero : halfMersenneProduct 0 = 1 := by
  simp [halfMersenneProduct]

theorem halfMersenneProduct_succ (n : ℕ) :
    halfMersenneProduct (n + 1) =
      halfMersenneProduct n * ((2 : ℚ) ^ (n + 1) - 1) := by
  simp [halfMersenneProduct, Finset.prod_range_succ]

theorem halfMersenneProduct_pos (n : ℕ) : 0 < halfMersenneProduct n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [halfMersenneProduct_succ]
      exact mul_pos ih (by
        have : (1 : ℚ) < 2 ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
        linarith)

theorem halfMersenneProduct_ne_zero (n : ℕ) : halfMersenneProduct n ≠ 0 :=
  (halfMersenneProduct_pos n).ne'

private theorem half_factor_eq (m : ℕ) :
    1 - (1 / 2 : ℚ) ^ m = ((2 : ℚ) ^ m - 1) / (2 : ℚ) ^ m := by
  rw [div_pow]
  simp only [one_pow]
  field_simp

private theorem choose_succ_two' (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  rw [show n + 1 = Nat.succ n by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

/-- The exact denominator normalization of `(1/2;1/2)_n`. -/
theorem halfQPochhammer_eq_mersenne_div (n : ℕ) :
    halfQPochhammer n =
      halfMersenneProduct n / (2 : ℚ) ^ ((n + 1).choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        simpa only [Nat.succ_eq_add_one] using choose_succ_two' (n + 1)
      rw [halfQPochhammer_succ, halfMersenneProduct_succ, ih,
        half_factor_eq, hchoose, pow_add]
      ring

private theorem square_eq_choose_sum (n : ℕ) :
    n * n = (n + 1).choose 2 + n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htop : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        simpa only [Nat.succ_eq_add_one] using choose_succ_two' (n + 1)
      have hbottom : (n + 1).choose 2 = n.choose 2 + n := choose_succ_two' n
      rw [htop, hbottom]
      nlinarith

/-- The full prefactor denominator in the requested formula has no hidden
division: `2^(n^2) (1/2;1/2)_n = 2^(choose n 2) ∏_{j=1}^n (2^j-1)`. -/
theorem two_pow_sq_mul_halfQPochhammer (n : ℕ) :
    (2 : ℚ) ^ (n * n) * halfQPochhammer n =
      (2 : ℚ) ^ (n.choose 2) * halfMersenneProduct n := by
  rw [halfQPochhammer_eq_mersenne_div, square_eq_choose_sum, pow_add]
  field_simp

/-- The same normalization, with the Wolfram expression `n^2` transcribed
literally as a natural-number square. -/
theorem two_pow_nat_sq_mul_halfQPochhammer (n : ℕ) :
    (2 : ℚ) ^ (n ^ 2) * halfQPochhammer n =
      (2 : ℚ) ^ (n.choose 2) * halfMersenneProduct n := by
  simpa [pow_two] using two_pow_sq_mul_halfQPochhammer n

/-- Normalization of the reciprocal prefactor in the requested formula. -/
theorem one_div_two_pow_nat_sq_mul_halfQPochhammer (n : ℕ) :
    1 / ((2 : ℚ) ^ (n ^ 2) * halfQPochhammer n) =
      1 / ((2 : ℚ) ^ (n.choose 2) * halfMersenneProduct n) := by
  rw [two_pow_nat_sq_mul_halfQPochhammer]

/-- The Wolfram denominator `4^Binomial[k,2]` as a pure power of two. -/
theorem four_pow_choose_two (k : ℕ) :
    (4 : ℚ) ^ (k.choose 2) = (2 : ℚ) ^ (k * (k - 1)) := by
  have htwo : 2 * k.choose 2 = k * (k - 1) := by
    cases k with
    | zero => simp
    | succ k =>
        simpa [mul_comm] using two_mul_choose_succ_two k
  calc
    (4 : ℚ) ^ (k.choose 2) = ((2 : ℚ) ^ 2) ^ (k.choose 2) := by norm_num
    _ = (2 : ℚ) ^ (2 * k.choose 2) := by rw [pow_mul]
    _ = (2 : ℚ) ^ (k * (k - 1)) := by rw [htwo]

/-- `QBinomial[n,k,1/2]`, extended by zero for `k > n`. -/
noncomputable def halfQBinomial (n k : ℕ) : ℚ :=
  if k ≤ n then
    halfQPochhammer n /
      (halfQPochhammer k * halfQPochhammer (n - k))
  else 0

/-- The q-Pochhammer quotient presentation of Wolfram Language's
`QBinomial[n,k,q]` over `ℚ`, extended by zero when `k > n`.  This agrees with
the polynomial continuation whenever the denominator is nonzero; in
particular, it is exact at the specialization `q = 1/2` used below. -/
noncomputable def qBinomial (n k : ℕ) (q : ℚ) : ℚ :=
  if k ≤ n then
    qPochhammer q q n /
      (qPochhammer q q k * qPochhammer q q (n - k))
  else 0

theorem qBinomial_half_eq (n k : ℕ) :
    qBinomial n k (1 / 2) = halfQBinomial n k := by
  rfl

theorem qBinomial_eq_zero_of_lt (q : ℚ) {n k : ℕ} (hk : n < k) :
    qBinomial n k q = 0 := by
  simp [qBinomial, Nat.not_le.mpr hk]

theorem halfQBinomial_eq_quotient {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k =
      halfQPochhammer n /
        (halfQPochhammer k * halfQPochhammer (n - k)) := by
  simp [halfQBinomial, hk]

theorem halfQBinomial_eq_zero_of_lt {n k : ℕ} (hk : n < k) :
    halfQBinomial n k = 0 := by
  simp [halfQBinomial, Nat.not_le.mpr hk]

@[simp] theorem halfQBinomial_zero_right (n : ℕ) :
    halfQBinomial n 0 = 1 := by
  rw [halfQBinomial_eq_quotient (Nat.zero_le n)]
  simp [halfQPochhammer_ne_zero]

@[simp] theorem halfQBinomial_self (n : ℕ) :
    halfQBinomial n n = 1 := by
  rw [halfQBinomial_eq_quotient (le_refl n)]
  simp [halfQPochhammer_ne_zero]

@[simp] theorem halfQBinomial_zero_zero : halfQBinomial 0 0 = 1 := by simp

@[simp] theorem halfQBinomial_zero_succ (k : ℕ) :
    halfQBinomial 0 (k + 1) = 0 := by
  exact halfQBinomial_eq_zero_of_lt (by omega)

theorem halfQBinomial_pos {n k : ℕ} (hk : k ≤ n) :
    0 < halfQBinomial n k := by
  rw [halfQBinomial_eq_quotient hk]
  exact div_pos (halfQPochhammer_pos n)
    (mul_pos (halfQPochhammer_pos k) (halfQPochhammer_pos (n - k)))

theorem halfQBinomial_ne_zero {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k ≠ 0 := (halfQBinomial_pos hk).ne'

theorem halfQBinomial_eq_zero_iff {n k : ℕ} :
    halfQBinomial n k = 0 ↔ n < k := by
  constructor
  · intro h
    by_contra hnot
    exact (halfQBinomial_ne_zero (Nat.le_of_not_gt hnot)) h
  · exact halfQBinomial_eq_zero_of_lt

private theorem choose_split (n k : ℕ) (hk : k ≤ n) :
    (n + 1).choose 2 =
      (k + 1).choose 2 + k * (n - k) + (n - k + 1).choose 2 := by
  have h := choose_add_succ_two k (n - k)
  rw [Nat.add_sub_of_le hk] at h
  exact h

/-- Mersenne-product normalization of the Gaussian coefficient at `q=1/2`. -/
theorem halfQBinomial_eq_mersenne {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n k =
      halfMersenneProduct n /
        (halfMersenneProduct k * halfMersenneProduct (n - k) *
          (2 : ℚ) ^ (k * (n - k))) := by
  rw [halfQBinomial_eq_quotient hk]
  simp_rw [halfQPochhammer_eq_mersenne_div]
  rw [choose_split n k hk, pow_add, pow_add]
  field_simp [halfMersenneProduct_ne_zero]

theorem halfQBinomial_symm {n k : ℕ} (hk : k ≤ n) :
    halfQBinomial n (n - k) = halfQBinomial n k := by
  rw [halfQBinomial_eq_quotient (Nat.sub_le n k),
    halfQBinomial_eq_quotient hk]
  rw [Nat.sub_sub_self hk]
  ring

/-- The q-Pascal recurrence, in the orientation suited to the finite
q-binomial theorem. -/
theorem halfQBinomial_succ_succ (n k : ℕ) :
    halfQBinomial (n + 1) (k + 1) =
      halfQBinomial n k +
        (1 / 2 : ℚ) ^ (k + 1) * halfQBinomial n (k + 1) := by
  by_cases hkn : k < n
  · have hk1n1 : k + 1 ≤ n + 1 := by omega
    have hknle : k ≤ n := hkn.le
    have hk1n : k + 1 ≤ n := hkn
    rw [halfQBinomial_eq_quotient hk1n1,
      halfQBinomial_eq_quotient hknle,
      halfQBinomial_eq_quotient hk1n]
    have hsub : n - k = (n - (k + 1)) + 1 := by omega
    have hpow : (1 / 2 : ℚ) ^ (n + 1) =
        (1 / 2 : ℚ) ^ (k + 1) * (1 / 2 : ℚ) ^ (n - k) := by
      rw [← pow_add]
      congr 1
      omega
    have hkfactor : 1 - (1 / 2 : ℚ) ^ (k + 1) ≠ 0 := by
      have hlt := pow_lt_one₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)
        (by omega : k + 1 ≠ 0)
      linarith
    have hnfactor : 1 - (1 / 2 : ℚ) ^ (n - k) ≠ 0 := by
      have hlt := pow_lt_one₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)
        (by omega : n - k ≠ 0)
      linarith
    have hpowSub : (1 / 2 : ℚ) ^ (n - k) =
        (1 / 2 : ℚ) ^ (n - (k + 1)) * (1 / 2 : ℚ) := by
      rw [hsub, pow_succ]
    have hnfactor' :
        1 + (1 / 2 : ℚ) ^ (n - (1 + k)) * (-1 / 2) ≠ 0 := by
      have heq : 1 + (1 / 2 : ℚ) ^ (n - (1 + k)) * (-1 / 2) =
          1 - (1 / 2 : ℚ) ^ (n - k) := by
        rw [show 1 + k = k + 1 by omega]
        rw [hpowSub]
        ring
      rw [heq]
      exact hnfactor
    have hden : 1 - (1 / 2 : ℚ) ^ (n - (k + 1) + 1) ≠ 0 := by
      rw [← hsub]
      exact hnfactor
    rw [show n + 1 - (k + 1) = n - k by omega]
    rw [halfQPochhammer_succ n, halfQPochhammer_succ k]
    rw [hsub, halfQPochhammer_succ]
    rw [hpow]
    field_simp [halfQPochhammer_ne_zero, hkfactor, hnfactor, hnfactor']
    rw [hpowSub]
    field_simp [hden]
    ring
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    rcases hnk.eq_or_lt with rfl | hnk
    · rw [halfQBinomial_self, halfQBinomial_self,
        halfQBinomial_eq_zero_of_lt (Nat.lt_succ_self n)]
      ring
    · rw [halfQBinomial_eq_zero_of_lt (by omega),
        halfQBinomial_eq_zero_of_lt hnk,
        halfQBinomial_eq_zero_of_lt (by omega)]
      ring

/-- The symmetric q-Pascal recurrence. -/
theorem halfQBinomial_succ_succ' (n k : ℕ) :
    halfQBinomial (n + 1) (k + 1) =
      halfQBinomial n (k + 1) +
        (1 / 2 : ℚ) ^ (n - k) * halfQBinomial n k := by
  by_cases hkn : k < n
  · have hk1n : k + 1 ≤ n := hkn
    have hk1n1 : k + 1 ≤ n + 1 := by omega
    calc
      halfQBinomial (n + 1) (k + 1) =
          halfQBinomial (n + 1) ((n + 1) - (k + 1)) :=
        (halfQBinomial_symm hk1n1).symm
      _ = halfQBinomial (n + 1) (n - k) := by
        rw [show (n + 1) - (k + 1) = n - k by omega]
      _ = halfQBinomial (n + 1) ((n - (k + 1)) + 1) := by
        rw [show n - k = (n - (k + 1)) + 1 by omega]
      _ = halfQBinomial n (n - (k + 1)) +
          (1 / 2 : ℚ) ^ ((n - (k + 1)) + 1) *
            halfQBinomial n ((n - (k + 1)) + 1) :=
        halfQBinomial_succ_succ n (n - (k + 1))
      _ = halfQBinomial n (k + 1) +
          (1 / 2 : ℚ) ^ (n - k) * halfQBinomial n k := by
        rw [show n - (k + 1) = n - (k + 1) by rfl]
        rw [halfQBinomial_symm hk1n]
        rw [show n - (k + 1) + 1 = n - k by omega]
        rw [halfQBinomial_symm hkn.le]
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    rcases hnk.eq_or_lt with rfl | hnk
    · rw [halfQBinomial_self,
        halfQBinomial_eq_zero_of_lt (Nat.lt_succ_self n),
        halfQBinomial_self]
      simp
    · rw [halfQBinomial_eq_zero_of_lt (by omega),
        halfQBinomial_eq_zero_of_lt (by omega),
        halfQBinomial_eq_zero_of_lt hnk]
      ring

private noncomputable def halfQBinomialSummand (n : ℕ) (z : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
    halfQBinomial n k * z ^ k

@[simp] private theorem halfQBinomialSummand_zero (n : ℕ) (z : ℚ) :
    halfQBinomialSummand n z 0 = 1 := by
  simp [halfQBinomialSummand]

private theorem halfQBinomialSummand_succ_succ
    (n k : ℕ) (hk : k ≤ n) (z : ℚ) :
    halfQBinomialSummand (n + 1) z (k + 1) =
      halfQBinomialSummand n z (k + 1) -
        z * (1 / 2 : ℚ) ^ n * halfQBinomialSummand n z k := by
  rw [halfQBinomialSummand, halfQBinomialSummand,
    halfQBinomialSummand, halfQBinomial_succ_succ']
  rw [choose_succ_two', pow_add, pow_succ, pow_succ]
  have hsum : k + (n - k) = n := Nat.add_sub_of_le hk
  have hknpow : (1 / 2 : ℚ) ^ k * (1 / 2 : ℚ) ^ (n - k) =
      (1 / 2 : ℚ) ^ n := by
    rw [← pow_add, hsum]
  ring_nf
  linear_combination
    -(halfQBinomial n k * z * z ^ k * (-1 : ℚ) ^ k *
      (1 / 2 : ℚ) ^ (k.choose 2)) * hknpow

private theorem halfQBinomialSummand_above (n : ℕ) (z : ℚ) :
    halfQBinomialSummand n z (n + 1) = 0 := by
  rw [halfQBinomialSummand, halfQBinomial_eq_zero_of_lt (Nat.lt_succ_self n)]
  ring

/-- The finite q-binomial theorem specialized to `q = 1/2`. -/
theorem halfQBinomial_theorem (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * z ^ k) =
      finiteQPochhammer z (1 / 2) n := by
  change (∑ k ∈ Finset.range (n + 1), halfQBinomialSummand n z k) = _
  induction n with
  | zero => simp [finiteQPochhammer]
  | succ n ih =>
      have hrec :
          (∑ k ∈ Finset.range (n + 1),
              halfQBinomialSummand (n + 1) z (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              (halfQBinomialSummand n z (k + 1) -
                z * (1 / 2 : ℚ) ^ n * halfQBinomialSummand n z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact halfQBinomialSummand_succ_succ n k
          (by simpa using Finset.mem_range.mp hk) z
      have htail :
          1 + (∑ k ∈ Finset.range (n + 1),
              halfQBinomialSummand n z (k + 1)) =
            ∑ k ∈ Finset.range (n + 1), halfQBinomialSummand n z k := by
        calc
          1 + (∑ k ∈ Finset.range (n + 1),
              halfQBinomialSummand n z (k + 1)) =
              ∑ k ∈ Finset.range (n + 2), halfQBinomialSummand n z k := by
            have hs := (Finset.sum_range_succ'
              (fun k => halfQBinomialSummand n z k) (n + 1)).symm
            rw [show n + 1 + 1 = n + 2 by omega] at hs
            simpa [add_comm] using hs
          _ = (∑ k ∈ Finset.range (n + 1), halfQBinomialSummand n z k) +
                halfQBinomialSummand n z (n + 1) := by
            exact Finset.sum_range_succ _ _
          _ = _ := by rw [halfQBinomialSummand_above, add_zero]
      rw [show n + 1 + 1 = n + 2 by omega, Finset.sum_range_succ']
      rw [halfQBinomialSummand_zero, hrec, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      calc
        (∑ x ∈ Finset.range (n + 1), halfQBinomialSummand n z (x + 1)) -
              z * (1 / 2 : ℚ) ^ n *
                (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) + 1 =
            (1 + ∑ x ∈ Finset.range (n + 1),
                halfQBinomialSummand n z (x + 1)) -
              z * (1 / 2 : ℚ) ^ n *
                (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) := by
          ring
        _ = (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) -
              z * (1 / 2 : ℚ) ^ n *
                (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) := by
          rw [htail]
        _ = (1 - z * (1 / 2 : ℚ) ^ n) *
              (∑ i ∈ Finset.range (n + 1), halfQBinomialSummand n z i) := by
          ring
        _ = finiteQPochhammer z (1 / 2) (n + 1) := by
          rw [ih, finiteQPochhammer_succ]
          ring

/-- Notation-faithful form of the finite q-binomial theorem at `q = 1/2`. -/
theorem qBinomial_half_theorem (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * z ^ k) =
      qPochhammer z (1 / 2) n := by
  simpa only [qBinomial_half_eq] using halfQBinomial_theorem n z

private theorem two_pow_mul_half_pow (n j : ℕ) (hj : j ≤ n) :
    (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ j = (2 : ℚ) ^ (n - j) := by
  rw [div_pow]
  simp only [one_pow]
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ j * (2 : ℚ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [hpow]
  field_simp

theorem qPochhammer_two_pow_eq_zero {n m : ℕ} (hm : m < n) :
    qPochhammer ((2 : ℚ) ^ m) (1 / 2) n = 0 := by
  unfold qPochhammer finiteQPochhammer
  apply Finset.prod_eq_zero (i := m)
  · exact Finset.mem_range.mpr hm
  · rw [two_pow_mul_half_pow m m (le_refl m)]
    norm_num

private theorem qPochhammer_two_pow_self_eq_mersenne (n : ℕ) :
    qPochhammer ((2 : ℚ) ^ n) (1 / 2) n =
      (-1 : ℚ) ^ n * halfMersenneProduct n := by
  have hterm (j : ℕ) (hj : j < n) :
      1 - (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ j =
        -((2 : ℚ) ^ (n - j) - 1) := by
    rw [two_pow_mul_half_pow n j hj.le]
    ring
  have hreflect :
      (∏ j ∈ Finset.range n, ((2 : ℚ) ^ (n - j) - 1)) =
        halfMersenneProduct n := by
    rw [halfMersenneProduct]
    rw [← Finset.prod_range_reflect
      (fun j => ((2 : ℚ) ^ (j + 1) - 1)) n]
    apply Finset.prod_congr rfl
    intro j hj
    congr 2
    have hjlt := Finset.mem_range.mp hj
    omega
  unfold qPochhammer finiteQPochhammer
  calc
    (∏ j ∈ Finset.range n,
        (1 - (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ j)) =
        ∏ j ∈ Finset.range n, -((2 : ℚ) ^ (n - j) - 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hterm j (Finset.mem_range.mp hj)
    _ = (-1 : ℚ) ^ n *
          ∏ j ∈ Finset.range n, ((2 : ℚ) ^ (n - j) - 1) := by
      calc
        (∏ j ∈ Finset.range n, -((2 : ℚ) ^ (n - j) - 1)) =
            ∏ j ∈ Finset.range n,
              ((-1 : ℚ) * ((2 : ℚ) ^ (n - j) - 1)) := by
          apply Finset.prod_congr rfl
          intro j _hj
          ring
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          simp
    _ = (-1 : ℚ) ^ n * halfMersenneProduct n := by rw [hreflect]

/-- The q-binomial sum vanishes at every dyadic node `2^m` with `m < n`. -/
theorem halfQBinomial_two_pow_sum_eq_zero {n m : ℕ} (hm : m < n) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ m) ^ k) = 0 := by
  rw [halfQBinomial_theorem]
  exact qPochhammer_two_pow_eq_zero hm

/-- Evaluation at the last dyadic node. -/
theorem halfQBinomial_two_pow_sum_eq_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        halfQBinomial n k * ((2 : ℚ) ^ n) ^ k) =
      (-1 : ℚ) ^ n * (2 : ℚ) ^ ((n + 1).choose 2) *
        halfQPochhammer n := by
  rw [halfQBinomial_theorem]
  calc
    finiteQPochhammer ((2 : ℚ) ^ n) (1 / 2) n =
        (-1 : ℚ) ^ n * halfMersenneProduct n :=
      qPochhammer_two_pow_self_eq_mersenne n
    _ = (-1 : ℚ) ^ n * (2 : ℚ) ^ ((n + 1).choose 2) *
        halfQPochhammer n := by
      rw [halfQPochhammer_eq_mersenne_div]
      field_simp

/-- Literal-notation vanishing form used by the Fabius formula. -/
theorem qBinomial_half_two_pow_sum_eq_zero {n m : ℕ} (hm : m < n) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ m) ^ k) = 0 := by
  simpa only [qBinomial_half_eq] using halfQBinomial_two_pow_sum_eq_zero hm

/-- Literal-notation endpoint evaluation used by the Fabius formula. -/
theorem qBinomial_half_two_pow_sum_eq_self (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) *
        qBinomial n k (1 / 2) * ((2 : ℚ) ^ n) ^ k) =
      (-1 : ℚ) ^ n * (2 : ℚ) ^ ((n + 1).choose 2) *
        qPochhammer (1 / 2) (1 / 2) n := by
  simpa only [qBinomial_half_eq, qPochhammer_half_eq] using
    halfQBinomial_two_pow_sum_eq_self n

end Fabius
