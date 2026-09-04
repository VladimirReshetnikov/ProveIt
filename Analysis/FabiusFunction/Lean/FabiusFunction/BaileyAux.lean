import FabiusFunction.FiniteQBinomialCore

/-!
# The auxiliary finite identity of the limiting Bailey lemma

`∑_{k=0}^{N} z^k q^{k(k-1)} [N,k]_q (zq^k;q)_{N-k} = 1` in every commutative ring
(`bailey_aux_sum`).  Writing `S_N(z)` for the left side, the second `q`-Pascal rule
`[N+1,k+1] = [N,k+1] + q^{N-k} [N,k]` and the splitting of the last factor of
`(zq^{k};q)_{N+1-k}` give the recurrence

  `S_{N+1}(z) = (1 - zq^N) S_N(z) + zq^N S_N(qz)`  (`baileyAuxSum_succ`),

and `S_0 = 1`, so `S_N = 1` by induction.

## Main declarations

* `baileyAuxSum`, `baileyAuxSum_succ`, `baileyAuxSum_eq_one`, `bailey_aux_sum`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {R : Type*} [CommRing R]

/-- The Bailey auxiliary sum `S_N(z) = ∑_{k ≤ N} z^k q^{k(k-1)} [N,k]_q (zq^k;q)_{N-k}`. -/
def baileyAuxSum (q z : R) (N : ℕ) : R :=
  ∑ k ∈ range (N + 1),
    z ^ k * q ^ (k * (k - 1)) * gaussianBinomial q N k *
      finiteQPochhammerIn (z * q ^ k) q (N - k)

/-- The zeroth Bailey auxiliary sum is `1`. -/
theorem baileyAuxSum_zero (q z : R) : baileyAuxSum q z 0 = 1 := by
  simp [baileyAuxSum, finiteQPochhammerIn, gaussianBinomial]

/-- The recurrence `S_{N+1}(z) = (1 - zq^N) S_N(z) + zq^N S_N(qz)`. -/
theorem baileyAuxSum_succ (q z : R) (N : ℕ) :
    baileyAuxSum q z (N + 1) =
      (1 - z * q ^ N) * baileyAuxSum q z N + z * q ^ N * baileyAuxSum q (z * q) N := by
  -- `S_N(z)`: the terms `k = j+1` and the term `k = 0`
  have hS : baileyAuxSum q z N =
      (∑ j ∈ range N, z ^ (j + 1) * q ^ ((j + 1) * j) * gaussianBinomial q N (j + 1) *
        finiteQPochhammerIn (z * q ^ (j + 1)) q (N - (j + 1))) +
        finiteQPochhammerIn z q N := by
    unfold baileyAuxSum
    rw [sum_range_succ']
    refine congrArg₂ (· + ·) (sum_congr rfl fun j _ => ?_) ?_
    · rw [Nat.add_sub_cancel]
    · simp [gaussianBinomial_zero_right]
  have hB : baileyAuxSum q (z * q) N =
      ∑ j ∈ range (N + 1), (z * q) ^ j * q ^ (j * (j - 1)) * gaussianBinomial q N j *
        finiteQPochhammerIn (z * q * q ^ j) q (N - j) := rfl
  have hzero : gaussianBinomial q N (N + 1) = 0 :=
    gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self N)
  -- the terms `k = j+1` of `S_{N+1}(z)`, split by the `q`-Pascal rule
  have hterm : ∀ j ∈ range (N + 1),
      z ^ (j + 1) * q ^ ((j + 1) * (j + 1 - 1)) * gaussianBinomial q (N + 1) (j + 1) *
        finiteQPochhammerIn (z * q ^ (j + 1)) q (N + 1 - (j + 1)) =
      z ^ (j + 1) * q ^ ((j + 1) * j) * gaussianBinomial q N (j + 1) *
          finiteQPochhammerIn (z * q ^ (j + 1)) q (N - j) +
        z * q ^ N * ((z * q) ^ j * q ^ (j * (j - 1)) * gaussianBinomial q N j *
          finiteQPochhammerIn (z * q * q ^ j) q (N - j)) := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [Nat.add_sub_cancel, Nat.add_sub_add_right, gaussianBinomial_succ_succ]
    have hexp : z ^ (j + 1) * q ^ ((j + 1) * j) * q ^ (N - j) =
        z * q ^ N * ((z * q) ^ j * q ^ (j * (j - 1))) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjN
      rw [Nat.add_sub_cancel_left]
      cases j with
      | zero => ring
      | succ i =>
          rw [Nat.add_sub_cancel]
          ring
    rw [show z * q * q ^ j = z * q ^ (j + 1) by ring]
    linear_combination
      (gaussianBinomial q N j * finiteQPochhammerIn (z * q ^ (j + 1)) q (N - j)) * hexp
  -- the terms `j < N` of the first part carry the factor `1 - zq^N`
  have hA : ∀ j ∈ range N,
      z ^ (j + 1) * q ^ ((j + 1) * j) * gaussianBinomial q N (j + 1) *
        finiteQPochhammerIn (z * q ^ (j + 1)) q (N - j) =
      (z ^ (j + 1) * q ^ ((j + 1) * j) * gaussianBinomial q N (j + 1) *
        finiteQPochhammerIn (z * q ^ (j + 1)) q (N - (j + 1))) * (1 - z * q ^ N) := by
    intro j hj
    have hjN : j + 1 ≤ N := mem_range.mp hj
    have h1 : N - j = N - (j + 1) + 1 := by omega
    rw [h1, finiteQPochhammerIn_succ]
    have h2 : z * q ^ (j + 1) * q ^ (N - (j + 1)) = z * q ^ N := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hjN]
    rw [h2]
    ring
  conv_lhs => unfold baileyAuxSum
  rw [sum_range_succ', sum_congr rfl hterm, sum_add_distrib,
    ← mul_sum (range (N + 1)) _ (z * q ^ N), sum_range_succ, hzero]
  simp only [mul_zero, zero_mul, add_zero]
  rw [sum_congr rfl hA, ← sum_mul]
  simp only [pow_zero, one_mul, mul_one, gaussianBinomial_zero_right, Nat.sub_zero]
  rw [hS, hB, finiteQPochhammerIn_succ]
  ring

/-- `S_N(z) = 1` for every `N` and `z`. -/
theorem baileyAuxSum_eq_one (q z : R) (N : ℕ) : baileyAuxSum q z N = 1 := by
  induction N generalizing z with
  | zero => exact baileyAuxSum_zero q z
  | succ N ih =>
      rw [baileyAuxSum_succ, ih z, ih (z * q)]
      ring

/-- **The auxiliary finite identity** (lem:bailey-aux):
`∑_{k=0}^{N} z^k q^{k(k-1)} [N,k]_q (zq^k;q)_{N-k} = 1`. -/
theorem bailey_aux_sum (q z : R) (N : ℕ) :
    ∑ k ∈ range (N + 1),
      z ^ k * q ^ (k * (k - 1)) * gaussianBinomial q N k *
        finiteQPochhammerIn (z * q ^ k) q (N - k) = 1 :=
  baileyAuxSum_eq_one q z N

end Fabius
