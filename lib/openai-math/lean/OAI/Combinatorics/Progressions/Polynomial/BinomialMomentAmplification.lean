import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pow_le_choose_block (R n : ℕ) :
    (R : ℝ) ^ n ≤ (((R + 1) * n).choose n : ℝ) := by
  have hchoose := Nat.pow_le_choose (α := ℝ) n ((R + 1) * n)
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hbase : R * n ≤ (R + 1) * n + 1 - n := by
    rw [Nat.add_mul, one_mul]
    omega
  have hbaseR : (R : ℝ) * n ≤ (((R + 1) * n + 1 - n : ℕ) : ℝ) := by exact_mod_cast hbase
  have hfirst : (R : ℝ) ^ n ≤
      ((((R + 1) * n + 1 - n : ℕ) : ℝ) ^ n) / (n.factorial : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < n.factorial)).mpr
    calc
      (R : ℝ) ^ n * (n.factorial : ℝ) ≤ (R : ℝ) ^ n * (n : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = ((R : ℝ) * n) ^ n := (mul_pow _ _ _).symm
      _ ≤ (((R + 1) * n + 1 - n : ℕ) : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hbaseR n
  exact hfirst.trans hchoose

theorem expect_one_add_pow_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (N : ℕ) :
    (𝔼 x ∈ s, (1 + f x) ^ N) =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (𝔼 x ∈ s, f x ^ k) := by
  have hpow (x : ι) : (1 + f x) ^ N =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * f x ^ k := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hpow]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_expect]

theorem expect_one_add_pow_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ s, f x ^ k) {n N : ℕ} (hn : n ≤ N) :
    (N.choose n : ℝ) * (𝔼 x ∈ s, f x ^ n) ≤ 𝔼 x ∈ s, (1 + f x) ^ N := by
  rw [expect_one_add_pow_eq]
  exact Finset.single_le_sum
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hmom k)) (Finset.mem_range.mpr (by omega))

theorem expect_one_add_pow_block_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ s, f x ^ k) (R n : ℕ) :
    (R : ℝ) ^ n * (𝔼 x ∈ s, f x ^ n) ≤ 𝔼 x ∈ s, (1 + f x) ^ ((R + 1) * n) := by
  apply (mul_le_mul_of_nonneg_right (pow_le_choose_block R n) (hmom n)).trans
  apply expect_one_add_pow_lower s f hmom
  nlinarith

end Erdos3

end

end OAI
