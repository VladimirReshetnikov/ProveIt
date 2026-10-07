/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productCutoff_transfer_exp (j n : ℕ) {q : ℝ} (_hq : 0 ≤ q) :
    Real.exp (-((q + 1) * ((2 ^ (j + 2) * n + 1 : ℕ) : ℝ) + ((n + 3) * n : ℕ))) ≤
      (Real.exp (-q) / 2) ^ (2 ^ (j + 2) * n + 1) /
        (4 * (n + 1 : ℝ)) ^ n := by
  have hbase : Real.exp (-(q + 1)) ≤ Real.exp (-q) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-(q + 1)) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hden : (4 * (n + 1 : ℝ)) ^ n ≤ Real.exp (((n + 3) * n : ℕ) : ℝ) := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    have hn : (n + 1 : ℝ) ≤ Real.exp n := Real.add_one_le_exp _
    calc
      _ ≤ (Real.exp 3 * Real.exp n) ^ n :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul h4 hn (by positivity) (Real.exp_nonneg _)) n
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg (-(q + 1))) hbase (2 ^ (j + 2) * n + 1)
  calc
    _ = Real.exp (-(q + 1)) ^ (2 ^ (j + 2) * n + 1) /
        Real.exp (((n + 3) * n : ℕ) : ℝ) := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := div_le_div₀ (by positivity) hpow (by positivity) hden

theorem product_box_volume_ratio_exp {I : Type*} [Fintype I]
    (N H : I → ℕ) (hN : ∀ i, 0 < N i) {d : ℕ} (hd : 0 < d)
    {p : ℝ} (_hp : 0 ≤ p) (hdp : (d : ℝ) ≤ Real.exp p)
    (hH : ∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) :
    Real.exp (-((2 * p + 2) * Fintype.card I)) ≤
      ((∏ i, H i : ℕ) : ℝ) / ((∏ i, 4 * (d * N i) : ℕ) : ℝ) := by
  classical
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      4 = (2 : ℝ) * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul h2 h2 (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have haxis (i) : Real.exp (-(2 * p + 2)) ≤ (H i : ℝ) / (4 * (d * N i)) := by
    have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (d * N i))).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 2)) * (Real.exp 2 * (Real.exp p * N i)) := by
        gcongr
      _ = Real.exp (-p) * N i := by
        rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := hH i
  calc
    _ = ∏ _i : I, Real.exp (-(2 * p + 2)) := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ∏ i, (H i : ℝ) / (4 * (d * N i)) :=
      Finset.prod_le_prod₀ (fun _ _ => Real.exp_nonneg _) (fun coordinate _ => haxis coordinate)
    _ = _ := by simp only [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat]

end Erdos3

end

end OAI
